use bytes::{Buf, BufMut, IntoBuf, Bytes, Source, ByteBuf};
use std::{cmp, fmt, ops};
use std::io::Cursor;
use std::sync::Arc;

// The implementation is mostly a port of the implementation found in the Java
// protobuf lib.

const CONCAT_BY_COPY_LEN: usize = 128;
const MAX_DEPTH: usize = 47;

// Used to decide when to rebalance the tree.
static MIN_LENGTH_BY_DEPTH: [usize; MAX_DEPTH] = [
              1,              2,              3,              5,              8,
             13,             21,             34,             55,             89,
            144,            233,            377,            610,            987,
          1_597,          2_584,          4_181,          6_765,         10_946,
         17_711,         28_657,         46_368,         75_025,        121_393,
        196_418,        317_811,        514_229,        832_040,      1_346_269,
      2_178_309,      3_524_578,      5_702_887,      9_227_465,     14_930_352,
     24_157_817,     39_088_169,     63_245_986,    102_334_155,    165_580_141,
    267_914_296,    433_494_437,    701_408_733,  1_134_903_170,  1_836_311_903,
  2_971_215_073,  4_294_967_295];

/// An immutable sequence of bytes formed by concatenation of other `ByteStr`
/// values, without copying the data in the pieces. The concatenation is
/// represented as a tree whose leaf nodes are each a `Bytes` value.
///
/// Most of the operation here is inspired by the now-famous paper [Ropes: an
/// Alternative to Strings. hans-j. boehm, russ atkinson and michael
/// plass](http://www.cs.rit.edu/usr/local/pub/jeh/courses/QUARTERS/FP/Labs/CedarRope/rope-paper.pdf).
///
/// Fundamentally the Rope algorithm represents the collection of pieces as a
/// binary tree. BAP95 uses a Fibonacci bound relating depth to a minimum
/// sequence length, sequences that are too short relative to their depth cause
/// a tree rebalance.  More precisely, a tree of depth d is "balanced" in the
/// terminology of BAP95 if its length is at least F(d+2), where F(n) is the
/// n-the Fibonacci number. Thus for depths 0, 1, 2, 3, 4, 5,... we have
/// minimum lengths 1, 2, 3, 5, 8, 13,...
#[derive(Clone)]
pub struct Rope {
    left: Node,
    right: Node,
    depth: u16,
    len: usize,
}

pub struct RopeBuf<'a> {
    // Number of bytes left to iterate
    rem: usize,

    // Iterates all the leaf nodes in order
    nodes: NodeIter<'a>,

    // Current leaf node buffer
    leaf_buf: Option<Cursor<&'a [u8]>>,
}

#[derive(Clone)]
enum Node {
    Empty,
    Leaf(Bytes),
    Branch(Arc<Rope>),
}

// TODO: store stack inline if possible
struct NodeIter<'a> {
    stack: Vec<&'a Rope>,
    next: Option<&'a Node>,
}

/// Balance operation state
struct Balance {
    stack: Vec<Partial>,
}

/// Temporarily detached branch
enum Partial {
    Rope(Rope),
    Node(Node),
}

impl Rope {
    pub fn empty() -> Rope {
        Rope::new(Node::Empty, Node::Empty)
    }

    pub fn from_slice<T: AsRef<[u8]>>(slice: T) -> Rope {
        let bytes = Bytes::from_slice(slice);
        bytes.into()
    }

    fn new(left: Node, right: Node) -> Rope {
        debug_assert!(!left.is_empty() || right.is_empty());

        // If left is 0 then right must be zero
        let len = left.len() + right.len();
        let depth = cmp::max(left.depth(), right.depth()) + 1;

        Rope {
            left: left,
            right: right,
            depth: depth,
            len: len,
        }
    }

    pub fn buf(&self) -> RopeBuf {
        let mut nodes = NodeIter::new(self);

        // Get the next leaf node buffer
        let leaf_buf = nodes.next()
            .map(|node| node.leaf_buf());

        RopeBuf {
            rem: self.len(),
            nodes: nodes,
            leaf_buf: leaf_buf,
        }
    }

    /// Concat two `Bytes` together.
    pub fn concat<T: Into<Rope>>(&self, other: T) -> Rope {
        let other: Rope = other.into();

        if other.is_empty() {
            return self.clone();
        }

        if self.is_empty() {
            return other;
        }

        let len = self.len() + other.len();

        if len < CONCAT_BY_COPY_LEN {
            return concat_bytes(self, &other, len).into();
        }

        let len_right_concat = self.right.len() + other.len();

        if len_right_concat < CONCAT_BY_COPY_LEN {
            // Optimization from BAP95: As an optimization of the case
            // where the ByteString is constructed by repeated concatenate,
            // recognize the case where a short string is concatenated to a
            // left-hand node whose right-hand branch is short.  In the
            // paper this applies to leaves, but we just look at the length
            // here. This has the advantage of shedding references to
            // unneeded data when substrings have been taken.
            //
            // When we recognize this case, we do a copy of the data and
            // create a new parent node so that the depth of the result is
            // the same as the given left tree.
            let new_right = concat_bytes(&self.right, &other, len_right_concat);

            return Rope::new(self.left.clone(), Node::Leaf(new_right));
        }

        if self.left.depth() > self.right.depth() && self.depth > other.depth() {
            // Typically for concatenate-built strings the left-side is
            // deeper than the right.  This is our final attempt to
            // concatenate without increasing the tree depth.  We'll redo
            // the the node on the RHS.  This is yet another optimization
            // for building the string by repeatedly concatenating on the
            // right.
            let new_right = Rope::new(self.right.clone(), other.into());

            return Rope::new(self.left.clone(), new_right.into());
        }

        // Fine, we'll add a node and increase the tree depth -- unless we
        // rebalance ;^)
        let depth = cmp::max(self.depth(), other.depth()) + 1;

        if len >= MIN_LENGTH_BY_DEPTH[depth as usize] {
            // No need to rebalance
            return Rope::new(self.clone().into(), other.into());
        }

        Balance::new().balance(self.clone(), other).into()
    }

    fn depth(&self) -> u16 {
        self.depth
    }

    pub fn len(&self) -> usize {
        self.len as usize
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a new ByteStr value containing the byte range between `begin`
    /// (inclusive) and `end` (exclusive)
    pub fn slice(&self, begin: usize, end: usize) -> Rope {
        // Assert args
        assert!(begin <= end && end <= self.len(), "invalid range");

        let len = end - begin;

        // Empty slice
        if len == 0 {
            return Rope::empty();
        }

        // Full rope
        if len == self.len() {
            return self.clone();
        }

        // == Proper substring ==

        let left_len = self.left.len();

        if end <= left_len {
            // Slice on the left
            return self.left.slice(begin, end);
        }

        if begin >= left_len {
            // Slice on the right
            return self.right.slice(begin - left_len, end - left_len);
        }

        // Split slice
        let left_slice = self.left.slice(begin, self.left.len());
        let right_slice = self.right.slice(0, end - left_len);

        Rope::new(left_slice.into(), right_slice.into())
    }

    /// Returns a new Rope value containing the byte range starting from
    /// `begin` (inclusive) to the end of the byte str.
    ///
    /// Equivalent to `rope.slice(begin, bytes.len())`
    pub fn slice_from(&self, begin: usize) -> Rope {
        self.slice(begin, self.len())
    }

    /// Returns a new Rope value containing the byte range from the start up
    /// to `end` (exclusive).
    ///
    /// Equivalent to `rope.slice(0, end)`
    pub fn slice_to(&self, end: usize) -> Rope {
        self.slice(0, end)
    }
}

impl Node {
    fn len(&self) -> usize {
        match *self {
            Node::Empty => 0,
            Node::Leaf(ref b) => b.len(),
            Node::Branch(ref b) => b.len,
        }
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn depth(&self) -> u16 {
        match *self {
            Node::Branch(ref r) => r.depth,
            _ => 0,
        }
    }

    fn slice(&self, begin: usize, end: usize) -> Rope {
        match *self {
            Node::Leaf(ref v) => Rope::new(Node::Leaf(v.slice(begin, end)), Node::Empty),
            Node::Branch(ref v) => v.slice(begin, end),
            Node::Empty => unreachable!(),
        }
    }

    fn leaf_buf(&self) -> Cursor<&[u8]> {
        match *self {
            Node::Leaf(ref v) => Cursor::new(v.as_slice()),
            _ => unreachable!(),
        }
    }

    fn as_rope(&self) -> Option<&Rope> {
        match *self {
            Node::Branch(ref v) => Some(&**v),
            _ => None,
        }
    }
}

impl<'a> Source for &'a Rope {
    fn source<B: BufMut>(self, buf: &mut B) {
        Source::source(&mut self.buf(), buf);
    }
}

impl<'a> From<&'a Rope> for Rope {
    fn from(src: &'a Rope) -> Rope {
        src.clone()
    }
}

impl From<Bytes> for Rope {
    fn from(src: Bytes) -> Rope {
        Rope::new(Node::Leaf(src), Node::Empty)
    }
}

impl<'a> From<&'a [u8]> for Rope {
    fn from(src: &'a [u8]) -> Rope {
        Rope::from_slice(src)
    }
}

impl From<Vec<u8>> for Rope {
    fn from(src: Vec<u8>) -> Rope {
        let bytes: Bytes = src.into();
        bytes.into()
    }
}

impl<'a> Source for &'a Node {
    fn source<B: BufMut>(self, buf: &mut B) {
        match *self {
            Node::Leaf(ref b) => b.source(buf),
            Node::Branch(ref b) => b.source(buf),
            Node::Empty => unreachable!(),
        }
    }
}

impl From<Rope> for Node {
    fn from(src: Rope) -> Node {
        if src.right.is_empty() {
            src.left
        } else {
            assert!(!src.left.is_empty());
            Node::Branch(Arc::new(src))
        }
    }
}

impl ops::Index<usize> for Rope {
    type Output = u8;

    fn index(&self, index: usize) -> &u8 {
        assert!(index < self.len());

        let left_len = self.left.len();

        if index < left_len {
            self.left.index(index)
        } else {
            self.right.index(index - left_len)
        }
    }
}

impl ops::Index<usize> for Node {
    type Output = u8;

    fn index(&self, index: usize) -> &u8 {
        match *self {
            Node::Leaf(ref v) => v.index(index),
            Node::Branch(ref v) => v.index(index),
            Node::Empty => unreachable!(),
        }
    }
}

impl<'a> IntoBuf for &'a Rope {
    type Buf = RopeBuf<'a>;

    fn into_buf(self) -> Self::Buf {
        self.buf()
    }
}

impl<T> cmp::PartialEq<T> for Rope
    where for<'a> &'a T: IntoBuf
{
    fn eq(&self, other: &T) -> bool {
        let mut buf1 = self.buf();
        let mut buf2 = other.into_buf();

        if buf1.remaining() != buf2.remaining() {
            return false;
        }

        while buf1.has_remaining() {
            let len;
            {
                let b1 = buf1.bytes();
                let b2 = buf2.bytes();

                len = cmp::min(b1.len(), b2.len());

                if b1[..len] != b2[..len] {
                    return false;
                }
            }

            buf1.advance(len);
            buf2.advance(len);
        }

        true
    }
}

impl cmp::Eq for Rope {}

/*
 *
 * ===== Helper Fns =====
 *
 */

fn concat_bytes<S1, S2>(left: S1, right: S2, len: usize) -> Bytes
    where S1: Source, S2: Source,
{
    let mut buf = ByteBuf::with_capacity(len);

    buf.copy_from(left);
    buf.copy_from(right);

    return buf.into();
}

fn depth_for_len(len: usize) -> u16 {
    match MIN_LENGTH_BY_DEPTH.binary_search(&len) {
        Ok(idx) => idx as u16,
        Err(idx) => {
            // It wasn't an exact match, so convert to the index of the
            // containing fragment, which is one less even than the insertion
            // point.
            idx as u16 - 1
        }
    }
}

impl<'a> NodeIter<'a> {
    fn new(root: &'a Rope) -> NodeIter<'a> {
        let mut iter = NodeIter {
            // TODO: Consider allocating with capacity for depth
            stack: vec![],
            next: None,
        };

        iter.next = iter.get_leaf_by_left(root);
        iter
    }

    fn get_leaf_by_left(&mut self, mut root: &'a Rope) -> Option<&'a Node> {
        loop {
            self.stack.push(root);
            let left = &root.left;

            if left.is_empty() {
                return None;
            }

            if let Some(rope) = left.as_rope() {
                root = rope;
                continue;
            }

            return Some(left);
        }
    }

    fn next_non_empty_leaf(&mut self) -> Option<&'a Node>{
        loop {
            if let Some(rope) = self.stack.pop() {
                if let Some(rope) = rope.right.as_rope() {
                    let res = self.get_leaf_by_left(&rope);

                    if res.is_none() {
                        continue;
                    }

                    return res;
                }

                if rope.right.is_empty() {
                    continue;
                }

                return Some(&rope.right);
            }

            return None;
        }
    }
}

impl<'a> Iterator for NodeIter<'a> {
    type Item = &'a Node;

    fn next(&mut self) -> Option<&'a Node> {
        let ret = self.next.take();

        if ret.is_some() {
            self.next = self.next_non_empty_leaf();
        }

        ret
    }
}

impl<'a> Buf for RopeBuf<'a> {
    fn remaining(&self) -> usize {
        self.rem
    }

    fn bytes(&self) -> &[u8] {
        self.leaf_buf.as_ref()
            .map(|b| b.bytes())
            .unwrap_or(&[])
    }

    fn advance(&mut self, mut cnt: usize) {
        cnt = cmp::min(cnt, self.rem);

        // Advance the internal cursor
        self.rem -= cnt;

        // Advance the leaf buffer
        while cnt > 0 {
            {
                let curr = self.leaf_buf.as_mut()
                    .expect("expected a value");

                if curr.remaining() > cnt {
                    curr.advance(cnt);
                    break;
                }

                cnt -= curr.remaining();
            }

            self.leaf_buf = self.nodes.next()
                .map(|node| node.leaf_buf());
        }
    }
}

/*
 *
 * ===== Balance =====
 *
 */

impl Balance {
    fn new() -> Balance {
        Balance { stack: vec![] }
    }

    fn balance(&mut self, left: Rope, right: Rope) -> Rope {
        self.do_balance(Partial::Rope(left));
        self.do_balance(Partial::Rope(right));

        let mut partial = self.stack.pop()
            .expect("expected a value");

        while !partial.is_empty() {
            let new_left = self.stack.pop()
                .expect("expected a value");

            partial = Partial::Rope(Rope::new(new_left.into(), partial.into()));
        }

        partial.unwrap_rope()
    }

    fn do_balance(&mut self, root: Partial) {
      // BAP95: Insert balanced subtrees whole. This means the result might not
      // be balanced, leading to repeated rebalancings on concatenate. However,
      // these rebalancings are shallow due to ignoring balanced subtrees, and
      // relatively few calls to insert() result.
      if root.is_balanced() {
          self.insert(root);
      } else {
          let rope = root.unwrap_rope();

          self.do_balance(Partial::Node(rope.left));
          self.do_balance(Partial::Node(rope.right));
      }
    }

    // Push a string on the balance stack (BAP95).  BAP95 uses an array and
    // calls the elements in the array 'bins'.  We instead use a stack, so the
    // 'bins' of lengths are represented by differences between the elements of
    // minLengthByDepth.
    //
    // If the length bin for our string, and all shorter length bins, are
    // empty, we just push it on the stack.  Otherwise, we need to start
    // concatenating, putting the given string in the "middle" and continuing
    // until we land in an empty length bin that matches the length of our
    // concatenation.
    fn insert(&mut self, bytes: Partial) {
        let depth_bin = depth_for_len(bytes.len());
        let bin_end = MIN_LENGTH_BY_DEPTH[depth_bin as usize + 1];

        // BAP95: Concatenate all trees occupying bins representing the length
        // of our new piece or of shorter pieces, to the extent that is
        // possible.  The goal is to clear the bin which our piece belongs in,
        // but that may not be entirely possible if there aren't enough longer
        // bins occupied.
        if let Some(len) = self.peek().map(|r| r.len()) {
            if len >= bin_end {
                self.stack.push(bytes);
                return;
            }
        }

        let bin_start = MIN_LENGTH_BY_DEPTH[depth_bin as usize];

        // Concatenate the subtrees of shorter length
        let mut new_tree = self.stack.pop()
            .expect("expected a value");

        while let Some(len) = self.peek().map(|r| r.len()) {
            // If the head is big enough, break the loop
            if len >= bin_start { break; }

            let left = self.stack.pop()
                .expect("expected a value");

            new_tree = Partial::Rope(Rope::new(left.into(), new_tree.into()));
        }

        // Concatenate the given string
        new_tree = Partial::Rope(Rope::new(new_tree.into(), bytes.into()));

        // Continue concatenating until we land in an empty bin
        while let Some(len) = self.peek().map(|r| r.len()) {
            let depth_bin = depth_for_len(new_tree.len());
            let bin_end = MIN_LENGTH_BY_DEPTH[depth_bin as usize + 1];

            if len < bin_end {
                let left = self.stack.pop()
                    .expect("expected a value");

                new_tree = Partial::Rope(Rope::new(left.into(), new_tree.into()));
            } else {
                break;
            }
        }

        self.stack.push(new_tree);
    }

    fn peek(&self) -> Option<&Partial> {
        self.stack.last()
    }
}

impl Partial {
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn len(&self) -> usize {
        match *self {
            Partial::Rope(ref v) => v.len(),
            Partial::Node(ref v) => v.len(),
        }
    }

    fn depth(&self) -> u16 {
        match *self {
            Partial::Rope(ref v) => v.depth(),
            Partial::Node(ref v) => v.depth(),
        }
    }

    fn is_balanced(&self) -> bool {
        self.len() >= MIN_LENGTH_BY_DEPTH[self.depth() as usize]
    }

    fn unwrap_rope(self) -> Rope {
        match self {
            Partial::Rope(v) => v,
            Partial::Node(Node::Branch(arc)) => {
                match Arc::try_unwrap(arc) {
                    Ok(v) => v,
                    Err(v) => (*v).clone(),
                }
            }
            _ => panic!("unexpected state calling `Partial::unwrap_rope()`"),
        }
    }
}

impl From<Partial> for Node {
    fn from(src: Partial) -> Node {
        match src {
            Partial::Node(v) => v,
            Partial::Rope(v) => Node::from(v),
        }
    }
}

impl fmt::Debug for Rope {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let mut buf = self.buf();

        try!(write!(fmt, "Rope[len={}; ", self.len()));

        let mut rem = 128;

        while buf.has_remaining() {
            let byte = buf.get_u8();

            if rem > 0 {
                if is_ascii(byte) {
                    try!(write!(fmt, "{}", byte as char));
                } else {
                    try!(write!(fmt, "\\x{:02X}", byte));
                }

                rem -= 1;
            } else {
                try!(write!(fmt, " ... "));
                break;
            }
        }

        try!(write!(fmt, "]"));

        Ok(())
    }
}

fn is_ascii(byte: u8) -> bool {
    match byte {
        10 | 13 | 32...126 => true,
        _ => false,
    }
}
