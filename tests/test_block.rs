extern crate bytes;
extern crate bytes_more;

use bytes::BufMut;
use bytes_more::BlockBuf;

#[test]
pub fn test_block_drop() {
    let mut buf = BlockBuf::new(2, 4);

    assert_eq!(buf.remaining_mut(), 8);

    buf.copy_from_slice(b"12345");
    buf.copy_from_slice(b"678");
    assert_eq!(buf.remaining_mut(), 0);
    assert_eq!(buf.len(), 8);

    buf.drop(1);
    assert_eq!(buf.len(), 7);
    assert_eq!(buf.is_compact(), false);

    buf.drop(4);
    assert_eq!(buf.len(), 3);
    assert_eq!(buf.is_compact(), true);
}
