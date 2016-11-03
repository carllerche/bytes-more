extern crate bytes;
extern crate bytes_more;

use bytes::{Buf, BufMut};
use bytes_more::RingBuf;

#[test]
pub fn test_ring_buf_is_send() {
    fn is_send<T: Send>() {}
    is_send::<RingBuf>();
}

#[test]
pub fn test_initial_buf_empty() {
    let mut buf = RingBuf::with_capacity(16);
    assert_eq!(BufMut::remaining_mut(&buf), 16);
    assert_eq!(Buf::remaining(&buf), 0);

    buf.copy_from(&[1, 2, 3][..]);

    buf.copy_from(&[][..]);
    assert_eq!(BufMut::remaining_mut(&buf), 13);
    assert_eq!(Buf::remaining(&buf), 3);
    assert_eq!(buf.bytes(), [1, 2, 3]);

    let mut out = [0u8; 3];

    let pos = buf.position();
    buf.copy_to(&mut out[..]);
    assert_eq!(out, [1, 2, 3]);
    buf.set_position(pos);
    buf.copy_to(&mut out[..]);
    assert_eq!(out, [1, 2, 3]);

    assert_eq!(BufMut::remaining_mut(&buf), 16);
    assert_eq!(Buf::remaining(&buf), 0);
}

#[test]
fn test_wrapping_write() {
    let mut buf = RingBuf::with_capacity(16);
    let mut out = [0;10];

    buf.copy_from(&[42;12][..]);
    buf.copy_to(&mut out[..]);

    buf.copy_from(&[23;8][..]);

    let pos = buf.position();
    buf.copy_to(&mut out[..]);
    assert_eq!(out, [42, 42, 23, 23, 23, 23, 23, 23, 23, 23]);
    buf.set_position(pos);
    buf.copy_to(&mut out[..]);
    assert_eq!(out, [42, 42, 23, 23, 23, 23, 23, 23, 23, 23]);
}

#[test]
fn test_io_write_and_read() {
    let mut buf = RingBuf::with_capacity(16);
    let mut out = [0u8;8];

    buf.copy_from(&[1;8][..]);

    buf.copy_to(&mut out[..]);
    assert_eq!(out, [1;8]);

    buf.copy_from(&[2;8][..]);

    buf.copy_to(&mut out[..]);
    assert_eq!(out, [2;8]);
}

#[test]
#[should_panic]
fn test_wrap_reset() {
    let mut buf = RingBuf::with_capacity(8);
    buf.copy_from(&[1, 2, 3, 4, 5, 6, 7][..]);
    let pos = buf.position();
    buf.copy_to(&mut [0; 4][..]);
    buf.copy_from(&[1, 2, 3, 4][..]);
    buf.set_position(pos);
}

#[test]
// Test that writes across a mark/reset are preserved.
fn test_mark_write() {
    let mut buf = RingBuf::with_capacity(8);
    buf.copy_from(&[1, 2, 3, 4, 5, 6, 7][..]);
    let pos = buf.position();
    buf.copy_from(&[8][..]);
    buf.set_position(pos);

    let mut buf2 = [0; 8];
    buf.copy_to(&mut buf2[..]);
    assert_eq!(buf2, [1, 2, 3, 4, 5, 6, 7, 8]);
}

#[test]
// Test that "RingBuf::reset" does not reset the length of a
// full buffer to zero.
fn test_reset_full() {
    let mut buf = RingBuf::with_capacity(8);
    buf.copy_from(&[1, 2, 3, 4, 5, 6, 7, 8][..]);
    assert_eq!(BufMut::remaining_mut(&buf), 0);
    let pos = buf.position();
    buf.set_position(pos);
    assert_eq!(BufMut::remaining_mut(&buf), 0);
}


#[test]
// Test that "RingBuf::clear" does the full reset
fn test_clear() {
    let mut buf = RingBuf::with_capacity(8);
    buf.copy_from(&[0; 8][..]);
    assert_eq!(BufMut::remaining_mut(&buf), 0);
    assert_eq!(Buf::remaining(&buf), 8);
    buf.clear();
    assert_eq!(BufMut::remaining_mut(&buf), 8);
    assert_eq!(Buf::remaining(&buf), 0);
}
