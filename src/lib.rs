// #![deny(warnings)]

extern crate bytes;

/*
mod buf;
mod bytes;
*/

mod rope;

pub use rope::{Rope, RopeBuf};

// pub use buf::block::{BlockBuf, BlockBufCursor};

/*
pub mod buf {
    //! Traits, helpers, and type definitions for working with buffers.

    pub use imp::buf::{
        Source,
        Sink,
        Reader,
        ReadExt,
        Writer,
        WriteExt,
        Fmt,
    };

    pub use imp::buf::byte::ByteBuf;
    pub use imp::buf::slice::SliceBuf;
    // pub use imp::buf::append::AppendBuf;
    // pub use imp::buf::block::{BlockBuf, BlockBufCursor};
    pub use imp::buf::bound::{BoundBuf};
    // pub use imp::buf::ring::RingBuf;
    pub use imp::buf::take::Take;
    // pub use imp::bytes::BytesBuf;
}
*/
