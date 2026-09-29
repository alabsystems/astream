#![forbid(unsafe_code)]
//! # astream-wire
//!
//! The pure vocabulary of the astream message bus: the wire [`Frame`] codec,
//! the [`Subject`] / [`Filter`] address grammar, the single canonical
//! [`assign_partition`] function, and [`Offset`] arithmetic.
//!
//! Design rules:
//!
//! * **No panics on hostile input.** Decoders return `Result`/`Option`; the
//!   encode path returns `Result` rather than panicking on an oversized payload.
//! * **One partitioner.** There is exactly one [`assign_partition`], so every
//!   router derives the same partition for the same message.
//! * **Names match behavior.** [`crate::hash::crc32_ieee`] is named for the
//!   polynomial it computes (IEEE, not Castagnoli/CRC-32C).
//! * **Zero dependencies.** This crate pulls in nothing, so it is trivially
//!   auditable and reproducible.

pub mod frame;
pub mod hash;
pub mod offset;
pub mod partition;
pub mod subject;

pub use frame::{Decoded, Frame, FrameError, HEADER_SIZE, MAX_PAYLOAD_LEN};
pub use hash::{crc32_ieee, fnv1a_64};
pub use offset::Offset;
pub use partition::{assign_partition, time_bucket, PartitionKey, TIME_BUCKET_MS};
pub use subject::{Filter, FilterError, Subject, SubjectError};
