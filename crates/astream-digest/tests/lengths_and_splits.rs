//! Every message length from 0 to 1024 bytes — sixteen blocks, every padding
//! position many times over — fed whole and under random `update` splits
//! (zero-length updates included).
//!
//! The sweep is pinned by one SHA-256 over all 1025 digests, and a row of
//! boundary lengths by their own digests. Both were recorded on 2026-10-15 from
//! the `sha2` crate (0.10.9) that `astream-digest` replaced, while a differential
//! against it (sha2 as a dev-dependency, since dropped) held every length, whole
//! and under eight random splits each, equal to it.

use astream_digest::Sha256;

/// SHA-256 over the concatenated digests of `message(0)` ..= `message(1024)`.
const SWEEP: &str = "f495fcff135572ebceb2942525473baa5ac0845df1b9ea9afb1d51b8ab36f5ce";

/// `(length, digest)` at the padding and block boundaries, and the ends.
const BOUNDARIES: [(usize, &str); 13] = [
    (
        0,
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    ),
    (
        1,
        "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
    ),
    (
        55,
        "8f1e863f0609d5a1ccf47107d4e13784a572656c5458751a83333a68804b2890",
    ),
    (
        56,
        "0816bc277a95ac99a09a80510a30987b1c7379267b180ebe80c6415ef5af5087",
    ),
    (
        63,
        "7b7d08700d8632c229ec7085d4232bec4247c00224391d3b86f197135fb3b0fe",
    ),
    (
        64,
        "b3dcf4c38748bd2d39c0198ad45e7614cf57353eb3557bbc64f984b8ee5124b7",
    ),
    (
        65,
        "29a83d9943799fa40fbece538b80dbb73a22b2fdd51a369beec60ab6d0421fe0",
    ),
    (
        119,
        "15116f6b8ef5a74f7d9ad8a2d3200587a455ffc8f5d0b3df4daf2a11be8340e4",
    ),
    (
        120,
        "a602f9785727b212645c2a9f67f80864c7450eb57c04f471de5aa9dae8fe2096",
    ),
    (
        127,
        "2dff2e1afe5bcc1f038ac211680ffa9958b3d6363f57f8b30933ba5c8c1df81b",
    ),
    (
        128,
        "5e9c7a97eb178cb2a75a9ccd52e8b842c7bd8d97c82d4ebe1f45d68ab23ef9df",
    ),
    (
        1023,
        "6fa2c6ef1b63167b5b683c4d38a59e1fa3320ba884df90cdbf89f862cfaeb5d2",
    ),
    (
        1024,
        "8ce18740272727bc93adfebd406eb4c5d3b37b246a4485b8610276a80c7bbf9a",
    ),
];

/// SplitMix64: a deterministic stream, so a failure names a reproducible input.
struct SplitMix(u64);

impl SplitMix {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// A chunk length in `0..=max`.
    fn below(&mut self, max: usize) -> usize {
        (self.next_u64() % (max as u64 + 1)) as usize
    }
}

/// The first `len` bytes of one fixed pseudo-random 1024-byte message.
fn message(len: usize) -> Vec<u8> {
    let mut rng = SplitMix(0x6173_7472_6561_6d21);
    (0..len).map(|_| rng.next_u64() as u8).collect()
}

/// `msg` fed in random chunks of 0..=130 bytes: shorter than a block, exactly a
/// block, and over two, so a chunk both tops up and spills the partial buffer.
fn split_digest(msg: &[u8], rng: &mut SplitMix) -> [u8; 32] {
    let mut h = Sha256::new();
    let mut rest = msg;
    while !rest.is_empty() {
        let (chunk, tail) = rest.split_at(rng.below(130).min(rest.len()));
        h.update(chunk);
        rest = tail;
    }
    h.finalize()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn every_length_to_1024_is_the_recorded_answer() {
    let mut rng = SplitMix(0x5eed);
    let mut sweep = Sha256::new();
    for len in 0..=1024 {
        let msg = message(len);
        let whole = Sha256::digest(&msg);
        assert_eq!(split_digest(&msg, &mut rng), whole, "{len} bytes, split");
        sweep.update(whole);
    }
    assert_eq!(hex(&sweep.finalize()), SWEEP);
    for (len, want) in BOUNDARIES {
        assert_eq!(hex(&Sha256::digest(message(len))), want, "{len} bytes");
    }
}
