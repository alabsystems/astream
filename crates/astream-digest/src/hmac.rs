// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! HMAC-SHA256 (RFC 2104) and HKDF-SHA256 (RFC 5869), over this crate's SHA-256.
//!
//! `HMAC(K, m) = H((K0 ^ opad) ‖ H((K0 ^ ipad) ‖ m))`, where `K0` is the key
//! zero-padded to the 64-byte block, or `H(K)` zero-padded when the key is longer
//! than a block (a key of exactly 64 bytes is used verbatim, never hashed).
//!
//! ONE CONSTRUCTION, three doors. There were four copies of this MAC, and nothing
//! held any of them to another: aterm-digest's `hmac_sha256.rs` (the streaming API),
//! aterm-net's fleet HKDF over it, astream-cap's private const `hmac_sha256_parts`
//! (capability tags, attach proofs, Macaroon chains), and astream-aead's private
//! `hmac_sha256` (the handshake's HKDF, which wipes its pads). A fix or a proof had
//! to land four times. All four are gone: astream-cap and astream-aead call this
//! one, aterm-digest re-exports it (aterm cb93e33cff), and aterm-net's fleet HKDF
//! derives through it (aterm a719a8ff7d), so a fix or a proof here reaches every
//! one of them. Every door here goes
//! through the same four steps —
//! [`KeyPads::of`] (the key block and its two pads), [`inner_primed`], the message
//! fed to that inner hash, and [`outer_tag`] — so they cannot drift apart:
//!
//! * [`HmacSha256`] is the streaming door (`new_from_slice`, `update`, `finalize`,
//!   `verify_slice`), aterm-digest's API, `const` but for the verify;
//! * [`hmac_sha256_parts`] is the `const` one-shot over the CONCATENATION of its
//!   parts, astream-cap's core: it is [`HmacSha256`] keyed, fed each part, finalized;
//! * [`hmac_sha256_wiping`] is the one-shot for a key that must not outlive the call
//!   (a pre-shared key, a pseudo-random key): the same steps with the key block and
//!   both pads held on its own frame, which it zeroes before it returns. That is
//!   astream-aead's zeroization, and why it is not `const` (`fill` is not).
//!
//! The key-block derivation and the pad expansion are astream-cap's code, moved here
//! unchanged: every index is masked (`k[i & 63]`) or a literal, so the verified lane
//! (`scripts/verify-ready.sh`) discharges each bounds obligation rather than leaving
//! it open. [`hkdf_extract`] and [`hkdf_expand_32`] are RFC 5869 over the wiping
//! one-shot: astream-aead's handshake and identity session keys derive through them,
//! and so do aterm's fleet keys (aterm-net, through aterm-digest's re-export).
//!
//! The wipe is BEST-EFFORT, as every wipe in safe Rust is: `fill(0)` followed by
//! [`core::hint::black_box`] keeps the optimiser from dropping the stores to arrays
//! it can see are dead, but a copy the compiler made on the way (a moved value, a
//! register spill) and the SHA-256 states the pads were fed into are not wiped.

use crate::{ct_eq, Sha256, BLOCK_LEN, OUTPUT_LEN};

/// Returned by [`HmacSha256::new_from_slice`] for API compatibility with the
/// `hmac` crate. Never produced: HMAC accepts a key of any length.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidLength;

impl std::fmt::Display for InvalidLength {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("invalid key length")
    }
}

impl std::error::Error for InvalidLength {}

/// A MAC did not verify.
///
/// Carries nothing: reporting how a tag was wrong would be a forgery oracle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MacError;

impl std::fmt::Display for MacError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("MAC tag mismatch")
    }
}

impl std::error::Error for MacError {}

/// The key material one HMAC holds while it runs: `K0` (the key reduced to one
/// block), `K0 ^ ipad` and `K0 ^ opad`. Every door derives it here, and only
/// [`hmac_sha256_wiping`] keeps it whole long enough to [`wipe`](KeyPads::wipe) it.
struct KeyPads {
    /// `K0`: the key zero-padded to a block, or its digest zero-padded.
    k0: [u8; BLOCK_LEN],
    /// `K0 ^ 0x36^64`, the block the inner hash starts with.
    ipad: [u8; BLOCK_LEN],
    /// `K0 ^ 0x5c^64`, the block the outer hash starts with.
    opad: [u8; BLOCK_LEN],
}

impl KeyPads {
    /// RFC 2104 §2, steps (1)-(2) and (5): the key block and its two pads.
    const fn of(key: &[u8]) -> Self {
        let k0 = key_block(key);
        let ipad = hmac_ipad(&k0);
        let opad = hmac_opad(&k0);
        Self { k0, ipad, opad }
    }

    /// Zero all three blocks. `black_box` hands the zeroed blocks to code the
    /// optimiser cannot see into, so it cannot prove the stores dead and drop them.
    fn wipe(&mut self) {
        self.k0.fill(0);
        self.ipad.fill(0);
        self.opad.fill(0);
        core::hint::black_box(&mut *self);
    }
}

/// `K0`: a key longer than the block is replaced by its SHA-256 digest; either way
/// the result is zero-padded to [`BLOCK_LEN`] bytes.
const fn key_block(key: &[u8]) -> [u8; BLOCK_LEN] {
    if key.len() > BLOCK_LEN {
        pad_digest_key(Sha256::digest_slice(key))
    } else {
        let mut k = [0u8; BLOCK_LEN];
        let mut i = 0usize;
        let mut rem = key;
        while let &[b, ref tail @ ..] = rem {
            k[i & 63] = b;
            i = (i & 63) + 1;
            rem = tail;
        }
        k
    }
}

const fn hmac_ipad_q0(k: &[u8; BLOCK_LEN]) -> [u8; 16] {
    [
        k[0] ^ 0x36,
        k[1] ^ 0x36,
        k[2] ^ 0x36,
        k[3] ^ 0x36,
        k[4] ^ 0x36,
        k[5] ^ 0x36,
        k[6] ^ 0x36,
        k[7] ^ 0x36,
        k[8] ^ 0x36,
        k[9] ^ 0x36,
        k[10] ^ 0x36,
        k[11] ^ 0x36,
        k[12] ^ 0x36,
        k[13] ^ 0x36,
        k[14] ^ 0x36,
        k[15] ^ 0x36,
    ]
}

const fn hmac_ipad_q1(k: &[u8; BLOCK_LEN]) -> [u8; 16] {
    [
        k[16] ^ 0x36,
        k[17] ^ 0x36,
        k[18] ^ 0x36,
        k[19] ^ 0x36,
        k[20] ^ 0x36,
        k[21] ^ 0x36,
        k[22] ^ 0x36,
        k[23] ^ 0x36,
        k[24] ^ 0x36,
        k[25] ^ 0x36,
        k[26] ^ 0x36,
        k[27] ^ 0x36,
        k[28] ^ 0x36,
        k[29] ^ 0x36,
        k[30] ^ 0x36,
        k[31] ^ 0x36,
    ]
}

const fn hmac_ipad_q2(k: &[u8; BLOCK_LEN]) -> [u8; 16] {
    [
        k[32] ^ 0x36,
        k[33] ^ 0x36,
        k[34] ^ 0x36,
        k[35] ^ 0x36,
        k[36] ^ 0x36,
        k[37] ^ 0x36,
        k[38] ^ 0x36,
        k[39] ^ 0x36,
        k[40] ^ 0x36,
        k[41] ^ 0x36,
        k[42] ^ 0x36,
        k[43] ^ 0x36,
        k[44] ^ 0x36,
        k[45] ^ 0x36,
        k[46] ^ 0x36,
        k[47] ^ 0x36,
    ]
}

const fn hmac_ipad_q3(k: &[u8; BLOCK_LEN]) -> [u8; 16] {
    [
        k[48] ^ 0x36,
        k[49] ^ 0x36,
        k[50] ^ 0x36,
        k[51] ^ 0x36,
        k[52] ^ 0x36,
        k[53] ^ 0x36,
        k[54] ^ 0x36,
        k[55] ^ 0x36,
        k[56] ^ 0x36,
        k[57] ^ 0x36,
        k[58] ^ 0x36,
        k[59] ^ 0x36,
        k[60] ^ 0x36,
        k[61] ^ 0x36,
        k[62] ^ 0x36,
        k[63] ^ 0x36,
    ]
}

const fn hmac_ipad(k: &[u8; BLOCK_LEN]) -> [u8; BLOCK_LEN] {
    let [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] = hmac_ipad_q0(k);
    let [b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] =
        hmac_ipad_q1(k);
    let [b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47] =
        hmac_ipad_q2(k);
    let [b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63] =
        hmac_ipad_q3(k);
    [
        b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19,
        b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37,
        b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
        b56, b57, b58, b59, b60, b61, b62, b63,
    ]
}

const fn hmac_opad_q0(k: &[u8; BLOCK_LEN]) -> [u8; 16] {
    [
        k[0] ^ 0x5c,
        k[1] ^ 0x5c,
        k[2] ^ 0x5c,
        k[3] ^ 0x5c,
        k[4] ^ 0x5c,
        k[5] ^ 0x5c,
        k[6] ^ 0x5c,
        k[7] ^ 0x5c,
        k[8] ^ 0x5c,
        k[9] ^ 0x5c,
        k[10] ^ 0x5c,
        k[11] ^ 0x5c,
        k[12] ^ 0x5c,
        k[13] ^ 0x5c,
        k[14] ^ 0x5c,
        k[15] ^ 0x5c,
    ]
}

const fn hmac_opad_q1(k: &[u8; BLOCK_LEN]) -> [u8; 16] {
    [
        k[16] ^ 0x5c,
        k[17] ^ 0x5c,
        k[18] ^ 0x5c,
        k[19] ^ 0x5c,
        k[20] ^ 0x5c,
        k[21] ^ 0x5c,
        k[22] ^ 0x5c,
        k[23] ^ 0x5c,
        k[24] ^ 0x5c,
        k[25] ^ 0x5c,
        k[26] ^ 0x5c,
        k[27] ^ 0x5c,
        k[28] ^ 0x5c,
        k[29] ^ 0x5c,
        k[30] ^ 0x5c,
        k[31] ^ 0x5c,
    ]
}

const fn hmac_opad_q2(k: &[u8; BLOCK_LEN]) -> [u8; 16] {
    [
        k[32] ^ 0x5c,
        k[33] ^ 0x5c,
        k[34] ^ 0x5c,
        k[35] ^ 0x5c,
        k[36] ^ 0x5c,
        k[37] ^ 0x5c,
        k[38] ^ 0x5c,
        k[39] ^ 0x5c,
        k[40] ^ 0x5c,
        k[41] ^ 0x5c,
        k[42] ^ 0x5c,
        k[43] ^ 0x5c,
        k[44] ^ 0x5c,
        k[45] ^ 0x5c,
        k[46] ^ 0x5c,
        k[47] ^ 0x5c,
    ]
}

const fn hmac_opad_q3(k: &[u8; BLOCK_LEN]) -> [u8; 16] {
    [
        k[48] ^ 0x5c,
        k[49] ^ 0x5c,
        k[50] ^ 0x5c,
        k[51] ^ 0x5c,
        k[52] ^ 0x5c,
        k[53] ^ 0x5c,
        k[54] ^ 0x5c,
        k[55] ^ 0x5c,
        k[56] ^ 0x5c,
        k[57] ^ 0x5c,
        k[58] ^ 0x5c,
        k[59] ^ 0x5c,
        k[60] ^ 0x5c,
        k[61] ^ 0x5c,
        k[62] ^ 0x5c,
        k[63] ^ 0x5c,
    ]
}

const fn hmac_opad(k: &[u8; BLOCK_LEN]) -> [u8; BLOCK_LEN] {
    let [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] = hmac_opad_q0(k);
    let [b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] =
        hmac_opad_q1(k);
    let [b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47] =
        hmac_opad_q2(k);
    let [b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63] =
        hmac_opad_q3(k);
    [
        b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19,
        b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37,
        b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
        b56, b57, b58, b59, b60, b61, b62, b63,
    ]
}

const fn pad_digest_key(d: [u8; OUTPUT_LEN]) -> [u8; BLOCK_LEN] {
    [
        d[0], d[1], d[2], d[3], d[4], d[5], d[6], d[7], d[8], d[9], d[10], d[11], d[12], d[13],
        d[14], d[15], d[16], d[17], d[18], d[19], d[20], d[21], d[22], d[23], d[24], d[25], d[26],
        d[27], d[28], d[29], d[30], d[31], 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ]
}

/// The inner hash, primed with `K0 ^ ipad` and ready for the message.
const fn inner_primed(ipad: &[u8; BLOCK_LEN]) -> Sha256 {
    let mut inner = Sha256::new();
    inner.update_slice(ipad);
    inner
}

/// The tag: `H((K0 ^ opad) ‖ H((K0 ^ ipad) ‖ m))`, given the inner hash that has
/// absorbed `(K0 ^ ipad) ‖ m`.
const fn outer_tag(opad: &[u8; BLOCK_LEN], inner: Sha256) -> [u8; OUTPUT_LEN] {
    let ih = inner.finalize();
    let mut outer = Sha256::new();
    outer.update_slice(opad);
    outer.update_slice(&ih);
    outer.finalize()
}

/// HMAC-SHA256 (RFC 2104), keyed with SHA-256: the streaming door.
///
/// [`finalize`](HmacSha256::finalize) returns a plain `[u8; 32]`. Fed in pieces or
/// whole, it answers the same tag ([`hmac_sha256_parts`] is exactly that).
///
/// # Example
///
/// ```rust
/// use astream_digest::HmacSha256;
///
/// let mut mac = HmacSha256::new_from_slice(b"shared secret")
///     .expect("HMAC-SHA256 accepts a key of any length");
/// mac.update(b"authenticated data");
/// let tag = mac.finalize();
///
/// let mut verifier = HmacSha256::new_from_slice(b"shared secret")
///     .expect("HMAC-SHA256 accepts a key of any length");
/// verifier.update(b"authenticated data");
/// assert!(verifier.verify_slice(&tag).is_ok());
/// ```
#[derive(Clone)]
pub struct HmacSha256 {
    /// `H((K0 ^ ipad) ‖ m)` in progress: primed with the ipad block.
    inner: Sha256,
    /// `K0 ^ opad`, held until the outer hash runs at finalize time.
    outer_key: [u8; BLOCK_LEN],
}

impl HmacSha256 {
    /// The MAC under `key`, infallibly: what [`new_from_slice`](Self::new_from_slice)
    /// answers inside its `Ok`, and what [`hmac_sha256_parts`] starts from.
    const fn keyed(key: &[u8]) -> Self {
        let pads = KeyPads::of(key);
        Self {
            inner: inner_primed(&pads.ipad),
            outer_key: pads.opad,
        }
    }

    /// Creates a MAC over the given key.
    ///
    /// Keys longer than the 64-byte block are replaced by their SHA-256 digest;
    /// shorter keys are zero-padded.
    ///
    /// # Errors
    ///
    /// Never. See [`InvalidLength`].
    pub const fn new_from_slice(key: &[u8]) -> Result<Self, InvalidLength> {
        Ok(Self::keyed(key))
    }

    /// Feeds more bytes into the authenticated message.
    pub const fn update(&mut self, bytes: &[u8]) {
        self.inner.update_slice(bytes);
    }

    /// Finishes the MAC and returns the 32-byte tag.
    #[must_use]
    pub const fn finalize(self) -> [u8; OUTPUT_LEN] {
        outer_tag(&self.outer_key, self.inner)
    }

    /// Checks `tag` against the computed MAC through [`ct_eq`]: no data-dependent
    /// exit in the byte fold, and a tag of the wrong length refused on its length.
    ///
    /// # Errors
    ///
    /// [`MacError`] when `tag` is not the MAC of the message fed in, including
    /// a truncated or an extended tag.
    pub fn verify_slice(self, tag: &[u8]) -> Result<(), MacError> {
        if ct_eq(&self.finalize(), tag) {
            Ok(())
        } else {
            Err(MacError)
        }
    }
}

impl std::fmt::Debug for HmacSha256 {
    /// Opaque on purpose: the struct holds `K0 ^ opad`, from which the key block is
    /// recoverable by XOR. That must never reach a log line.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HmacSha256").finish_non_exhaustive()
    }
}

/// HMAC-SHA256 under `key` of the CONCATENATION of `parts`, streamed into the inner
/// hash one part at a time: the same tag as one [`HmacSha256`] fed the joined bytes,
/// without materialising the join. `const`, so a capability tag or an attach proof
/// can be computed in a `const fn`.
#[must_use]
pub const fn hmac_sha256_parts(key: &[u8], parts: &[&[u8]]) -> [u8; OUTPUT_LEN] {
    let mut mac = HmacSha256::keyed(key);
    let mut rem = parts;
    while let &[part, ref tail @ ..] = rem {
        mac.update(part);
        rem = tail;
    }
    mac.finalize()
}

/// [`hmac_sha256_parts`] for a key that must not outlive the call: the same steps,
/// with the key block `K0` and both pads held on this frame and zeroed before it
/// returns (best-effort; see the module doc). Not `const`, because `fill` is not.
#[must_use]
pub fn hmac_sha256_wiping(key: &[u8], parts: &[&[u8]]) -> [u8; OUTPUT_LEN] {
    let mut pads = KeyPads::of(key);
    tag_then_wipe(&mut pads, parts)
}

/// The wiping door's body, on pads its caller holds: the tag over `parts`, then the
/// wipe of all three blocks, so the pads are zero when it returns. It takes the
/// pads by reference so a test can hold them across the call and see them zeroed:
/// the one thing that sets this door apart from [`hmac_sha256_parts`] is then
/// pinned, where a wipe on a frame nothing else can read was not.
fn tag_then_wipe(pads: &mut KeyPads, parts: &[&[u8]]) -> [u8; OUTPUT_LEN] {
    let mut inner = inner_primed(&pads.ipad);
    for part in parts {
        inner.update_slice(part);
    }
    let tag = outer_tag(&pads.opad, inner);
    pads.wipe();
    tag
}

/// HKDF-Extract (RFC 5869 §2.2): `PRK = HMAC-SHA256(salt, IKM)`.
///
/// An empty salt is RFC 5869's "not provided", a string of 32 zero bytes: HMAC
/// zero-pads both to the same block, so the two give one PRK. Through
/// [`hmac_sha256_wiping`], so the salt's key block (a pre-shared key, when the
/// salt is one) does not outlive the call; the PRK it returns is the caller's to
/// wipe.
#[must_use]
pub fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> [u8; OUTPUT_LEN] {
    hmac_sha256_wiping(salt, &[ikm])
}

/// HKDF-Expand (RFC 5869 §2.3) for exactly 32 bytes of output key material, its
/// first block alone: `T(1) = HMAC-SHA256(PRK, info ‖ 0x01)` (`T(0)` is empty).
/// Through [`hmac_sha256_wiping`], so the PRK's key block does not outlive the call.
#[must_use]
pub fn hkdf_expand_32(prk: &[u8; OUTPUT_LEN], info: &[u8]) -> [u8; OUTPUT_LEN] {
    hmac_sha256_wiping(prk, &[info, &[0x01]])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    fn unhex(s: &str) -> Vec<u8> {
        assert!(s.len().is_multiple_of(2), "an odd hex digit: {s}");
        (0..s.len() / 2)
            .map(|i| u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).unwrap())
            .collect()
    }

    /// The streaming door, fed `data` whole.
    fn mac(key: &[u8], data: &[u8]) -> [u8; OUTPUT_LEN] {
        let mut m = HmacSha256::new_from_slice(key).expect("HMAC-SHA256 accepts any key length");
        m.update(data);
        m.finalize()
    }

    /// All three doors on one `(key, data)`, held to one answer.
    fn mac_all_doors(key: &[u8], data: &[u8]) -> [u8; OUTPUT_LEN] {
        let streamed = mac(key, data);
        assert_eq!(hmac_sha256_parts(key, &[data]), streamed, "parts door");
        assert_eq!(hmac_sha256_wiping(key, &[data]), streamed, "wiping door");
        streamed
    }

    // -----------------------------------------------------------------------
    // RFC 4231 test vectors for HMAC-SHA256
    // -----------------------------------------------------------------------

    /// RFC 4231 §4.2–4.8, one row per test case: `(case, key, data, tag)`, through
    /// every door. Case 5 is published truncated to 128 bits, so its tag is
    /// compared over the first 16 bytes only; cases 6 and 7 carry a 131-byte key, so
    /// they pin the hash-the-key-first path a short key never reaches. Negative
    /// control: the same data under the key with one bit flipped is a different tag
    /// in every case, so a MAC that ignored its key would fail here.
    #[test]
    fn rfc4231_test_vectors() {
        let case4_key: Vec<u8> = (0x01u8..=0x19).collect();
        assert_eq!(case4_key.len(), 25);
        let case7_data: &[u8] = b"This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm.";
        assert_eq!(case7_data.len(), 152);
        for (case, key, data, tag) in [
            (
                1,
                &[0x0b; 20][..],
                &b"Hi There"[..],
                "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7",
            ),
            // A key shorter than the digest, exercising the zero-pad path.
            (
                2,
                b"Jefe",
                b"what do ya want for nothing?",
                "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843",
            ),
            (
                3,
                &[0xaa; 20],
                &[0xdd; 50],
                "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe",
            ),
            (
                4,
                &case4_key,
                &[0xcd; 50],
                "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b",
            ),
            // Published truncated to 128 bits.
            (
                5,
                &[0x0c; 20],
                b"Test With Truncation",
                "a3b6167473100ee06e0c796c2955552b",
            ),
            // 131-byte key: longer than the 64-byte block, so it is hashed first.
            (
                6,
                &[0xaa; 131],
                b"Test Using Larger Than Block-Size Key - Hash Key First",
                "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54",
            ),
            // Over-block-size key and over-block-size data.
            (
                7,
                &[0xaa; 131],
                case7_data,
                "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2",
            ),
        ] {
            let full = mac_all_doors(key, data);
            assert_eq!(hex(&full[..tag.len() / 2]), tag, "RFC 4231 case {case}");

            let mut other = key.to_vec();
            other[0] ^= 0x01;
            assert_ne!(mac(&other, data), full, "case {case}: the key must matter");
        }
    }

    /// The block boundary from both sides, through every door: a key of exactly one
    /// block (64 bytes) is padded, never hashed, and one of 65 is hashed first. The
    /// two answers are astream-aead's, from Python's `hmac` module. Negative control:
    /// the 64-byte key's answer is NOT the answer of its digest as a key, which is
    /// what a hash-at-64 off-by-one would compute; the 65-byte key's answer IS its
    /// digest's (RFC 2104 §2), so the hashing branch is the one the 65 takes.
    #[test]
    fn known_answers_on_both_sides_of_the_block_size() {
        let block: Vec<u8> = (0u8..64).collect();
        let over: Vec<u8> = (0u8..65).collect();
        let msg = b"block-size boundary";
        for (key, want) in [
            (
                &block[..],
                "0e28123f03dbcda96a31302c68e4cf3f092abf8b6394c1f825056927622a7a38",
            ),
            (
                &over[..],
                "bb5c919dfb366ab7388b18d7785e4bbc90550971b16ccae1c68417455dd03799",
            ),
        ] {
            assert_eq!(
                hex(&mac_all_doors(key, msg)),
                want,
                "{}-byte key",
                key.len()
            );
        }
        assert_ne!(mac(&block, msg), mac(&Sha256::digest(&block), msg));
        assert_eq!(mac(&over, msg), mac(&Sha256::digest(&over), msg));
    }

    /// `hmac_sha256_parts` and `hmac_sha256_wiping` MAC the concatenation: where the
    /// message is cut is not part of the tag, the empty part and the empty list
    /// included. Negative control: moving one byte between the key and the message
    /// changes the tag.
    #[test]
    fn the_parts_doors_mac_the_concatenation_wherever_it_is_cut() {
        let key = [7u8; 32];
        let whole = mac(&key, b"abcd");
        for parts in [
            &[&b"abcd"[..]][..],
            &[b"ab", b"cd"],
            &[b"abc", b"d"],
            &[b"", b"abcd", b""],
            &[b"a", b"b", b"c", b"d"],
        ] {
            assert_eq!(hmac_sha256_parts(&key, parts), whole, "{parts:?}");
            assert_eq!(hmac_sha256_wiping(&key, parts), whole, "{parts:?}");
        }
        assert_eq!(hmac_sha256_parts(&key, &[]), mac(&key, b""));
        assert_eq!(hmac_sha256_wiping(&key, &[]), mac(&key, b""));
        let mut longer_key = key.to_vec();
        longer_key.push(b'a');
        assert_ne!(mac(&longer_key, b"bcd"), whole);
    }

    /// The wiping door zeroes all 192 bytes it holds: `tag_then_wipe`, the body of
    /// `hmac_sha256_wiping`, returns the door's tag and leaves the pads it was handed
    /// all zero, so deleting its wipe fails here. Negative control: before the call
    /// no pad is zero (an all-zero `K0` still has pads of 0x36 and 0x5c), so the
    /// check after it is not vacuous; and the tag is the streaming door's, so a body
    /// that zeroed the pads BEFORE using them would fail too.
    #[test]
    fn the_wiping_door_zeroes_its_key_block_and_both_pads() {
        for key in [&b""[..], b"Jefe", &[0xaa; 131]] {
            let mut pads = KeyPads::of(key);
            assert!(pads.ipad.iter().any(|&b| b != 0), "{}", key.len());
            assert!(pads.opad.iter().any(|&b| b != 0), "{}", key.len());
            assert_eq!(pads.k0.iter().any(|&b| b != 0), !key.is_empty());
            let tag = tag_then_wipe(&mut pads, &[b"wiped"]);
            assert_eq!(tag, mac(key, b"wiped"), "{}", key.len());
            assert_eq!(tag, hmac_sha256_wiping(key, &[b"wiped"]));
            assert!(pads.k0.iter().all(|&b| b == 0), "{}", key.len());
            assert!(pads.ipad.iter().all(|&b| b == 0), "{}", key.len());
            assert!(pads.opad.iter().all(|&b| b == 0), "{}", key.len());
        }
    }

    // -----------------------------------------------------------------------
    // Verification
    // -----------------------------------------------------------------------

    /// The full tag verifies; its 16-byte prefix and a 33-byte extension do not.
    #[test]
    fn verify_slice_rejects_a_truncated_or_extended_tag() {
        let tag = mac(b"k", b"payload");

        let mut whole = HmacSha256::new_from_slice(b"k").expect("any key length");
        whole.update(b"payload");
        assert!(whole.verify_slice(&tag).is_ok());

        // A truncated tag must not validate on its prefix.
        let mut truncated = HmacSha256::new_from_slice(b"k").expect("any key length");
        truncated.update(b"payload");
        assert!(truncated.verify_slice(&tag[..16]).is_err());

        // Nor an over-long one.
        let mut extended = HmacSha256::new_from_slice(b"k").expect("any key length");
        extended.update(b"payload");
        let mut longer = tag.to_vec();
        longer.push(0);
        assert!(extended.verify_slice(&longer).is_err());
    }

    /// EVERY one-bit flip of a tag is refused: all 256 of them, for one key and
    /// message (the length sweep in `tests/lengths_and_streaming.rs` flips one random
    /// bit per length). Control: the unflipped tag verifies under the same MAC state,
    /// so each refusal is the flip's.
    #[test]
    fn verify_slice_refuses_every_one_bit_flip_of_the_tag() {
        let keyed = |msg: &[u8]| {
            let mut m = HmacSha256::new_from_slice(b"k").expect("any key length");
            m.update(msg);
            m
        };
        let tag = mac(b"k", b"payload");
        assert!(keyed(b"payload").verify_slice(&tag).is_ok());
        for i in 0..OUTPUT_LEN {
            for bit in 0..8 {
                let mut flipped = tag;
                flipped[i] ^= 1 << bit;
                assert!(
                    keyed(b"payload").verify_slice(&flipped).is_err(),
                    "byte {i}, bit {bit}"
                );
            }
        }
    }

    /// `Debug` is the constant `HmacSha256 { .. }` for every key and message, the
    /// whole output and not a prefix of it: a derived `Debug` would print the
    /// `outer_key` bytes in decimal, which never spell the key's text and from which
    /// the key block is one XOR away, so a test that only looked for the key's text
    /// would pass it. Negative control: a key that is not a secret DOES appear in
    /// the bytes of its key block, so opacity is what keeps it out, not luck.
    #[test]
    fn debug_does_not_leak_the_key() {
        for (key, msg) in [
            (&b"a very secret key"[..], &b"x"[..]),
            (b"", b""),
            (&[0xaa; 131], b"over a block"),
        ] {
            let mut m = HmacSha256::new_from_slice(key).expect("any key length");
            m.update(msg);
            assert_eq!(format!("{m:?}"), "HmacSha256 { .. }", "{}", key.len());
            assert_eq!(format!("{m:#?}"), "HmacSha256 { .. }", "{}", key.len());
        }
        let k0 = String::from_utf8(KeyPads::of(b"a very secret key").k0.to_vec()).unwrap();
        assert!(k0.contains("secret"));
    }

    // -----------------------------------------------------------------------
    // HKDF-SHA256 (RFC 5869)
    // -----------------------------------------------------------------------

    /// RFC 5869 Appendix A.1-A.3 (SHA-256): the PRK and the first 32 bytes of the OKM.
    /// A.2's 80-byte salt is longer than the HMAC block, so Extract hashes it first,
    /// the path A.1's 13-byte salt never reaches; A.3 has an empty salt and an empty
    /// info. Negative control: A.1 with one info byte changed is another key.
    #[test]
    fn hkdf_matches_rfc5869_a1_a2_and_a3() {
        let a2_salt: Vec<u8> = (0x60u8..=0xaf).collect();
        let a2_ikm: Vec<u8> = (0x00u8..=0x4f).collect();
        let a2_info: Vec<u8> = (0xb0u8..=0xff).collect();
        for (case, ikm, salt, info, prk, okm) in [
            (
                "A.1",
                vec![0x0bu8; 22],
                unhex("000102030405060708090a0b0c"),
                unhex("f0f1f2f3f4f5f6f7f8f9"),
                "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5",
                "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf",
            ),
            (
                "A.2",
                a2_ikm,
                a2_salt,
                a2_info,
                "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244",
                "b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c",
            ),
            (
                "A.3",
                vec![0x0bu8; 22],
                Vec::new(),
                Vec::new(),
                "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04",
                "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d",
            ),
        ] {
            let got_prk = hkdf_extract(&salt, &ikm);
            assert_eq!(hex(&got_prk), prk, "RFC 5869 {case} PRK");
            assert_eq!(hex(&hkdf_expand_32(&got_prk, &info)), okm, "{case} OKM");
            let mut other = info.clone();
            other.push(0);
            assert_ne!(hex(&hkdf_expand_32(&got_prk, &other)), okm, "{case}");
        }
    }

    /// An empty salt is RFC 5869's default, `HashLen` zero bytes: one PRK. Negative
    /// control: a salt of 32 ones is a different PRK.
    #[test]
    fn an_empty_salt_is_32_zero_bytes() {
        let ikm = b"input keying material";
        assert_eq!(hkdf_extract(&[], ikm), hkdf_extract(&[0u8; 32], ikm));
        assert_ne!(hkdf_extract(&[], ikm), hkdf_extract(&[1u8; 32], ikm));
    }

    /// Recorded answer: the session key astream-aead's PSK handshake derives for
    /// `psk = [9; 32]`, `dh = [7; 32]` and ephemerals `[1; 32]` (client), `[2; 32]`
    /// (server), recorded over the `sha2` crate (0.10.9) on 2026-10-15 before
    /// astream-aead moved to this crate's hash, and unchanged since its HMAC moved
    /// here. Both ends of every handshake derive this key, so the HMAC under it may
    /// change only if it does not. The info is the handshake's label then the two
    /// ephemerals in role order (astream-aead `build_hs_info`, pinned there).
    #[test]
    fn the_handshake_session_key_is_the_recorded_answer() {
        let mut info = b"astream-handshake-v1".to_vec();
        info.extend_from_slice(&[1u8; 32]);
        info.extend_from_slice(&[2u8; 32]);
        let prk = hkdf_extract(&[9u8; 32], &[7u8; 32]);
        assert_eq!(
            hex(&hkdf_expand_32(&prk, &info)),
            "0d5a777ebe43ec2044188fa05d226c609e80df383b6cfce2b3cfa2bacbc64c24"
        );
    }
}
