// INTENTIONAL VIOLATION FIXTURE (not compiled; scanned by the gate test).
// `ghost` is referenced but never declared in Cargo.toml [features] — exactly
// the predecessor's `cloud-dropbox` -> `cloud-Andrew Yates` dead-code class.

#[cfg(feature = "ghost")]
pub fn ghost() {}

#[cfg(feature = "real")]
pub fn real() {}

// Asymmetric / tab spacing around `=` — valid in the attribute and emitted by
// rustfmt, but the old fixed-opener scan never saw these, so an undeclared
// feature could hide here with a green gate.
#[cfg(feature= "ghost2")]
pub fn ghost2() {}

#[cfg(feature ="ghost3")]
pub fn ghost3() {}

// A line break around `=` — also valid in the attribute — must be seen too:
// the scan is whitespace-insensitive, not merely space/tab-insensitive.
#[cfg(feature =
    "ghost4")]
pub fn ghost4() {}
