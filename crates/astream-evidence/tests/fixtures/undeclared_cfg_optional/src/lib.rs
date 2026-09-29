// INTENTIONAL VIOLATION FIXTURE (scanned by the gate test only).
#[cfg(feature = "wrap")]
mod wrap {}

#[cfg(feature = "plain")]
mod plain {}

#[cfg(feature = "unixonly")]
mod unixonly {}

// The one undeclared feature: `dep:hidden` suppressed it.
#[cfg(feature = "hidden")]
mod hidden {}
