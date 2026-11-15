// An inline island: a stock rustc stops at its first backtick.
clean {
    -- `x` is a natural number
    def x : Nat := 0
}

// A gated island file: the stock rustc never opens it.
#[cfg(clean_islands)]
#[path = "gated_island.rs"]
mod gated_island;

// An ungated island file: the stock rustc opens it.
mod ungated_island;

// A bare contract clause, outside `contract_fn!`.
pub fn within(len: u64, cap: u64) -> bool
    ensures result == (len <= cap)
{
    len <= cap
}

contract_fn! {
    pub fn through_the_macro(len: u64, cap: u64) -> bool
    clauses [ensures result == (len <= cap)]
    {
        len <= cap
    }
}
