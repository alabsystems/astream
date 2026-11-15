//! Spawned-shell agent environment-variable strip verifier (`aterm` primer).

#[cfg(clean_islands)]
#[path = "env_sanitization_verifier_island.rs"]
mod env_sanitization_verifier_island;
#[cfg(clean_islands)]
pub use env_sanitization_verifier_island::{env_prefix_family_clamp, env_stripped_count_advance};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn env_stripped_count_advance(prev_count: u64, next_count: u64) -> u64 {
    if prev_count < next_count {
        next_count
    } else {
        prev_count
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn env_prefix_family_clamp(family_idx: u64) -> u64 {
    if family_idx < 13 {
        family_idx
    } else {
        13
    }
}

contract_fn! {
    #[must_use]
    pub const fn env_spawn_clean(leaked_vars: u64) -> bool
    clauses [ensures result == ((leaked_vars < 1))]
    {
        leaked_vars < 1
    }
}

pub const STRIPPED_ENV_PREFIXES: [&str; 13] = [
    "CLAUDE",
    "ANTHROPIC_",
    "COPILOT_",
    "CODEX_",
    "ANTIGRAVITY_",
    "GEMINI_",
    "CURSOR_",
    "GROK_",
    "XAI_",
    "KIMI_",
    "MOONSHOT_",
    "AI_",
    "_DEVTOOL_",
];

#[must_use]
const fn has_byte_prefix(mut key: &[u8], mut prefix: &[u8]) -> bool {
    while let &[pb, ref ptail @ ..] = prefix {
        let &[kb, ref ktail @ ..] = key else {
            return false;
        };
        if kb != pb {
            return false;
        }
        key = ktail;
        prefix = ptail;
    }
    true
}

#[must_use]
pub const fn classify_stripped_env_key(key: &str) -> Option<usize> {
    let key_bytes = key.as_bytes();
    let mut rest: &[&str] = &STRIPPED_ENV_PREFIXES;
    let mut i = 0u64;
    while let &[prefix, ref tail @ ..] = rest {
        if has_byte_prefix(key_bytes, prefix.as_bytes()) {
            return Some(env_prefix_family_clamp(i) as usize);
        }
        i = i.saturating_add(1);
        rest = tail;
    }
    None
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnvSanitizationVerifier {
    stripped_total: u64,
}

impl EnvSanitizationVerifier {
    #[must_use]
    pub const fn new() -> Self {
        Self { stripped_total: 0 }
    }

    #[must_use]
    pub const fn stripped_total(&self) -> u64 {
        self.stripped_total
    }

    pub fn should_keep_for_child(&mut self, key: &str) -> bool {
        if classify_stripped_env_key(key).is_some() {
            let next = self.stripped_total.saturating_add(1);
            self.stripped_total = env_stripped_count_advance(self.stripped_total, next);
            false
        } else {
            true
        }
    }

    #[must_use]
    pub fn audit_child_env<S: AsRef<str>>(keys: &[S]) -> bool {
        let mut leaked = 0u64;
        let mut rest = keys;
        while let [k, tail @ ..] = rest {
            if classify_stripped_env_key(k.as_ref()).is_some() {
                leaked = leaked.saturating_add(1);
            }
            rest = tail;
        }
        env_spawn_clean(leaked)
    }
}

impl Default for EnvSanitizationVerifier {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strips_all_thirteen_agent_families_while_keeping_aterm_and_atpkg_vars() {
        let mut v = EnvSanitizationVerifier::new();
        assert!(!v.should_keep_for_child("CLAUDECODE"));
        assert!(!v.should_keep_for_child("ANTHROPIC_API_KEY"));
        assert!(!v.should_keep_for_child("ANTIGRAVITY_TOKEN"));
        assert!(!v.should_keep_for_child("_DEVTOOL_PORT"));
        assert!(v.should_keep_for_child("ATERM_SESSION_ID"));
        assert!(v.should_keep_for_child("ATPKG_BIN"));
        assert_eq!(v.stripped_total(), 4);
        assert!(EnvSanitizationVerifier::audit_child_env(&[
            "PATH",
            "ATERM_CHILD"
        ]));
        assert!(!EnvSanitizationVerifier::audit_child_env(&[
            "PATH",
            "GEMINI_API_KEY"
        ]));
        assert_eq!(env_prefix_family_clamp(99), 13);
    }
}
