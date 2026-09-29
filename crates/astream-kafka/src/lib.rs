#![forbid(unsafe_code)]
//! `astream-kafka` — a Kafka wire-protocol **codec** (codec only, not yet wired).
//! It is the seed of the doctrine's answer to the ecosystem-maturity exception —
//! inherit Kafka's clients + tooling by speaking its protocol, while the better
//! engine runs underneath — but today **no Kafka client can connect to anything**:
//! this crate opens no socket, is not a dependency of `astream-broker`, and the
//! broker's TCP accept path (`asb serve --tcp`) speaks astream `Frame`s, not Kafka
//! framing. A Kafka client pointed at it gets a connection that never answers.
//! Wiring the codec into an accept path is a designed, unbuilt increment.
//!
//! What IS built is the **handshake + discovery** layer as bytes in / bytes out:
//! [`parse_header`] and [`respond`] take one Kafka request (without the outer
//! 4-byte size prefix — the caller frames that) and produce the `ApiVersions` or
//! `Metadata` response, which is what a real Kafka client sends first and uses to
//! find the broker, topics, and partition leaders. astream advertises
//! `max_version = 0` for the APIs it speaks, so a client negotiates down to the
//! simple (non-"flexible") v0 schemas this module parses + emits, byte-for-byte
//! per the Kafka protocol spec.
//!
//! Version negotiation is honest about the v0-only scope: a real client's FIRST
//! message is an `ApiVersions` request at the client's OWN highest version (often a
//! "flexible" v3+), before it has learned the broker's range. Per the Kafka spec's
//! one bootstrap special case, an `ApiVersions` request at an unsupported version is
//! answered with `error_code = UNSUPPORTED_VERSION (35)` in a v0-shaped body that
//! still carries the supported-versions array — so the client downgrades and retries
//! at v0. (Emitting `error_code = 0` with v0 bytes to a flexible client is strictly
//! worse: it would misparse the v0 INT32 array length as a compact unsigned varint.)
//! Any other API requested above its advertised max gets a valid empty-bodied frame
//! rather than a mis-versioned body it would misparse.
//!
//! Not built yet, besides the wiring above: the **Produce / Fetch data path**
//! (record-batch v2 + CRC32C). This module is std-only, zero third-party deps,
//! `forbid(unsafe)`: the protocol codec, deliberately not a client library.

use std::collections::HashSet;

/// Kafka API keys this surface answers.
pub const API_VERSIONS: i16 = 18;
pub const METADATA: i16 = 3;

/// Kafka error codes this surface emits.
const NONE: i16 = 0;
const UNKNOWN_TOPIC_OR_PARTITION: i16 = 3;
const UNSUPPORTED_VERSION: i16 = 35;

/// What astream advertises in an `ApiVersions` response: `(api_key, min, max)`. We
/// cap every API at v0 so clients use the non-flexible schemas implemented here.
const SUPPORTED: &[(i16, i16, i16)] = &[(API_VERSIONS, 0, 0), (METADATA, 0, 0)];

/// The max version astream implements for `api_key`, or `None` for an unknown key.
fn max_version(api_key: i16) -> Option<i16> {
    SUPPORTED
        .iter()
        .find(|&&(k, _, _)| k == api_key)
        .map(|&(_, _, max)| max)
}

/// One broker astream advertises to Kafka clients (this node).
#[derive(Debug, Clone)]
pub struct BrokerMeta {
    pub node_id: i32,
    pub host: String,
    pub port: i32,
}

/// The cluster view astream presents over the Kafka protocol: this single broker
/// and the topics it serves (each a single partition led by this node).
#[derive(Debug, Clone)]
pub struct ClusterMeta {
    pub broker: BrokerMeta,
    pub topics: Vec<String>,
}

// ---- Kafka wire primitives (every wire integer is big-endian) ----

fn put_i16(o: &mut Vec<u8>, v: i16) {
    o.extend_from_slice(&v.to_be_bytes());
}
fn put_i32(o: &mut Vec<u8>, v: i32) {
    o.extend_from_slice(&v.to_be_bytes());
}
fn put_str(o: &mut Vec<u8>, s: &str) {
    // A Kafka v0 STRING length is an i16: a name >= 32768 bytes would wrap to a
    // negative length and be decoded as a null string, corrupting the rest of the
    // frame. Clamp to the largest char boundary that fits so length == bytes written.
    // (Advertised names are short; this is fail-safe defense-in-depth.)
    let mut n = s.len().min(i16::MAX as usize);
    while n > 0 && !s.is_char_boundary(n) {
        n -= 1;
    }
    put_i16(o, n as i16);
    o.extend_from_slice(&s.as_bytes()[..n]);
}

/// A bounds-checked big-endian cursor over a request body (fails closed).
struct Cur<'a> {
    b: &'a [u8],
    i: usize,
}
impl Cur<'_> {
    fn i16(&mut self) -> Option<i16> {
        let e = self.i.checked_add(2)?;
        let v = i16::from_be_bytes(self.b.get(self.i..e)?.try_into().ok()?);
        self.i = e;
        Some(v)
    }
    fn i32(&mut self) -> Option<i32> {
        let e = self.i.checked_add(4)?;
        let v = i32::from_be_bytes(self.b.get(self.i..e)?.try_into().ok()?);
        self.i = e;
        Some(v)
    }
    fn kstring(&mut self) -> Option<Option<String>> {
        let n = self.i16()?;
        if n < 0 {
            return Some(None); // null string
        }
        let e = self.i.checked_add(n as usize)?;
        let s = String::from_utf8(self.b.get(self.i..e)?.to_vec()).ok()?;
        self.i = e;
        Some(Some(s))
    }
}

/// A decoded Kafka request header (v1 header: client_id present).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReqHeader {
    pub api_key: i16,
    pub api_version: i16,
    pub correlation_id: i32,
    pub client_id: Option<String>,
}

/// Parse a Kafka request (WITHOUT the outer 4-byte size prefix — the caller frames
/// that). Returns the header and the offset where the body begins. Panic-free.
pub fn parse_header(req: &[u8]) -> Option<(ReqHeader, usize)> {
    let mut c = Cur { b: req, i: 0 };
    let api_key = c.i16()?;
    let api_version = c.i16()?;
    let correlation_id = c.i32()?;
    let client_id = c.kstring()?;
    Some((
        ReqHeader {
            api_key,
            api_version,
            correlation_id,
            client_id,
        },
        c.i,
    ))
}

/// Build a full Kafka response frame (with the 4-byte size prefix) for `req` against
/// `cluster`. Returns `None` if the request header is unparseable, or if the
/// response would not fit the protocol's i32 frame size.
///
/// Version-gated (see the module docs): an `ApiVersions` request above the supported
/// range gets a v0-shaped body with `error_code = UNSUPPORTED_VERSION` plus the
/// supported-versions array (the spec's bootstrap downgrade path); any other API
/// requested above its advertised max — or an unknown API key — gets a valid
/// empty-bodied response (correlation id echoed) rather than a mis-versioned body.
pub fn respond(req: &[u8], cluster: &ClusterMeta) -> Option<Vec<u8>> {
    let (h, body_at) = parse_header(req)?;
    let body = &req[body_at..];
    let supported =
        max_version(h.api_key).is_some_and(|m| h.api_version >= 0 && h.api_version <= m);
    let payload = match h.api_key {
        // The ApiVersions reply ALWAYS uses the v0 response header + body shape (a
        // Kafka special case), so this is parseable even by a flexible-v3+ client; the
        // error code, not the framing, tells it to downgrade.
        API_VERSIONS if supported => api_versions_response(NONE),
        API_VERSIONS => api_versions_response(UNSUPPORTED_VERSION),
        METADATA if supported => metadata_response(body, cluster),
        // Known API at an unimplemented version, or an unknown API: a valid empty
        // frame the client can cleanly reject, never a mis-encoded body.
        _ => Vec::new(),
    };
    // Response = size:i32 | correlation_id:i32 | payload.
    let mut out = Vec::with_capacity(8 + payload.len());
    put_i32(&mut out, frame_size(payload.len())?);
    put_i32(&mut out, h.correlation_id);
    out.extend_from_slice(&payload);
    Some(out)
}

/// The response frame's size prefix: the correlation id plus the payload, or
/// `None` if that does not fit the protocol's i32 size field.
fn frame_size(payload_len: usize) -> Option<i32> {
    i32::try_from(payload_len.checked_add(4)?).ok()
}

/// ApiVersions v0 response body: error_code:i16, then an array of
/// (api_key:i16, min_version:i16, max_version:i16). The supported array is sent even
/// with `UNSUPPORTED_VERSION` so an over-eager client learns the range and downgrades.
fn api_versions_response(error_code: i16) -> Vec<u8> {
    let mut o = Vec::new();
    put_i16(&mut o, error_code);
    put_i32(&mut o, SUPPORTED.len() as i32);
    for &(key, min, max) in SUPPORTED {
        put_i16(&mut o, key);
        put_i16(&mut o, min);
        put_i16(&mut o, max);
    }
    o
}

/// Metadata v0 response body: brokers[], then topics[]. The request lists the topics
/// the client wants (an empty/all list → advertise every served topic). A topic the
/// client explicitly asks for but we do not serve is returned with
/// `UNKNOWN_TOPIC_OR_PARTITION` rather than silently dropped — so the client sees a
/// definitive answer instead of an empty set it must time out on. Like Kafka, the
/// answer covers the SET of requested topics (first-request order): a repeated name
/// is answered once, so a request of repeats cannot amplify into a larger response.
fn metadata_response(body: &[u8], cluster: &ClusterMeta) -> Vec<u8> {
    // Parse the requested topic array (v0: i32 count, then strings). The count is
    // attacker-controlled, so it is NOT a trusted loop bound: stop as soon as the
    // body is exhausted (a huge count over a short body must not spin).
    // `None` asks for every topic (an empty or null array); a request that NAMED
    // topics is answered only for the names it carried, even when truncation or
    // null entries leave none of them readable — never widened to all topics.
    let mut c = Cur { b: body, i: 0 };
    let requested: Option<Vec<String>> = match c.i32() {
        Some(n) if n > 0 => {
            let mut v = Vec::new();
            for _ in 0..n {
                match c.kstring() {
                    Some(Some(s)) => v.push(s),
                    Some(None) => continue, // null topic entry
                    None => break,          // truncated body: no more topics
                }
            }
            Some(v)
        }
        _ => None, // null/empty/all → advertise everything we serve
    };

    let mut o = Vec::new();
    // brokers: array of (node_id:i32, host:string, port:i32)
    put_i32(&mut o, 1);
    put_i32(&mut o, cluster.broker.node_id);
    put_str(&mut o, &cluster.broker.host);
    put_i32(&mut o, cluster.broker.port);
    // topics: array of (error_code:i16, name:string, partitions[]).
    let node = cluster.broker.node_id;
    if let Some(requested) = requested {
        let served: HashSet<&str> = cluster.topics.iter().map(String::as_str).collect();
        let mut seen = HashSet::new();
        let unique: Vec<&str> = requested
            .iter()
            .map(String::as_str)
            .filter(|t| seen.insert(*t))
            .collect();
        put_i32(&mut o, unique.len() as i32);
        for t in unique {
            put_topic(&mut o, t, served.contains(t), node);
        }
    } else {
        put_i32(&mut o, cluster.topics.len() as i32);
        for t in &cluster.topics {
            put_topic(&mut o, t, true, node);
        }
    }
    o
}

/// Emit one Metadata v0 topic entry. A served topic gets `error=none` and its single
/// partition (led by `node`); an unserved-but-requested topic gets
/// `UNKNOWN_TOPIC_OR_PARTITION` and an empty partition array.
fn put_topic(o: &mut Vec<u8>, name: &str, served: bool, node: i32) {
    if !served {
        put_i16(o, UNKNOWN_TOPIC_OR_PARTITION);
        put_str(o, name);
        put_i32(o, 0); // no partitions
        return;
    }
    put_i16(o, NONE); // topic error = none
    put_str(o, name);
    // one partition (id 0), led by this broker, replicas=[node], isr=[node]
    put_i32(o, 1);
    put_i16(o, NONE); // partition error
    put_i32(o, 0); // partition_id
    put_i32(o, node); // leader
    put_i32(o, 1);
    put_i32(o, node); // replicas = [node]
    put_i32(o, 1);
    put_i32(o, node); // isr = [node]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cluster() -> ClusterMeta {
        ClusterMeta {
            broker: BrokerMeta {
                node_id: 0,
                host: "127.0.0.1".into(),
                port: 9092,
            },
            topics: vec!["astream".into()],
        }
    }

    /// A real ApiVersions v0 request, byte-for-byte per the Kafka protocol:
    /// api_key=18, api_version=0, correlation_id=7, client_id="kc" (no body).
    fn api_versions_request() -> Vec<u8> {
        let mut r = Vec::new();
        r.extend_from_slice(&18i16.to_be_bytes());
        r.extend_from_slice(&0i16.to_be_bytes());
        r.extend_from_slice(&7i32.to_be_bytes());
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc");
        r
    }

    #[test]
    fn answers_apiversions_v0_in_spec_format() {
        let resp = respond(&api_versions_request(), &cluster()).unwrap();
        // size:i32 | correlation_id:i32 | error:i16 | count:i32 | entries...
        let size = i32::from_be_bytes(resp[0..4].try_into().unwrap()) as usize;
        assert_eq!(size, resp.len() - 4, "size prefix counts the rest");
        assert_eq!(
            i32::from_be_bytes(resp[4..8].try_into().unwrap()),
            7,
            "correlation id echoed"
        );
        assert_eq!(
            i16::from_be_bytes(resp[8..10].try_into().unwrap()),
            0,
            "no error"
        );
        let count = i32::from_be_bytes(resp[10..14].try_into().unwrap());
        assert_eq!(count, SUPPORTED.len() as i32);
        // First advertised API is ApiVersions itself, capped at v0.
        assert_eq!(
            i16::from_be_bytes(resp[14..16].try_into().unwrap()),
            API_VERSIONS
        );
        assert_eq!(
            i16::from_be_bytes(resp[18..20].try_into().unwrap()),
            0,
            "max_version capped at 0"
        );
    }

    /// A real Metadata v0 request for all topics (topic array count = 0).
    fn metadata_request_all() -> Vec<u8> {
        let mut r = Vec::new();
        r.extend_from_slice(&3i16.to_be_bytes()); // api_key = Metadata
        r.extend_from_slice(&0i16.to_be_bytes()); // version 0
        r.extend_from_slice(&42i32.to_be_bytes()); // correlation id
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc"); // client_id
        r.extend_from_slice(&0i32.to_be_bytes()); // topics: 0 = all
        r
    }

    #[test]
    fn answers_metadata_v0_with_broker_and_topic() {
        let resp = respond(&metadata_request_all(), &cluster()).unwrap();
        assert_eq!(
            i32::from_be_bytes(resp[4..8].try_into().unwrap()),
            42,
            "correlation id echoed"
        );
        // Decode the body: brokers[1] then topics[].
        let mut c = Cur {
            b: &resp[8..],
            i: 0,
        };
        assert_eq!(c.i32().unwrap(), 1, "one broker advertised");
        assert_eq!(c.i32().unwrap(), 0, "node_id 0");
        assert_eq!(c.kstring().unwrap().unwrap(), "127.0.0.1", "broker host");
        assert_eq!(c.i32().unwrap(), 9092, "broker port");
        assert_eq!(c.i32().unwrap(), 1, "one topic");
        assert_eq!(c.i16().unwrap(), 0, "topic error none");
        assert_eq!(c.kstring().unwrap().unwrap(), "astream", "topic name");
        assert_eq!(c.i32().unwrap(), 1, "one partition");
        let _perr = c.i16().unwrap();
        assert_eq!(c.i32().unwrap(), 0, "partition 0");
        assert_eq!(c.i32().unwrap(), 0, "leader = this node");
    }

    #[test]
    fn unparseable_request_is_none_not_a_panic() {
        assert_eq!(respond(&[0, 1], &cluster()), None);
        assert_eq!(respond(&[], &cluster()), None);
    }

    /// An ApiVersions request at a FLEXIBLE version (v3) astream does not implement.
    fn api_versions_request_v3() -> Vec<u8> {
        let mut r = Vec::new();
        r.extend_from_slice(&18i16.to_be_bytes()); // api_key = ApiVersions
        r.extend_from_slice(&3i16.to_be_bytes()); // api_version = 3 (flexible)
        r.extend_from_slice(&9i32.to_be_bytes()); // correlation id
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc");
        r
    }

    #[test]
    fn apiversions_unsupported_version_returns_error_35_with_range() {
        // Per the Kafka bootstrap special case, an ApiVersions request above the
        // supported range gets a v0-framed body: error_code = UNSUPPORTED_VERSION(35)
        // PLUS the supported array, so the client downgrades — never error 0 with v0
        // bytes (which a flexible client misparses).
        let resp = respond(&api_versions_request_v3(), &cluster()).unwrap();
        assert_eq!(
            i32::from_be_bytes(resp[4..8].try_into().unwrap()),
            9,
            "correlation echoed"
        );
        assert_eq!(
            i16::from_be_bytes(resp[8..10].try_into().unwrap()),
            35,
            "UNSUPPORTED_VERSION, not 0"
        );
        let count = i32::from_be_bytes(resp[10..14].try_into().unwrap());
        assert_eq!(count, SUPPORTED.len() as i32, "range still advertised");
        assert_eq!(
            i16::from_be_bytes(resp[14..16].try_into().unwrap()),
            API_VERSIONS
        );
        assert_eq!(
            i16::from_be_bytes(resp[18..20].try_into().unwrap()),
            0,
            "max_version 0"
        );
    }

    /// A Metadata v0 request naming exactly one topic.
    fn metadata_request_for(name: &str) -> Vec<u8> {
        let mut r = Vec::new();
        r.extend_from_slice(&3i16.to_be_bytes());
        r.extend_from_slice(&0i16.to_be_bytes());
        r.extend_from_slice(&7i32.to_be_bytes());
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc");
        r.extend_from_slice(&1i32.to_be_bytes()); // one topic requested
        r.extend_from_slice(&(name.len() as i16).to_be_bytes());
        r.extend_from_slice(name.as_bytes());
        r
    }

    #[test]
    fn metadata_unknown_requested_topic_is_error_3_not_dropped() {
        let resp = respond(&metadata_request_for("nope"), &cluster()).unwrap();
        let mut c = Cur {
            b: &resp[8..],
            i: 0,
        };
        assert_eq!(c.i32().unwrap(), 1, "one broker");
        assert_eq!(c.i32().unwrap(), 0, "node_id");
        assert_eq!(c.kstring().unwrap().unwrap(), "127.0.0.1");
        assert_eq!(c.i32().unwrap(), 9092);
        assert_eq!(
            c.i32().unwrap(),
            1,
            "one topic returned, NOT silently dropped"
        );
        assert_eq!(c.i16().unwrap(), 3, "UNKNOWN_TOPIC_OR_PARTITION");
        assert_eq!(
            c.kstring().unwrap().unwrap(),
            "nope",
            "echoes requested name"
        );
        assert_eq!(c.i32().unwrap(), 0, "no partitions");
    }

    #[test]
    fn metadata_oversized_topic_count_terminates_on_short_body() {
        // Claim a million topics but supply exactly one, then EOF: the loop must stop
        // when the body is exhausted (count is attacker-controlled, never a bound).
        let mut r = Vec::new();
        r.extend_from_slice(&3i16.to_be_bytes());
        r.extend_from_slice(&0i16.to_be_bytes());
        r.extend_from_slice(&5i32.to_be_bytes());
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc");
        r.extend_from_slice(&1_000_000i32.to_be_bytes()); // claim 1,000,000 topics...
        r.extend_from_slice(&7i16.to_be_bytes());
        r.extend_from_slice(b"astream"); // ...but supply one, then the body ends
        let resp = respond(&r, &cluster()).unwrap(); // returns (does not spin)
        let mut c = Cur {
            b: &resp[8..],
            i: 0,
        };
        assert_eq!(c.i32().unwrap(), 1, "one broker");
        let _ = c.i32().unwrap();
        let _ = c.kstring().unwrap();
        let _ = c.i32().unwrap();
        assert_eq!(c.i32().unwrap(), 1, "the one supplied topic, not a million");
        assert_eq!(c.i16().unwrap(), 0, "served topic, error none");
        assert_eq!(c.kstring().unwrap().unwrap(), "astream");
    }

    #[test]
    fn a_request_naming_topics_is_never_widened_to_all_topics() {
        // Two topics claimed; one null entry, then the body ends: nothing readable
        // was named, but the client asked for specific topics, not for all of them.
        let mut r = Vec::new();
        r.extend_from_slice(&3i16.to_be_bytes());
        r.extend_from_slice(&0i16.to_be_bytes());
        r.extend_from_slice(&5i32.to_be_bytes());
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc");
        r.extend_from_slice(&2i32.to_be_bytes()); // two topics...
        r.extend_from_slice(&(-1i16).to_be_bytes()); // ...a null one, then EOF
        let resp = respond(&r, &cluster()).unwrap();
        let mut c = Cur {
            b: &resp[8..],
            i: 0,
        };
        assert_eq!(c.i32().unwrap(), 1, "one broker");
        let _ = c.i32().unwrap();
        let _ = c.kstring().unwrap();
        let _ = c.i32().unwrap();
        assert_eq!(c.i32().unwrap(), 0, "no topics, not every served topic");
        assert_eq!(c.i, resp.len() - 8, "nothing after the empty topic array");
    }

    #[test]
    fn metadata_duplicate_requested_topics_are_answered_once() {
        // A client may name the same topic many times; Kafka answers the SET of
        // requested topics. Echoing every repeat would let a request of tiny
        // repeated names amplify into a response many times its size.
        let mut r = Vec::new();
        r.extend_from_slice(&3i16.to_be_bytes());
        r.extend_from_slice(&0i16.to_be_bytes());
        r.extend_from_slice(&5i32.to_be_bytes());
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc");
        let names = ["astream", "nope", "astream", "nope", "astream"];
        r.extend_from_slice(&(names.len() as i32).to_be_bytes());
        for n in names {
            r.extend_from_slice(&(n.len() as i16).to_be_bytes());
            r.extend_from_slice(n.as_bytes());
        }
        let resp = respond(&r, &cluster()).unwrap();
        let mut c = Cur {
            b: &resp[8..],
            i: 0,
        };
        assert_eq!(c.i32().unwrap(), 1, "one broker");
        let _ = c.i32().unwrap();
        let _ = c.kstring().unwrap();
        let _ = c.i32().unwrap();
        assert_eq!(c.i32().unwrap(), 2, "each distinct topic answered once");
        assert_eq!(c.i16().unwrap(), 0, "served topic first, in request order");
        assert_eq!(c.kstring().unwrap().unwrap(), "astream");
        assert_eq!(c.i32().unwrap(), 1, "one partition");
        // error, id, leader, replicas[1], isr[1]
        let _ = c.i16();
        for _ in 0..6 {
            let _ = c.i32();
        }
        assert_eq!(c.i16().unwrap(), UNKNOWN_TOPIC_OR_PARTITION);
        assert_eq!(c.kstring().unwrap().unwrap(), "nope");
        assert_eq!(c.i32().unwrap(), 0, "no partitions");
        assert_eq!(c.i, resp.len() - 8, "nothing after the two topics");
    }

    #[test]
    fn a_response_too_large_for_the_i32_size_prefix_is_refused() {
        // The size prefix is an i32; a length that does not fit must not wrap
        // into a negative or short size that desyncs the client's framing.
        let max = i32::MAX as usize;
        assert_eq!(frame_size(0), Some(4));
        assert_eq!(frame_size(max - 4), Some(i32::MAX));
        assert_eq!(frame_size(max - 3), None);
        assert_eq!(frame_size(usize::MAX), None);
    }
}
