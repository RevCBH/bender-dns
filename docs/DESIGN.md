# bender-dns: design

A DNS client library for Bend 2 (compiler 2.0.32; never run `bend update`) with two
resolvers behind one API:

- **OS delegation** (`Os.lookup`): the platform resolver through `getaddrinfo`, a
  foreign effect (C and JS twins). Fast, honours nsswitch, `/etc/hosts`, mDNS,
  VPN split DNS; unproven ("unsafe" in Bend's sense: foreign code).
- **Native stack**: a DNS stub resolver written in Bend. RFC 1035 messages are
  encoded and decoded by pure, proven code; queries go to the configured
  nameservers over **TCP** (RFC 7766) using Base's byte-exact
  `TCP.send_bytes` / `TCP.recv_bytes`. No foreign code at all.

Why TCP, not UDP: Base 2.0.32's `UDP.send_to` / `UDP.recv_from` carry `String`
(UTF-8 text), so a DNS datagram with any byte above 0x7F cannot cross them
intact. TCP is a standard DNS transport that every recursive resolver serves
(RFC 7766 §5), including systemd-resolved's 127.0.0.53 stub.

## Non-goals

No server, no recursive resolution from the root (the native stack is a stub:
it asks recursive resolvers with RD=1), no DNSSEC validation (the AD bit is
reported, not trusted), no DNS-over-TLS/HTTPS, no caching, no mDNS/LLMNR, no
dynamic update, no zone transfers. IPv6 addresses are parsed, printed and
returned as data, but Base's `TCP.connect` reaches IPv4 nameservers only.

## Layout

| File | Alias | What |
|---|---|---|
| `main.bend` | (consumers) | the publish entry: `Dns.*` wrappers only |
| `src/bytes.bend` | `B` | bytes, the byte `Class` (from bender-http, unchanged) |
| `src/num.bend` | `N` | decimal/hex show/read on Nat (from bender-http, unchanged) |
| `src/types.bend` | `M` | RType, RClass, Name, Question, RData, Record, Header, Message, errors |
| `src/wire.bend` | `W` | big-endian u8/u16/u32 put/get on byte lists |
| `src/name.bend` | `NM` | domain names: text <-> labels, validity, case-insensitive equality, wire encode |
| `src/ip.bend` | `IP` | IPv4 / IPv6 text show/parse |
| `src/encode.bend` | `E` | message encoding (no compression) and query building |
| `src/decode.bend` | `D` | message decoding (with compression pointers, loop-safe) |
| `src/frame.bend` | `F` | the TCP length prefix (RFC 1035 §4.2.2) and an incremental frame reader |
| `src/conf.bend` | `CF` | `/etc/resolv.conf` and `/etc/hosts` parsers; search-list candidates |
| `src/answer.bend` | `A` | response validation and answer extraction (CNAME chains) |
| `src/os.bend` + `.c/.js` | | `Os.lookup`: getaddrinfo (foreign) |
| `src/transport.bend` | `X` | IO: one query over TCP to one nameserver, with a timeout |
| `src/resolver.bend` | `R` | IO: config, search list, servers and retries, CNAME re-queries |
| `LAWS.bend` / `PROOF.bend` / `proofs/*.bend` | | laws; proofs |
| `tests/`, `examples/` | | tests; `examples/dig.bend`, `examples/host.bend` |

**The proof boundary.** `LAWS.bend` imports only pure modules (bytes, num,
types, wire, name, ip, encode, decode, frame, conf, answer). Never os,
transport, resolver or main.

## Bend rules that bite (all verified on 2.0.32 in bender-http)

- A def may call only defs written above it. Order helpers first.
- An importer sees `Alias.name`, `Alias.Type`, `Alias.Ctor{..}`; patterns use the
  qualified constructor. Imports are not re-exported (main.bend wraps everything).
- `match` only on a parameter or a pattern-bound variable; pass computed values to a helper.
- Recursion must be structural (the first changing argument shrinks by a pattern
  match). Otherwise count down a Nat fuel. No mutual recursion; no `@unsafe`.
- Affine variables: `+x` to reuse Data; closures are affine.
- Nat is a native immediate at runtime (O(1) up to 2^48-1; past that the program
  aborts): never multiply a Nat parsed from the network without a bound. The
  checker evaluates Nat in unary: proofs and checker tests must not compute with
  large literals (a closed fact about 4294967295 is out of reach).
- Constructor names are global within a module: no two types in one module
  share a constructor name, and avoid Base's (`Some`, `None`, `Done`, `Fail`,
  `Close`, ...).
- Evaluation is strict: `Bool.pick` evaluates both branches.
- **JS lane stack**: recursion that is not a tail call overflows near 20-40k
  frames. Anything walking caller- or network-sized data (messages up to 65535
  bytes, record lists) at runtime must be a loop. Follow bender-http's
  convention: the runtime def is the loop; its plain structural recursion stays
  beside it as `<name>.spec`; the file header states the equation linking them;
  laws are stated on the public def and proofs go through the equation.

## Proof-friendly rules (mandatory)

1. Classify bytes and chars only through `B.class` / `B.char_class` (or a module
   classifier built from it, like bender-http's url `uclass`).
2. Numbers are Nat. Text numbers go through `N.show` / `N.read`.
3. Wire integers go through `W` only. `W.put_u16(n) = [n / 256, n % 256]`
   style definitions need div/mod lemmas; prefer definitions that make
   `get_u16(put_u16(n) ++ rest) == Some{(n, rest)}` easy (e.g. via Nat.divmod
   with a stated lemma), and keep the bound `n <= 65535` explicit.
4. Decoders that consume a prefix return the rest: `Maybe<&2, Pair-like-type>`
   with a named Data type (`Got{value, rest}`), never Base's `&` pairs (Type kind).
5. Keep every pure def total and small; a law will be proven about it.

## Interfaces

### types.bend (M)

    type RType is Data: TA{} TNS{} TCNAME{} TSOA{} TPTR{} TMX{} TTXT{} TAAAA{} TSRV{} TOPT{} TANY{} TOther{code: Nat}
    type RClass is Data: CIN{} COther{code: Nat}
    # A domain name: its labels, each a byte list (case kept), root = [].
    type Question is Data: Question{name: List<&2, List<&2, U32>>, qtype: RType, qclass: RClass}
    type RData is Data:
      RIpv4{a: Nat, b: Nat, c: Nat, d: Nat}
      RIpv6{groups: List<&2, Nat>}                       # 8 groups of 16 bits
      RName{name: List<&2, List<&2, U32>>}               # NS, CNAME, PTR
      RMx{preference: Nat, exchange: List<&2, List<&2, U32>>}
      RTxt{strings: List<&2, List<&2, U32>>}
      RSoa{mname, rname: names; serial, refresh, retry, expire, minimum: Nat}
      RSrv{priority: Nat, weight: Nat, port: Nat, target: List<&2, List<&2, U32>>}
      RRaw{bytes: List<&2, U32>}                         # any other type, and OPT
    type Record is Data: Record{name, rtype: RType, rclass: RClass, ttl: Nat, data: RData}
    type Header is Data: Header{id: Nat, qr: Bool, opcode: Nat, aa: Bool, tc: Bool, rd: Bool,
      ra: Bool, ad: Bool, cd: Bool, rcode: Nat}
    type Message is Data: Message{header: Header, questions: List<&2, Question>,
      answers: List<&2, Record>, authority: List<&2, Record>, additional: List<&2, Record>}

`src/types.bend` is the source of truth (it is written and checked).

### wire.bend (W)

- `put_u8 / put_u16 / put_u32(n: Nat) -> List<&2, U32>`; `get_u8 / get_u16 / get_u32(xs) ->
  Maybe<&2, M.Got>` where `Got{value: Nat, rest: List<&2, U32>}` (in types.bend).
- Laws: `n <= 65535 ⇒ get_u16(put_u16(n) ++ rest) == Some{Got{n, rest}}`; same for u8 (255) and
  u32 (4294967295 stays symbolic: state as `n < 65536 * 65536` via two u16s if that is easier).

### name.bend (NM)

- `from_text(s: String) -> Result<&2, &2, M.NameError, Name>`: dotted text, a trailing dot
  allowed (absolute), escapes `\.` and `\DDD` (RFC 1035 §5.1); refuses empty labels, labels over 63
  bytes, names over 255 wire bytes.
- `to_text(n) -> String` (the inverse for names from_text accepts: law).
- `ok(n) -> Bool`: every label 1..63 bytes of byte values, wire length <= 255.
- `wire(n) -> List<&2, U32>`: length-prefixed labels, then 0. `eq(a, b) -> Bool`: ASCII
  case-insensitive. `lower(n)`.
- Laws: `ok(n) ⇒ D.name_at(...) of wire(n) ++ rest` reads n back; `eq` is reflexive and
  symmetric; `from_text(to_text(n)) == Done{n}` for `ok(n)` names whose labels hold no byte that
  to_text must escape, or with escapes if achievable.

### ip.bend (IP)

- `show4(a, b, c, d) -> String`, `parse4(s) -> Maybe<&2, M.RData>` (canonical dotted quad, no
  leading zeros); `show6(groups) -> String` (RFC 5952: lowercase, longest zero run as `::`),
  `parse6(s) -> Maybe<&2, M.RData>`.
- Laws: parse4(show4(..)) roundtrip for octets <= 255; parse6(show6(g)) for 8 groups <= 65535
  if provable, else concrete cases.

### encode.bend (E), decode.bend (D)

- `E.message(m) -> List<&2, U32>`: header (12 bytes), then questions and records, names
  uncompressed. RDATA by type; RDLENGTH computed. `E.message_ok(m) -> Bool`: every name ok, every
  number in range, counts <= 65535, TXT strings <= 255 bytes each, total <= 65535 bytes.
- `E.query(id: Nat, name, qtype) -> List<&2, U32>`: RD=1, one question, class IN, and an EDNS0
  OPT record advertising 4096 bytes (optional; state it).
- `D.message(xs) -> Result<&2, &2, M.DecodeError, M.Message>`: the whole message (random access
  for compression pointers: a pointer must point strictly backwards, and the total number of
  pointer hops is bounded by the message length, so loops fail with BadPointer); trailing bytes
  are an error; unknown types become RRaw. Bound everything by the message length.
- Laws: `E.message_ok(m) ⇒ D.message(E.message(m)) == Done{m}` (the central law); concrete laws
  for a compressed real-world response decoding to the expected records, and for a pointer loop
  failing.

### frame.bend (F)

- `frame(xs) -> List<&2, U32>` = u16 length ++ xs. A reader state machine like bender-http's
  decoder: `init(max)`, `step(s, b)`, `feed(s, xs)` (structural), `done(s)`, `finish(s) ->
  Result<.., M.Got-like{message bytes, rest}>`.
- Laws: `feed_split`; `len(xs) <= 65535 ⇒ finish(feed(init(m), frame(xs) ++ rest)) == Done{(xs, rest)}`
  for a budget m covering it.

### conf.bend (CF)

- `resolv(text: String) -> M.Conf` where `Conf{nameservers: List<&2, String>, search:
  List<&2, String>, ndots: Nat, timeout_s: Nat, attempts: Nat}` (resolv.conf(5); defaults ndots 1,
  timeout 5, attempts 2; nameservers that are not IPv4 text are skipped; `domain` acts as a
  one-entry search list; later lines win per resolv.conf(5)).
- `hosts(text: String) -> List<&2, M.HostEntry>` (`HostEntry{address: String, names: List<&2, String>}`,
  comments and blank lines skipped); `hosts_lookup(entries, name) -> List<&2, String>` (case-insensitive).
- `candidates(conf, name: String) -> List<&2, String>`: the search-list expansion of resolv.conf(5):
  an absolute name (trailing dot) is tried alone; a name with at least ndots dots is tried as is
  first, then with each search suffix; otherwise the suffixes first, then as is.
- Laws: concrete parser cases; `candidates` of an absolute name is exactly `[name]`.

### answer.bend (A)

- `accept(query_id, question, response: M.Message) -> Bool`: QR=1, opcode 0, the same id, exactly
  the same question (name compared case-insensitively). `rcode(m)`, `truncated(m)`.
- `addresses(question_name, rtype, response) -> M.Answer` where `Answer` is `Found{name, records}`
  (the records of rtype at the end of the CNAME chain starting at question_name, the chain followed
  within the answer section, at most 16 hops), `Alias{target}` (the chain leaves the answer section:
  the resolver re-queries target), or `Nothing{}`.
- Laws: accept implies the ids and questions match; addresses only returns records whose owner is
  reached from the question name by the answer's CNAMEs.

### os.bend (foreign)

`Os.lookup(host: String, family: U32) -> IO(Result<&1, &1, U32 & String, List<&2, String>>)`:
getaddrinfo with AF_UNSPEC (0), AF_INET (4) or AF_INET6 (6); distinct addresses as text, in the
resolver's order, at most 32. bender-http's `src/dns.c`/`dns.js` are the starting point (they do
IPv4 only, refuse numeric non-canonical hosts, report EAI codes as errno values).

### transport.bend (X), resolver.bend (R)

- `X.query(server: String, port: Nat, query: List<&2, U32>, max: Nat, timeout_ms: Nat) ->
  IO(Result<&2, &2, M.Error, List<&2, U32>>)`: TCP connect, send `F.frame(query)`, read with the
  frame reader (recv_bytes, 65536-byte reads, each bounded by a timeout race like bender-http's
  `X.within`, which stops its timer once the race is decided), close. Base cannot cancel a stalled
  read: document it as bender-http does.
- `R.Config` (`Config{conf: M.Conf, hosts: List<&2, M.HostEntry>, port: Nat, timeout_ms: Nat}`),
  `R.system() -> IO(Result<.., Config>)` (reads `/etc/resolv.conf` and `/etc/hosts` with File.read;
  a missing resolv.conf means nameserver 127.0.0.1), `R.with_servers(cfg, list)`.
- `R.resolve(cfg, name: String, rtype) -> IO(Result<&2, &2, M.Error, M.Resolved>)`: IPv4/IPv6 literal
  → itself (for A/AAAA); hosts file (A/AAAA); for each search candidate, for each attempt, for each
  nameserver: query with a fresh random id (`IO.random_u32`), validate with `A.accept`, NXDOMAIN →
  next candidate, SERVFAIL/REFUSED/timeouts → next server, follow `Alias` by re-querying (at most 8
  times). `Resolved{name, records}`.
- `R.lookup_ipv4(cfg, name) -> IO(Result<.., List<&2, String>>)` and `lookup_ipv6`.

### main.bend

`Dns.*` wrappers only: type aliases, record and message accessors, `Dns.Name.parse/show`,
`Dns.Ip.*`, `Dns.encode`, `Dns.decode`, `Dns.query`, `Dns.system`, `Dns.with_servers`,
`Dns.with_timeout`, `Dns.resolve`, `Dns.lookup_ipv4`, `Dns.lookup_ipv6`, `Dns.os_lookup`,
`Dns.Error.show`, `Dns.Error.kind` (a tag type consumers can match).

## Running things

Every check, build and test runs on rust-build-box, never locally: `bend-box <bend args>` or
`bend-box --sh '<shell command>'` (from the project directory; it mirrors tracked and unignored
files; `--include .scratch` adds the git-ignored `.scratch/`). Build outputs go to `"$BEND_OUT"`.
`scripts/ci.sh` is the full gate; CI runs it on pushes to main.
