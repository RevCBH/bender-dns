# bender-dns

A DNS client library for [Bend 2](https://bend-lang.com/) (compiler 2.0.32),
with two resolvers behind one API:

- **Native stack** (`Dns.resolve`, `Dns.lookup_ipv4`, `Dns.lookup_ipv6`): a stub
  resolver written in Bend. Messages are encoded and decoded by pure code whose
  behavior is stated as laws in `LAWS.bend` and proven in `proofs/`; queries go to
  the configured recursive resolvers over TCP (RFC 7766) with Base's byte-exact
  TCP effects. No foreign code.
- **OS delegation** (`Dns.os_lookup`): the platform resolver through
  `getaddrinfo`, a foreign effect with C and JS twins. It honours nsswitch,
  `/etc/hosts`, mDNS and VPN split DNS, and is unproven ("unsafe" in Bend's
  sense).

Why TCP: Base 2.0.32's UDP effects carry text (UTF-8), so a DNS datagram with any
byte above 0x7F cannot cross them intact. TCP is a standard DNS transport that
every recursive resolver serves, including systemd-resolved's 127.0.0.53 stub.

## Use

Consumers import only `main.bend`; every public def is a `Dns.*` wrapper (see its
comments for the whole API).

```
import <this package>/main.bend as D

def main() -> IO(Unit):
  do IO<Unit>:
    cfg : Result<&2, &2, D.Dns.Error(), D.Dns.Config()> <- D.Dns.system()
    ...   # D.Dns.lookup_ipv4(cfg, "example.com"), D.Dns.resolve(cfg, "gmail.com", D.Dns.MX())
```

Examples, from this directory:

```bash
bend examples/dig.bend -- example.com AAAA
bend examples/dig.bend -- @8.8.8.8 gmail.com MX
bend examples/dig.bend -- --os example.com      # through getaddrinfo
bend examples/host.bend -- www.github.com
```

The API, in groups (all `Dns.*`):

| Group | Defs |
|---|---|
| Resolving | `system`, `load`, `config`, `default_config`, `with_servers`, `with_port`, `with_timeout`, `with_attempts`, `with_search`, `with_ndots`, `with_hosts`, `candidates`, `resolve`, `lookup_ipv4`, `lookup_ipv6`, `os_lookup`, `Resolved.name` / `records` |
| Names and addresses | `Name.parse` / `show` / `fqdn` / `eq` / `lower` / `ok` / `wire`, `Ip.show4` / `parse4` / `show6` / `parse6` / `is_ipv4` / `is_ipv6` |
| Types | `A`, `NS`, `CNAME`, `SOA`, `PTR`, `MX`, `TXT`, `AAAA`, `SRV`, `OPT`, `ANY`, `RType.of_code` / `code` / `show` / `parse` / `eq`, `IN`, `RClass.of_code` / `code` |
| Records | `record`, `Record.name` / `rtype` / `rclass` / `ttl` / `data` / `show`, `RData.kind` / `show` / `address` / `name` / `preference` / `strings` / `groups` / `bytes` / `port` / `serial`, builders `ipv4`, `ipv6`, `name_data`, `mx`, `txt`, `soa`, `srv`, `raw` |
| Messages | `question`, `header`, `message`, their accessors, `rcode_name`, `encode`, `encode_ok`, `decode`, `query`, `query_plain`, `accept`, `answer`, `frame`, `unframe`, `exchange` |
| Errors | `Error.kind` (tags `BadName`, `NxDomain`, `NoData`, `ServFail`, `Malformed`, `Mismatch`, `NoServers`, `Connect`, `Io`, `Timeout`, `Os`, `Config`), `Error.show` / `code` / `rcode` / `name`, `NameError.show`, `DecodeError.show` |

The native resolver follows resolv.conf(5): up to three IPv4 nameservers,
`search`/`domain`, `ndots`, `timeout`, `attempts`; `/etc/hosts` first; IP literals
answer themselves; a fresh random id per query; a response is accepted only if
it has the query's id and exactly its question; NXDOMAIN moves to the next
search candidate, SERVFAIL/REFUSED/timeouts/malformed responses to the next
server; CNAME chains are followed within the answer and re-queried when they
leave it (at most 8 times).

## Laws

`LAWS.bend` states 18 laws about the pure core, among them:

- `message_roundtrip`: every valid message decodes back to itself;
- the wire integers, names (text and comparison), IPv4 text and TCP framing
  round-trip, and the frame reader does not care how the stream is split;
- an accepted response carries the query's id, the QR bit and exactly its
  question; an absolute name is tried alone; a compression pointer loop is refused.

The gate:

    bend PROOF.bend             # ALL PROOFS CHECK
    bend PROOF.bend --verdict   # the same, rechecked by the BendTT kernel (needs Lean 4.34.0)

`scripts/ci.sh` runs it with every check and test; CI runs that on every push
(`.github/workflows/ci.yml`, GitHub-hosted, installing the pinned toolchain with
`scripts/ci-setup.sh`).

## Limitations

- **Stub only**: no recursion from the root, no cache, no DNSSEC validation (the
  AD bit is reported, not trusted), no DNS over TLS/HTTPS, no mDNS in the native
  stack (use `os_lookup`).
- **IPv4 nameservers only** (Base's `TCP.connect` reaches IPv4 only); IPv6
  addresses are fully supported as data. No UDP (see above), so the TC bit is
  reported but needs no fallback.
- **Timeouts** cannot cancel a stalled connect or read (Base has no cancellation):
  the resolver moves on at once, but the stalled step keeps the program alive
  until the peer acts; the examples exit explicitly.
- **JS lane**: `os_lookup` blocks the event loop; the JS lane is several times
  slower than the native one.
- Built and tested on Linux x86_64 with Bend 2.0.32. The C side of the foreign
  effect (`src/os.c`) uses Bend runtime internals with no ABI promise: rebuild and
  rerun the tests after any compiler update.

## Tests

`tests/*_test.bend` are checker-evaluated, `tests/*_run.bend` print PASS/FAIL on
both lanes (`bend f.bend` is the JS lane, `bend f.bend -o f && ./f` the native C
lane), and `tests/resolver_live.sh` runs a local DNS server plus real lookups
against 127.0.0.53, 8.8.8.8 and 1.1.1.1.

## License

MIT; see `LICENSE`.
