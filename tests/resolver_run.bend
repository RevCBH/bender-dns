import Base
import ../src/types.bend as M
import ../src/name.bend as NM
import ../src/encode.bend as E
import ../src/conf.bend as CF
import ../src/resolver.bend as R

# The resolver's pure parts on both lanes, and the IO paths that need no
# network: how one response is judged (classify), the policy after each
# candidate (after / finish), the tries, config builders and readers, the
# search candidates, literals and the hosts table, type names, record
# presentation, error texts; then resolve / lookup / load on literals,
# hosts entries, an empty server list and missing files.
#   bend tests/resolver_run.bend
#   bend tests/resolver_run.bend -o "$BEND_OUT/resolver_run" && "$BEND_OUT/resolver_run"
# Prints PASS / FAIL per case, then "ALL PASS" or "SOME FAIL: n".

# Fixtures
# --------

def name(s: String) -> M.Name():
  R.owner(NM.from_text(s))

def q(s: String, t: M.RType) -> M.Question:
  M.Question{name(s), t, M.CIN{}}

def hdr(id: Nat, qr: Bool, rcode: Nat) -> M.Header:
  M.Header{id, qr, 0n, False{}, False{}, True{}, True{}, False{}, False{}, rcode}

def a_rec(owner: String, a: Nat, b: Nat, c: Nat, d: Nat) -> M.Record:
  M.Record{name(owner), M.TA{}, M.CIN{}, 300n, M.RIpv4{a, b, c, d}}

def cname_rec(owner: String, target: String) -> M.Record:
  M.Record{name(owner), M.TCNAME{}, M.CIN{}, 300n, M.RName{name(target)}}

def response(id: Nat, qr: Bool, rcode: Nat, qs: List<&2, M.Question>, an: List<&2, M.Record>) -> List<&2, U32>:
  E.message(M.Message{hdr(id, qr, rcode), qs, an, Nil{}, Nil{}})

def wire(xs: List<&2, U32>) -> Result<&2, &2, M.Error, List<&2, U32>>:
  Done{xs}

# Showing results
# ---------------

def texts.go(rs: List<&2, M.Record>, acc: List<&2, String>) -> List<&2, String>:
  match rs:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{r, t}:
      match r:
        case M.Record{n, ty, c, ttl, d}:
          texts.go(t, R.rdata_text(d) <> acc)

def records_text(rs: List<&2, M.Record>) -> String:
  String.join(texts.go(rs, Nil{}), ",")

def outcome_text(o: R.Outcome) -> String:
  match o:
    case R.OFound{n, rs}:
      "found " ++ R.fqdn(n) ++ " " ++ records_text(rs)
    case R.OAlias{t}:
      "alias " ++ R.fqdn(t)
    case R.ONoData{}:
      "nodata"
    case R.ONxDomain{}:
      "nxdomain"
    case R.OFailed{e}:
      "failed: " ++ R.error_show(e)

def resolved_text(r: Result<&2, &2, M.Error, M.Resolved>) -> String:
  match r:
    case Done{x}:
      match x:
        case M.Resolved{n, rs}:
          "found " ++ R.fqdn(n) ++ " " ++ records_text(rs)
    case Fail{e}:
      "error: " ++ R.error_show(e)

def opt_text(m: Maybe<&2, String>) -> String:
  match m:
    case Some{s}:
      s
    case None{}:
      "-"

def opt_error(m: Maybe<&2, M.Error>) -> String:
  match m:
    case Some{e}:
      R.error_show(e)
    case None{}:
      "-"

def next_text(n: R.Next) -> String:
  match n:
    case R.NStop{r}:
      "stop " ++ resolved_text(r)
    case R.NGo{s}:
      match s:
        case R.Seen{nd, f}:
          "go nodata=" ++ opt_text(nd) ++ " failed=" ++ opt_error(f)

def lit_text(m: Maybe<&2, Result<&2, &2, M.Error, M.Resolved>>) -> String:
  match m:
    case Some{r}:
      resolved_text(r)
    case None{}:
      "none"

def type_text(m: Maybe<&2, M.RType>) -> String:
  match m:
    case Some{t}:
      R.type_name(t)
    case None{}:
      "none"

def addrs_text(r: Result<&2, &2, M.Error, List<&2, String>>) -> String:
  match r:
    case Done{xs}:
      String.join(xs, ",")
    case Fail{e}:
      "error: " ++ R.error_show(e)

def cfg_text(c: R.Config) -> String:
  +cfg = c
  "servers " ++ String.join(R.servers(cfg), ",") ++ " search " ++ String.join(R.search(cfg), ",")
    ++ " ndots " ++ Nat.show(R.ndots(cfg)) ++ " attempts " ++ Nat.show(R.attempts(cfg))
    ++ " port " ++ Nat.show(R.port(cfg)) ++ " timeout " ++ Nat.show(R.timeout_ms(cfg))

def loaded_text(r: Result<&2, &2, M.Error, R.Config>) -> String:
  match r:
    case Done{c}:
      cfg_text(c)
    case Fail{e}:
      "error: " ++ R.error_show(e)

# The cases
# ---------

type Case is Data:
  Case{label: String, got: String, want: String}

def verdict(ok: Bool, label: String, got: String, want: String, fails: Nat) -> IO(Nat):
  match ok:
    case True{}:
      do IO<Nat>:
        IO.print("PASS " ++ label ++ ": " ++ got)
        return fails
    case False{}:
      do IO<Nat>:
        IO.print("FAIL " ++ label ++ ": got " ++ got ++ ", want " ++ want)
        return 1n+fails

def check(c: Case, fails: Nat) -> IO(Nat):
  match c:
    case Case{label, +got, +want}:
      verdict(String.eq(got, want), label, got, want, fails)

def checks(cs: List<&2, Case>, fails: Nat) -> IO(Nat):
  match cs:
    case Nil{}:
      IO.pure(Nat, fails)
    case Con{c, t}:
      IO.bind(Nat, Nat, check(c, fails), f => checks(t, f))

def ex() -> M.Question:
  q("example.com", M.TA{})

def classify(id: Nat, xs: List<&2, U32>) -> String:
  outcome_text(R.classify(id, ex(), wire(xs)))

def classify_cases() -> List<&2, Case>:
  [Case{"NOERROR with an A record", classify(7n, response(7n, True{}, 0n, [ex()], [a_rec("example.com", 1n, 2n, 3n, 4n)])),
     "found example.com. 1.2.3.4"},
   Case{"question name case-insensitive", classify(7n, response(7n, True{}, 0n, [q("EXAMPLE.Com", M.TA{})],
     [a_rec("example.COM", 1n, 2n, 3n, 4n)])), "found example.com. 1.2.3.4"},
   Case{"CNAME chain inside the answer", classify(9n, response(9n, True{}, 0n, [ex()],
     [cname_rec("example.com", "b.example"), a_rec("b.example", 5n, 6n, 7n, 8n)])), "found b.example. 5.6.7.8"},
   Case{"CNAME leaving the answer: re-query", classify(9n, response(9n, True{}, 0n, [ex()],
     [cname_rec("example.com", "elsewhere.net")])), "alias elsewhere.net."},
   Case{"NOERROR, no answer: NODATA", classify(1n, response(1n, True{}, 0n, [ex()], Nil{})), "nodata"},
   Case{"other-name answers only: NODATA", classify(1n, response(1n, True{}, 0n, [ex()],
     [a_rec("other.com", 1n, 1n, 1n, 1n)])), "nodata"},
   Case{"NXDOMAIN", classify(2n, response(2n, True{}, 3n, [ex()], Nil{})), "nxdomain"},
   Case{"NXDOMAIN with a CNAME (RFC 6604)", classify(2n, response(2n, True{}, 3n, [ex()],
     [cname_rec("example.com", "gone.example")])), "nxdomain"},
   Case{"SERVFAIL", classify(3n, response(3n, True{}, 2n, [ex()], Nil{})), "failed: server failure (SERVFAIL)"},
   Case{"REFUSED", classify(3n, response(3n, True{}, 5n, [ex()], Nil{})), "failed: server failure (REFUSED)"},
   Case{"FORMERR", classify(3n, response(3n, True{}, 1n, [ex()], Nil{})), "failed: server failure (FORMERR)"},
   Case{"rcode 9", classify(3n, response(3n, True{}, 9n, [ex()], Nil{})), "failed: server failure (RCODE9)"},
   Case{"another id", classify(4n, response(5n, True{}, 0n, [ex()], [a_rec("example.com", 1n, 2n, 3n, 4n)])),
     "failed: a response did not match the query"},
   Case{"another question", classify(4n, response(4n, True{}, 0n, [q("example.org", M.TA{})], Nil{})),
     "failed: a response did not match the query"},
   Case{"another type", classify(4n, response(4n, True{}, 0n, [q("example.com", M.TAAAA{})], Nil{})),
     "failed: a response did not match the query"},
   Case{"no question", classify(4n, response(4n, True{}, 0n, Nil{}, Nil{})), "failed: a response did not match the query"},
   Case{"QR = 0 (a query, not a response)", classify(4n, response(4n, False{}, 0n, [ex()], Nil{})),
     "failed: a response did not match the query"},
   Case{"garbage", classify(4n, [1, 2, 3]), "failed: malformed response: the message ended early"},
   Case{"empty message", classify(4n, Nil{}), "failed: malformed response: the message ended early"},
   Case{"trailing bytes", classify(1n, List.append(&2, U32, response(1n, True{}, 0n, [ex()], Nil{}), [0])),
     "failed: malformed response: bytes after the message"},
   Case{"transport error passes through", outcome_text(R.classify(1n, ex(), Fail{M.Timeout{}})), "failed: timed out"}]

def policy_cases() -> List<&2, Case>:
  [Case{"found stops", next_text(R.after(R.OFound{name("a.b"), [a_rec("a.b", 1n, 1n, 1n, 1n)]}, "a.b", R.seen0())),
     "stop found a.b. 1.1.1.1"},
   Case{"NXDOMAIN goes on", next_text(R.after(R.ONxDomain{}, "a.b", R.seen0())), "go nodata=- failed=-"},
   Case{"NODATA noted, goes on", next_text(R.after(R.ONoData{}, "a.b", R.seen0())), "go nodata=a.b failed=-"},
   Case{"the first NODATA kept", next_text(R.after(R.ONoData{}, "c.d", R.Seen{Some{"a.b"}, None{}})),
     "go nodata=a.b failed=-"},
   Case{"SERVFAIL noted, goes on", next_text(R.after(R.OFailed{M.ServFail{2n}}, "a.b", R.seen0())),
     "go nodata=- failed=server failure (SERVFAIL)"},
   Case{"timeout stops", next_text(R.after(R.OFailed{M.Timeout{}}, "a.b", R.seen0())), "stop error: timed out"},
   Case{"connect error stops", next_text(R.after(R.OFailed{M.Connect{111, "refused"}}, "a.b", R.seen0())),
     "stop error: connect error 111: refused"},
   Case{"mismatch stops", next_text(R.after(R.OFailed{M.Mismatch{}}, "a.b", R.seen0())),
     "stop error: a response did not match the query"},
   Case{"no servers stops", next_text(R.after(R.OFailed{M.NoServers{}}, "a.b", R.seen0())), "stop error: no nameservers"},
   Case{"an alias left over is too long", next_text(R.after(R.OAlias{name("x.y")}, "a.b", R.seen0())),
     "stop error: server failure (SERVFAIL)"},
   Case{"finish: nothing seen is NXDOMAIN", resolved_text(R.finish("www", R.seen0())),
     "error: www: no such name (NXDOMAIN)"},
   Case{"finish: NODATA beats SERVFAIL", resolved_text(R.finish("www", R.Seen{Some{"www.corp"}, Some{M.ServFail{2n}}})),
     "error: www.corp: no record of that type"},
   Case{"finish: SERVFAIL beats NXDOMAIN", resolved_text(R.finish("www", R.Seen{None{}, Some{M.ServFail{5n}}})),
     "error: server failure (REFUSED)"}]

def cfg1() -> R.Config:
  R.from_text("nameserver 10.0.0.1\nnameserver 10.0.0.2\noptions timeout:3 attempts:3 ndots:2\nsearch corp.example lab.example\n",
    "10.9.8.7 myhost alias\n::5 myhost\n192.168.1.1 router # comment\n")

def config_cases() -> List<&2, Case>:
  [Case{"from_text", cfg_text(cfg1()),
     "servers 10.0.0.1,10.0.0.2 search corp.example,lab.example ndots 2 attempts 3 port 53 timeout 3000"},
   Case{"empty resolv.conf: 127.0.0.1 and the defaults", cfg_text(R.from_text("", "")),
     "servers 127.0.0.1 search  ndots 1 attempts 2 port 53 timeout 5000"},
   Case{"only IPv6 nameservers: 127.0.0.1", cfg_text(R.from_text("nameserver ::1\n", "")),
     "servers 127.0.0.1 search  ndots 1 attempts 2 port 53 timeout 5000"},
   Case{"default_config", cfg_text(R.default_config()),
     "servers 127.0.0.1 search  ndots 1 attempts 2 port 53 timeout 5000"},
   Case{"builders", cfg_text(R.with_ndots(R.with_search(R.with_attempts(R.with_timeout(R.with_port(
     R.with_servers(cfg1(), ["1.1.1.1"]), 5353n), 250n), 4n), ["x.test"]), 0n)),
     "servers 1.1.1.1 search x.test ndots 0 attempts 4 port 5353 timeout 250"},
   Case{"with_attempts 0 is 1", Nat.show(R.attempts(R.with_attempts(cfg1(), 0n))), "1"},
   Case{"tries: servers x attempts", String.join(R.tries(R.with_attempts(cfg1(), 2n)), ","),
     "10.0.0.1,10.0.0.2,10.0.0.1,10.0.0.2"},
   Case{"tries: one attempt", String.join(R.tries(R.with_attempts(cfg1(), 1n)), ","), "10.0.0.1,10.0.0.2"},
   Case{"tries: no servers", String.join(R.tries(R.with_servers(cfg1(), Nil{})), ","), ""},
   Case{"candidates: few dots, suffixes first", String.join(R.candidates(cfg1(), "www"), ","),
     "www.corp.example,www.lab.example,www"},
   Case{"candidates: ndots reached, as is first", String.join(R.candidates(cfg1(), "a.b.c"), ","),
     "a.b.c,a.b.c.corp.example,a.b.c.lab.example"},
   Case{"candidates: absolute alone", String.join(R.candidates(cfg1(), "www."), ","), "www."},
   Case{"hosts table read", Nat.show(List.length(&2, M.HostEntry, R.hosts(cfg1()))), "3"}]

def lit_cases() -> List<&2, Case>:
  [Case{"literal IPv4 for A", lit_text(R.literal("192.0.2.1", M.TA{})), "found 192.0.2.1. 192.0.2.1"},
   Case{"literal IPv6 for AAAA", lit_text(R.literal("2001:DB8::1", M.TAAAA{})), "found 2001:DB8::1. 2001:db8::1"},
   Case{"literal IPv4 for AAAA: NODATA", lit_text(R.literal("192.0.2.1", M.TAAAA{})),
     "error: 192.0.2.1: no record of that type"},
   Case{"literal IPv6 for A: NODATA", lit_text(R.literal("::1", M.TA{})), "error: ::1: no record of that type"},
   Case{"literal for MX: a name", lit_text(R.literal("192.0.2.1", M.TMX{})), "none"},
   Case{"non-canonical quad is a name", lit_text(R.literal("010.0.0.1", M.TA{})), "none"},
   Case{"hosts A", lit_text(R.hosts_answer(R.hosts(cfg1()), "myhost", name("myhost"), M.TA{})),
     "found myhost. 10.9.8.7"},
   Case{"hosts AAAA", lit_text(R.hosts_answer(R.hosts(cfg1()), "myhost", name("myhost"), M.TAAAA{})),
     "found myhost. ::5"},
   Case{"hosts: case and trailing dot", lit_text(R.hosts_answer(R.hosts(cfg1()), "ALIAS.", name("ALIAS."), M.TA{})),
     "found ALIAS. 10.9.8.7"},
   Case{"hosts: no entry of the family", lit_text(R.hosts_answer(R.hosts(cfg1()), "router", name("router"), M.TAAAA{})),
     "none"},
   Case{"hosts: not for MX", lit_text(R.hosts_answer(R.hosts(cfg1()), "myhost", name("myhost"), M.TMX{})), "none"}]

def type_cases() -> List<&2, Case>:
  [Case{"type a", type_text(R.type_of("a")), "A"},
   Case{"type AAAA", type_text(R.type_of("AAAA")), "AAAA"},
   Case{"type Mx", type_text(R.type_of("Mx")), "MX"},
   Case{"type txt", type_text(R.type_of("txt")), "TXT"},
   Case{"type any", type_text(R.type_of("ANY")), "ANY"},
   Case{"type TYPE65", type_text(R.type_of("TYPE65")), "TYPE65"},
   Case{"type type1 is A", type_text(R.type_of("type1")), "A"},
   Case{"type TYPE70000", type_text(R.type_of("TYPE70000")), "none"},
   Case{"type TYPE", type_text(R.type_of("TYPE")), "none"},
   Case{"type bogus", type_text(R.type_of("bogus")), "none"}]

def rdata_cases() -> List<&2, Case>:
  [Case{"A text", R.rdata_text(M.RIpv4{93n, 184n, 215n, 14n}), "93.184.215.14"},
   Case{"AAAA text", R.rdata_text(M.RIpv6{[8193n, 3512n, 0n, 0n, 0n, 0n, 0n, 1n]}), "2001:db8::1"},
   Case{"CNAME text", R.rdata_text(M.RName{name("github.com")}), "github.com."},
   Case{"root name text", R.rdata_text(M.RName{Nil{}}), "."},
   Case{"MX text", R.rdata_text(M.RMx{10n, name("smtp.example.com")}), "10 smtp.example.com."},
   Case{"TXT text", R.rdata_text(M.RTxt{[[104, 105], [34, 92, 32, 200, 10]]}), "\"hi\" \"\\\"\\\\ \\200\\010\""},
   Case{"TXT empty string", R.rdata_text(M.RTxt{[Nil{}]}), "\"\""},
   Case{"SOA text", R.rdata_text(M.RSoa{name("ns.example"), name("admin.example"), 2024010101n, 7200n, 3600n,
     1209600n, 300n}), "ns.example. admin.example. 2024010101 7200 3600 1209600 300"},
   Case{"SRV text", R.rdata_text(M.RSrv{0n, 5n, 5060n, name("sip.example")}), "0 5 5060 sip.example."},
   Case{"raw text", R.rdata_text(M.RRaw{[171, 1]}), "\\# 2 ab01"},
   Case{"raw empty", R.rdata_text(M.RRaw{Nil{}}), "\\# 0 "},
   Case{"record text", R.record_text(a_rec("example.com", 1n, 2n, 3n, 4n)), "example.com.\t300\tIN\tA\t1.2.3.4"}]

def error_cases() -> List<&2, Case>:
  [Case{"BadName", R.error_show(M.BadName{M.EmptyLabel{}}), "bad name: empty label"},
   Case{"BadName long label", R.error_show(M.BadName{M.LabelTooLong{}}), "bad name: label longer than 63 bytes"},
   Case{"NxDomain", R.error_show(M.NxDomain{"x.test"}), "x.test: no such name (NXDOMAIN)"},
   Case{"NoData", R.error_show(M.NoData{"x.test"}), "x.test: no record of that type"},
   Case{"ServFail", R.error_show(M.ServFail{2n}), "server failure (SERVFAIL)"},
   Case{"Malformed", R.error_show(M.Malformed{M.BadPointer{}}), "malformed response: bad compression pointer"},
   Case{"Mismatch", R.error_show(M.Mismatch{}), "a response did not match the query"},
   Case{"NoServers", R.error_show(M.NoServers{}), "no nameservers"},
   Case{"Connect", R.error_show(M.Connect{111, "Connection refused"}), "connect error 111: Connection refused"},
   Case{"Io", R.error_show(M.Io{104, "Connection reset by peer"}), "I/O error 104: Connection reset by peer"},
   Case{"Timeout", R.error_show(M.Timeout{}), "timed out"},
   Case{"Os", R.error_show(M.Os{2, "Name or service not known"}), "resolver error 2: Name or service not known"},
   Case{"Config", R.error_show(M.Config{"x"}), "configuration: x"}]

def all_cases() -> List<&2, Case>:
  List.concat(&2, Case, [classify_cases(), policy_cases(), config_cases(), lit_cases(), type_cases(), rdata_cases(),
    error_cases()])

# IO without the network
# ----------------------

def io_check(label: String, act: IO(String), want: String, fails: Nat) -> IO(Nat):
  IO.bind(String, Nat, act, got => check(Case{label, got, want}, fails))

def resolving(cfg: R.Config, n: String, t: M.RType) -> IO(String):
  IO.bind(Result<&2, &2, M.Error, M.Resolved>, String, R.resolve(cfg, n, t),
    r => IO.pure(String, resolved_text(r)))

def looking(act: IO(Result<&2, &2, M.Error, List<&2, String>>)) -> IO(String):
  IO.bind(Result<&2, &2, M.Error, List<&2, String>>, String, act, r => IO.pure(String, addrs_text(r)))

def loading(r: String, h: String) -> IO(String):
  IO.bind(Result<&2, &2, M.Error, R.Config>, String, R.load(r, h), x => IO.pure(String, loaded_text(x)))

def none() -> R.Config:
  R.with_servers(cfg1(), Nil{})

def finish(fails: Nat) -> IO(Unit):
  match fails:
    case 0n:
      IO.print("ALL PASS")
    case 1n+p:
      IO.print("SOME FAIL: " ++ Nat.show(1n+p))

def main() -> IO(Unit):
  do IO<Unit>:
    f : Nat <- checks(all_cases(), 0n)
    f : Nat <- io_check("resolve: literal", resolving(none(), "10.1.2.3", M.TA{}), "found 10.1.2.3. 10.1.2.3", f)
    f : Nat <- io_check("resolve: hosts A", resolving(none(), "myhost", M.TA{}), "found myhost. 10.9.8.7", f)
    f : Nat <- io_check("resolve: hosts AAAA", resolving(none(), "MyHost.", M.TAAAA{}), "found MyHost. ::5", f)
    f : Nat <- io_check("resolve: no servers", resolving(none(), "router", M.TAAAA{}), "error: no nameservers", f)
    f : Nat <- io_check("resolve: no servers, MX", resolving(none(), "myhost", M.TMX{}), "error: no nameservers", f)
    f : Nat <- io_check("resolve: bad name", resolving(none(), "a..b", M.TA{}), "error: bad name: empty label", f)
    f : Nat <- io_check("resolve: bad char", resolving(none(), "a b", M.TA{}),
      "error: bad name: character that is not visible ASCII", f)
    f : Nat <- io_check("resolve: unsupported type", resolving(none(), "x.test", M.TOther{70000n}),
      "error: configuration: unsupported query type", f)
    f : Nat <- io_check("lookup_ipv4 literal", looking(R.lookup_ipv4(none(), "127.0.0.1")), "127.0.0.1", f)
    f : Nat <- io_check("lookup_ipv6 literal", looking(R.lookup_ipv6(none(), "::1")), "::1", f)
    f : Nat <- io_check("lookup_ipv4 hosts", looking(R.lookup_ipv4(none(), "alias")), "10.9.8.7", f)
    f : Nat <- io_check("lookup_ipv6 of an IPv4 literal", looking(R.lookup_ipv6(none(), "127.0.0.1")),
      "error: 127.0.0.1: no record of that type", f)
    f : Nat <- io_check("load: missing files", loading("/nonexistent/resolv.conf", "/nonexistent/hosts"),
      "servers 127.0.0.1 search  ndots 1 attempts 2 port 53 timeout 5000", f)
    f : Nat <- io_check("load: a directory", loading("/", "/nonexistent/hosts"),
      "error: configuration: cannot read /: error 21: Is a directory", f)
    finish(f)
