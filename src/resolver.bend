import Base
import ./bytes.bend as B
import ./num.bend as N
import ./types.bend as M
import ./name.bend as NM
import ./ip.bend as IP
import ./encode.bend as E
import ./decode.bend as D
import ./conf.bend as CF
import ./answer.bend as A
import ./transport.bend as X

# The native stub resolver: configuration, the hosts file, the search list,
# nameservers and retries, CNAME re-queries; and the texts a caller shows
# (error messages, record presentation).
#
#   system()                    /etc/resolv.conf and /etc/hosts
#   load(resolv, hosts)         the same from other paths
#   resolve(cfg, name, rtype)   Resolved{owner, records} or why not
#   lookup_ipv4 / lookup_ipv6   the addresses as text
#
# How resolve answers (resolv.conf(5), glibc's res_nsearch where silent):
#  1. A literal: for A, a canonical dotted quad (IP.parse4) is its own
#     answer; for AAAA, an IPv6 address (IP.parse6). A literal of the other
#     family is NoData. Any other type goes to DNS as a name.
#  2. The name must be valid text (NM.from_text), else BadName.
#  3. For A and AAAA, the config's hosts entries (CF.hosts_lookup, one
#     trailing dot ignored): the addresses of the wanted family, in file
#     order, owned by the name, TTL 0. None of that family: on to DNS.
#  4. Each search candidate (CF.candidates) in turn; a candidate that is not
#     a valid name (too long once suffixed) is skipped. For each candidate
#     the tries are the nameservers in order, `attempts` times over
#     (tries(cfg)). Each try is one TCP exchange (X.query) with a fresh
#     random id (IO.random_u32, mod 65536) and the EDNS0 query (E.query),
#     the response judged by `classify`:
#       - not received (Connect, Io, Timeout), not decodable (Malformed), or
#         not answering the query (A.accept fails: Mismatch);
#         or an rcode other than NOERROR and NXDOMAIN (ServFail{rcode}:
#         SERVFAIL, REFUSED, NOTIMP, FORMERR, ...)    -> the next try
#       - NXDOMAIN (rcode 3, even with a CNAME in the answer: RFC 6604)
#                                                     -> the next candidate
#       - NOERROR: A.addresses at the question name: Found -> the answer;
#         Alias{target} -> re-query target (absolute, the same tries, at
#         most MAX_ALIASES times; past that ServFail{2}, as recursive
#         resolvers report a chain too long); Nothing -> NoData, noted,
#         and the next candidate.
#     When every try failed, a ServFail is noted and the next candidate
#     tried (glibc's got_servfail); any other failure (a timeout, a refused
#     connection, a bad response) ends the lookup with that error, the last
#     try's.
#  5. After the last candidate: NoData{the first candidate that had no
#     record of the type} if any, else the noted ServFail, else
#     NxDomain{name}.
# TC (truncated) is not acted on: over TCP there is no larger transport to
# retry with, so the records present are used. No cache; no IPv6
# nameservers (Base's TCP.connect reaches IPv4 only; CF.resolv skips them).
#
# Timeouts: Config.timeout_ms bounds each blocking step of an exchange (the
# connect, the send, each read; see X.within: a stalled step is not
# cancelled, so after a Timeout the program cannot end normally until the
# peer acts or the OS gives up; IO.die still ends it at once).
#
# NOTE (loops): every walk over a caller- or response-sized list (records,
# hosts addresses, servers, TXT bytes) is a direct tail call; the IO loops
# over tries, aliases and candidates recurse once per query, inside binds.

def MAX_ALIASES() -> Nat:
  8n

# Config
# ------

# conf: as CF.resolv reads it (nameservers, search, ndots, timeout_s,
# attempts); hosts: CF.hosts entries; port: the nameservers' TCP port;
# timeout_ms: each blocking step's limit (0: none).
type Config is Data:
  Config{conf: M.Conf, hosts: List<&2, M.HostEntry>, port: Nat, timeout_ms: Nat}

def conf.servers(c: M.Conf) -> List<&2, String>:
  match c:
    case M.Conf{ns, ss, nd, t, at}:
      ns

def conf.with_servers(c: M.Conf, list: List<&2, String>) -> M.Conf:
  match c:
    case M.Conf{ns, ss, nd, t, at}:
      M.Conf{list, ss, nd, t, at}

def conf.with_local(c: M.Conf) -> M.Conf:
  match c:
    case M.Conf{ns, ss, nd, t, at}:
      match ns:
        case Nil{}:
          M.Conf{["127.0.0.1"], ss, nd, t, at}
        case Con{h, r}:
          M.Conf{h <> r, ss, nd, t, at}

def conf.timeout_ms(c: M.Conf) -> Nat:
  match c:
    case M.Conf{ns, ss, nd, t, at}:
      Nat.mul(t, 1000n)

# The config for a parsed resolv.conf and hosts file: no nameserver means
# 127.0.0.1 (as glibc), port 53, timeout_s seconds per step.
def from_conf(+c: M.Conf, hosts: List<&2, M.HostEntry>) -> Config:
  +c2 = conf.with_local(c)
  Config{c2, hosts, 53n, conf.timeout_ms(c2)}

# The config from the texts of a resolv.conf and a hosts file.
def from_text(resolv: String, hosts: String) -> Config:
  from_conf(CF.resolv(resolv), CF.hosts(hosts))

# No resolv.conf and no hosts file: 127.0.0.1, ndots 1, 5 s, 2 attempts.
def default_config() -> Config:
  from_conf(CF.default_conf(), Nil{})

def with_servers(cfg: Config, list: List<&2, String>) -> Config:
  match cfg:
    case Config{c, hs, p, t}:
      Config{conf.with_servers(c, list), hs, p, t}

def with_port(cfg: Config, port: Nat) -> Config:
  match cfg:
    case Config{c, hs, p, t}:
      Config{c, hs, port, t}

def with_timeout(cfg: Config, ms: Nat) -> Config:
  match cfg:
    case Config{c, hs, p, t}:
      Config{c, hs, p, ms}

# At least 1.
def with_attempts(cfg: Config, n: Nat) -> Config:
  match cfg:
    case Config{c, hs, p, t}:
      match c:
        case M.Conf{ns, ss, nd, ts, at}:
          Config{M.Conf{ns, ss, nd, ts, Nat.max(1n, n)}, hs, p, t}

def with_search(cfg: Config, list: List<&2, String>) -> Config:
  match cfg:
    case Config{c, hs, p, t}:
      match c:
        case M.Conf{ns, ss, nd, ts, at}:
          Config{M.Conf{ns, list, nd, ts, at}, hs, p, t}

def with_ndots(cfg: Config, n: Nat) -> Config:
  match cfg:
    case Config{c, hs, p, t}:
      match c:
        case M.Conf{ns, ss, nd, ts, at}:
          Config{M.Conf{ns, ss, n, ts, at}, hs, p, t}

def with_hosts(cfg: Config, entries: List<&2, M.HostEntry>) -> Config:
  match cfg:
    case Config{c, hs, p, t}:
      Config{c, entries, p, t}

def conf(cfg: Config) -> M.Conf:
  match cfg:
    case Config{c, hs, p, t}:
      c

def servers(cfg: Config) -> List<&2, String>:
  conf.servers(conf(cfg))

def conf.search(c: M.Conf) -> List<&2, String>:
  match c:
    case M.Conf{ns, ss, nd, t, at}:
      ss

def conf.ndots(c: M.Conf) -> Nat:
  match c:
    case M.Conf{ns, ss, nd, t, at}:
      nd

def conf.attempts(c: M.Conf) -> Nat:
  match c:
    case M.Conf{ns, ss, nd, t, at}:
      at

def search(cfg: Config) -> List<&2, String>:
  conf.search(conf(cfg))

def ndots(cfg: Config) -> Nat:
  conf.ndots(conf(cfg))

def attempts(cfg: Config) -> Nat:
  conf.attempts(conf(cfg))

def hosts(cfg: Config) -> List<&2, M.HostEntry>:
  match cfg:
    case Config{c, hs, p, t}:
      hs

def port(cfg: Config) -> Nat:
  match cfg:
    case Config{c, hs, p, t}:
      p

def timeout_ms(cfg: Config) -> Nat:
  match cfg:
    case Config{c, hs, p, t}:
      t

# The tries for one name: the nameservers in order, `attempts` times over
# (a loop; servers ++ acc as two reverses).
def tries.go(k: Nat, +ns: List<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match k:
    case 0n:
      acc
    case 1n+p:
      tries.go(p, ns, B.rev(String, B.rev(String, ns, Nil{}), acc))

def tries(cfg: Config) -> List<&2, String>:
  match cfg:
    case Config{c, hs, p, t}:
      match c:
        case M.Conf{ns, ss, nd, ts, at}:
          tries.go(at, ns, Nil{})

# The names tried for `name`, in order (CF.candidates).
def candidates(cfg: Config, name: String) -> List<&2, String>:
  CF.candidates(conf(cfg), name)

# Reading the system's files
# --------------------------

def Text() -> Type:
  Result<&1, &1, U32 & String, String>

def read.close(p: File & Text()) -> IO(Text()):
  (f, r) = p
  IO.bind(Unit, Text(), File.close(f), u => IO.pure(Text(), r))

def read.opened(r: Result<&1, &1, U32 & String, File>) -> IO(Text()):
  match r:
    case Fail{e}:
      IO.pure(Text(), Fail{e})
    case Done{f}:
      IO.bind(File & Text(), Text(), File.read(f, 16777216), p => read.close(p))

# The text of the file at path (at most 16 MiB: one read).
def read_text(path: String) -> IO(Text()):
  IO.bind(Result<&1, &1, U32 & String, File>, Text(), File.open(path, "r"), r => read.opened(r))

def ENOENT() -> U32:
  2

def missing.pick(absent: Bool, path: String, +code: U32, message: String) -> Result<&2, &2, M.Error, String>:
  match absent:
    case True{}:
      Done{""}
    case False{}:
      Fail{M.Config{"cannot read " ++ path ++ ": error " ++ U32.show(code) ++ ": " ++ message}}

# A file's text; a file that does not exist reads as "".
def text_or_empty(r: Text(), path: String) -> Result<&2, &2, M.Error, String>:
  match r:
    case Done{s}:
      Done{s}
    case Fail{(code, message)}:
      +c = code
      missing.pick(U32.is_eq(c, ENOENT()), path, c, message)

def loaded(r: Result<&2, &2, M.Error, String>, h: Result<&2, &2, M.Error, String>) -> Result<&2, &2, M.Error, Config>:
  match r h:
    case Fail{e} _:
      Fail{e}
    case Done{rt} Fail{e}:
      Fail{e}
    case Done{rt} Done{ht}:
      Done{from_text(rt, ht)}

def load.hosts(r: Result<&2, &2, M.Error, String>, +hosts_path: String) -> IO(Result<&2, &2, M.Error, Config>):
  IO.bind(Text(), Result<&2, &2, M.Error, Config>, read_text(hosts_path),
    h => IO.pure(Result<&2, &2, M.Error, Config>, loaded(r, text_or_empty(h, hosts_path))))

# The config from a resolv.conf and a hosts file at these paths. A file
# that does not exist reads as empty (so no resolv.conf means 127.0.0.1);
# any other failure to read one is a Config error.
def load(+resolv_path: String, hosts_path: String) -> IO(Result<&2, &2, M.Error, Config>):
  IO.bind(Text(), Result<&2, &2, M.Error, Config>, read_text(resolv_path),
    r => load.hosts(text_or_empty(r, resolv_path), hosts_path))

# /etc/resolv.conf and /etc/hosts.
def system() -> IO(Result<&2, &2, M.Error, Config>):
  load("/etc/resolv.conf", "/etc/hosts")

# Judging one response
# --------------------

# What one try, or one name's tries, came to.
type Outcome is Data:
  OFound{name: List<&2, List<&2, U32>>, records: List<&2, M.Record>}
  OAlias{target: List<&2, List<&2, U32>>}
  ONoData{}
  ONxDomain{}
  OFailed{error: M.Error}

def answered(a: M.Answer) -> Outcome:
  match a:
    case M.Found{n, rs}:
      OFound{n, rs}
    case M.Alias{t}:
      OAlias{t}
    case M.Nothing{}:
      ONoData{}

def nxdomain(nx: Bool, rc: Nat) -> Outcome:
  match nx:
    case True{}:
      ONxDomain{}
    case False{}:
      OFailed{M.ServFail{rc}}

def noerror(ok: Bool, +rc: Nat, q: M.Question, m: M.Message) -> Outcome:
  match ok:
    case True{}:
      match q:
        case M.Question{n, t, c}:
          answered(A.addresses(n, t, m))
    case False{}:
      nxdomain(Nat.is_eq(rc, 3n), rc)

def accepted(ok: Bool, q: M.Question, +m: M.Message) -> Outcome:
  match ok:
    case True{}:
      +rc = A.rcode(m)
      noerror(Nat.is_eq(rc, 0n), rc, q, m)
    case False{}:
      OFailed{M.Mismatch{}}

def judged(id: Nat, +q: M.Question, d: Result<&2, &2, M.DecodeError, M.Message>) -> Outcome:
  match d:
    case Fail{e}:
      OFailed{M.Malformed{e}}
    case Done{+m}:
      accepted(A.accept(id, q, m), q, m)

# One try's outcome: what X.query brought, judged against the query (id, q).
def classify(id: Nat, q: M.Question, r: Result<&2, &2, M.Error, List<&2, U32>>) -> Outcome:
  match r:
    case Fail{e}:
      OFailed{e}
    case Done{xs}:
      judged(id, q, D.message(xs))

# Asking
# ------

def ask.id(r: Result<&1, &1, U32 & String, U32>, server: String, port: Nat, ms: Nat, +name: M.Name(),
  +rtype: M.RType) -> IO(Outcome):
  match r:
    case Fail{(code, message)}:
      IO.pure(Outcome, OFailed{M.Io{code, message}})
    case Done{u}:
      +id = Nat.mod(U32.to_nat(u), 65536n)
      IO.bind(Result<&2, &2, M.Error, List<&2, U32>>, Outcome,
        X.query(server, port, E.query(id, name, rtype), 65535n, ms),
        res => IO.pure(Outcome, classify(id, M.Question{name, rtype, M.CIN{}}, res)))

# One try: (name, rtype) asked of server:port with a fresh id.
def ask(server: String, port: Nat, ms: Nat, name: M.Name(), rtype: M.RType) -> IO(Outcome):
  IO.bind(Result<&1, &1, U32 & String, U32>, Outcome, IO.random_u32(),
    r => ask.id(r, server, port, ms, name, rtype))

# A failed try moves on to the next one; anything else is the answer.
def over.next(st: Outcome, rest: M.Error -> IO(Outcome)) -> IO(Outcome):
  match st:
    case OFailed{e}:
      rest(e)
    case OFound{n, rs}:
      IO.pure(Outcome, OFound{n, rs})
    case OAlias{t}:
      IO.pure(Outcome, OAlias{t})
    case ONoData{}:
      IO.pure(Outcome, ONoData{})
    case ONxDomain{}:
      IO.pure(Outcome, ONxDomain{})

# The tries in order until one is not a failure; all failed: the last
# failure (NoServers if there was no try at all).
def over(ts: List<&2, String>, +port: Nat, +ms: Nat, +name: M.Name(), +rtype: M.RType, last: M.Error) ->
  IO(Outcome):
  match ts:
    case Nil{}:
      IO.pure(Outcome, OFailed{last})
    case Con{s, t}:
      IO.bind(Outcome, Outcome, ask(s, port, ms, name, rtype),
        st => over.next(st, e => over(t, port, ms, name, rtype, e)))

def TOO_LONG() -> M.Error:
  M.ServFail{2n}

def chain.next(st: Outcome, more: M.Name() -> IO(Outcome)) -> IO(Outcome):
  match st:
    case OAlias{t}:
      more(t)
    case OFound{n, rs}:
      IO.pure(Outcome, OFound{n, rs})
    case ONoData{}:
      IO.pure(Outcome, ONoData{})
    case ONxDomain{}:
      IO.pure(Outcome, ONxDomain{})
    case OFailed{e}:
      IO.pure(Outcome, OFailed{e})

def chain.last(st: Outcome) -> Outcome:
  match st:
    case OAlias{t}:
      OFailed{TOO_LONG()}
    case OFound{n, rs}:
      OFound{n, rs}
    case ONoData{}:
      ONoData{}
    case ONxDomain{}:
      ONxDomain{}
    case OFailed{e}:
      OFailed{e}

# One name through the tries, then its alias targets, k more at most.
def chain(k: Nat, +ts: List<&2, String>, +port: Nat, +ms: Nat, name: M.Name(), +rtype: M.RType) -> IO(Outcome):
  match k:
    case 0n:
      IO.bind(Outcome, Outcome, over(ts, port, ms, name, rtype, M.NoServers{}),
        st => IO.pure(Outcome, chain.last(st)))
    case 1n+p:
      IO.bind(Outcome, Outcome, over(ts, port, ms, name, rtype, M.NoServers{}),
        st => chain.next(st, tg => chain(p, ts, port, ms, tg, rtype)))

# The search
# ----------

# What the candidates so far left: the first one with no record of the
# type, and a noted server failure.
type Seen is Data:
  Seen{nodata: Maybe<&2, String>, failed: Maybe<&2, M.Error>}

# After one candidate: the lookup's result, or go on with the next.
type Next is Data:
  NStop{result: Result<&2, &2, M.Error, M.Resolved>}
  NGo{seen: Seen}

def is_servfail(e: M.Error) -> Bool:
  match e:
    case M.ServFail{rc}:
      True{}
    case _:
      False{}

def after.failed(soft: Bool, e: M.Error, s: Seen) -> Next:
  match soft s:
    case True{} Seen{nd, f}:
      NGo{Seen{nd, Maybe.or(&2, M.Error, f, Some{e})}}
    case False{} _:
      NStop{Fail{e}}

# The policy after candidate c came to st (see the top of the file).
def after(st: Outcome, c: String, s: Seen) -> Next:
  match st:
    case OFound{n, rs}:
      NStop{Done{M.Resolved{n, rs}}}
    case ONxDomain{}:
      NGo{s}
    case ONoData{}:
      match s:
        case Seen{nd, f}:
          NGo{Seen{Maybe.or(&2, String, nd, Some{c}), f}}
    case OFailed{+e}:
      after.failed(is_servfail(e), e, s)
    case OAlias{t}:
      NStop{Fail{TOO_LONG()}}

# After the last candidate.
def finish(name: String, s: Seen) -> Result<&2, &2, M.Error, M.Resolved>:
  match s:
    case Seen{nd, f}:
      match nd f:
        case Some{c} _:
          Fail{M.NoData{c}}
        case None{} Some{e}:
          Fail{e}
        case None{} None{}:
          Fail{M.NxDomain{name}}

def seen0() -> Seen:
  Seen{None{}, None{}}

def Resolution() -> Type:
  IO(Result<&2, &2, M.Error, M.Resolved>)

def cands.next(n: Next, rest: Seen -> Resolution()) -> Resolution():
  match n:
    case NStop{r}:
      IO.pure(Result<&2, &2, M.Error, M.Resolved>, r)
    case NGo{s}:
      rest(s)

def cands.try(r: Result<&2, &2, M.NameError, M.Name()>, +c: String, +ts: List<&2, String>, +port: Nat, +ms: Nat,
  +rtype: M.RType, s: Seen, rest: Seen -> Resolution()) -> Resolution():
  match r:
    case Fail{e}:
      rest(s)
    case Done{n}:
      IO.bind(Outcome, Result<&2, &2, M.Error, M.Resolved>, chain(MAX_ALIASES(), ts, port, ms, n, rtype),
        st => cands.next(after(st, c, s), rest))

# Each candidate in turn (see the top of the file).
def cands(cs: List<&2, String>, +ts: List<&2, String>, +port: Nat, +ms: Nat, +rtype: M.RType, +name: String,
  s: Seen) -> Resolution():
  match cs:
    case Nil{}:
      IO.pure(Result<&2, &2, M.Error, M.Resolved>, finish(name, s))
    case Con{+c, t}:
      cands.try(NM.from_text(c), c, ts, port, ms, rtype, s, s2 => cands(t, ts, port, ms, rtype, name, s2))

# Literals and the hosts file
# ---------------------------

def is_a(t: M.RType) -> Bool:
  match t:
    case M.TA{}:
      True{}
    case _:
      False{}

def is_aaaa(t: M.RType) -> Bool:
  match t:
    case M.TAAAA{}:
      True{}
    case _:
      False{}

def owner(r: Result<&2, &2, M.NameError, M.Name()>) -> M.Name():
  match r:
    case Done{n}:
      n
    case Fail{e}:
      Nil{}

def literal.pick(want: Bool, +name: String, rtype: M.RType, d: M.RData) -> Maybe<&2, Result<&2, &2, M.Error, M.Resolved>>:
  match want:
    case True{}:
      +n = owner(NM.from_text(name))
      Some{Done{M.Resolved{n, [M.Record{n, rtype, M.CIN{}, 0n, d}]}}}
    case False{}:
      Some{Fail{M.NoData{name}}}

def literal.of(v4: Maybe<&2, M.RData>, v6: Maybe<&2, M.RData>, +name: String, +rtype: M.RType) ->
  Maybe<&2, Result<&2, &2, M.Error, M.Resolved>>:
  match v4 v6:
    case Some{d} _:
      literal.pick(is_a(rtype), name, rtype, d)
    case None{} Some{d}:
      literal.pick(is_aaaa(rtype), name, rtype, d)
    case None{} None{}:
      None{}

def literal.when(addr: Bool, +name: String, rtype: M.RType) -> Maybe<&2, Result<&2, &2, M.Error, M.Resolved>>:
  match addr:
    case True{}:
      literal.of(IP.parse4(name), IP.parse6(name), name, rtype)
    case False{}:
      None{}

# For A and AAAA: an address literal answers itself (or NoData for the
# other family's type); None for anything else.
def literal(name: String, +rtype: M.RType) -> Maybe<&2, Result<&2, &2, M.Error, M.Resolved>>:
  literal.when(is_a(rtype) || is_aaaa(rtype), name, rtype)

# s without one trailing '.'.
def strip_dot(s: String) -> String:
  String.reverse(CF.drop_dot(String.reverse(s)))

def host.rec(d: Maybe<&2, M.RData>, +n: M.Name(), +rtype: M.RType, acc: List<&2, M.Record>) -> List<&2, M.Record>:
  match d:
    case Some{x}:
      M.Record{n, rtype, M.CIN{}, 0n, x} <> acc
    case None{}:
      acc

def host.parse(v4: Bool, +a: String) -> Maybe<&2, M.RData>:
  match v4:
    case True{}:
      IP.parse4(a)
    case False{}:
      IP.parse6(a)

# The addresses of the family as records owned by n, reversed onto acc (a loop).
def host.go(addrs: List<&2, String>, +n: M.Name(), +rtype: M.RType, acc: List<&2, M.Record>) -> List<&2, M.Record>:
  match addrs:
    case Nil{}:
      acc
    case Con{a, t}:
      host.go(t, n, rtype, host.rec(host.parse(is_a(rtype), a), n, rtype, acc))

def hosted(rs: List<&2, M.Record>, n: M.Name()) -> Maybe<&2, Result<&2, &2, M.Error, M.Resolved>>:
  match rs:
    case Nil{}:
      None{}
    case Con{h, t}:
      Some{Done{M.Resolved{n, h <> t}}}

def hosts_answer.when(want: Bool, entries: List<&2, M.HostEntry>, name: String, +n: M.Name(), rtype: M.RType) ->
  Maybe<&2, Result<&2, &2, M.Error, M.Resolved>>:
  match want:
    case True{}:
      hosted(B.rev(M.Record, host.go(CF.hosts_lookup(entries, strip_dot(name)), n, rtype, Nil{}), Nil{}), n)
    case False{}:
      None{}

# For A and AAAA: the hosts entries' addresses of the family for name
# (owned by n), if any.
def hosts_answer(entries: List<&2, M.HostEntry>, name: String, n: M.Name(), +rtype: M.RType) ->
  Maybe<&2, Result<&2, &2, M.Error, M.Resolved>>:
  hosts_answer.when(is_a(rtype) || is_aaaa(rtype), entries, name, n, rtype)

# Resolving
# ---------

def resolve.dns(ok: Bool, +cfg: Config, +name: String, +rtype: M.RType) -> Resolution():
  match ok:
    case True{}:
      cands(candidates(cfg, name), tries(cfg), port(cfg), timeout_ms(cfg), rtype, name, seen0())
    case False{}:
      IO.pure(Result<&2, &2, M.Error, M.Resolved>, Fail{M.Config{"unsupported query type"}})

def resolve.hosts(h: Maybe<&2, Result<&2, &2, M.Error, M.Resolved>>, cfg: Config, name: String, +rtype: M.RType) ->
  Resolution():
  match h:
    case Some{r}:
      IO.pure(Result<&2, &2, M.Error, M.Resolved>, r)
    case None{}:
      resolve.dns(E.type_ok(rtype), cfg, name, rtype)

def resolve.named(r: Result<&2, &2, M.NameError, M.Name()>, +cfg: Config, +name: String, +rtype: M.RType) ->
  Resolution():
  match r:
    case Fail{e}:
      IO.pure(Result<&2, &2, M.Error, M.Resolved>, Fail{M.BadName{e}})
    case Done{n}:
      resolve.hosts(hosts_answer(hosts(cfg), name, n, rtype), cfg, name, rtype)

def resolve.lit(l: Maybe<&2, Result<&2, &2, M.Error, M.Resolved>>, +cfg: Config, +name: String, +rtype: M.RType) ->
  Resolution():
  match l:
    case Some{r}:
      IO.pure(Result<&2, &2, M.Error, M.Resolved>, r)
    case None{}:
      resolve.named(NM.from_text(name), cfg, name, rtype)

# The records of rtype for name (see the top of the file).
def resolve(+cfg: Config, +name: String, +rtype: M.RType) -> Resolution():
  resolve.lit(literal(name, rtype), cfg, name, rtype)

# Addresses
# ---------

def addr.of(d: M.RData) -> Maybe<&2, String>:
  match d:
    case M.RIpv4{a, b, c, e}:
      Some{IP.show4(a, b, c, e)}
    case M.RIpv6{gs}:
      Some{IP.show6(gs)}
    case _:
      None{}

def addr.add(m: Maybe<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match m:
    case Some{s}:
      s <> acc
    case None{}:
      acc

# Each A / AAAA record's address as text, reversed onto acc (a loop).
def addrs.go(rs: List<&2, M.Record>, acc: List<&2, String>) -> List<&2, String>:
  match rs:
    case Nil{}:
      acc
    case Con{r, t}:
      match r:
        case M.Record{n, ty, c, ttl, d}:
          addrs.go(t, addr.add(addr.of(d), acc))

# The addresses among the records, as text, in order.
def addresses(rs: List<&2, M.Record>) -> List<&2, String>:
  B.rev(String, addrs.go(rs, Nil{}), Nil{})

def addresses.of(r: Result<&2, &2, M.Error, M.Resolved>) -> Result<&2, &2, M.Error, List<&2, String>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match x:
        case M.Resolved{n, rs}:
          Done{addresses(rs)}

def lookup(+cfg: Config, +name: String, +rtype: M.RType) -> IO(Result<&2, &2, M.Error, List<&2, String>>):
  IO.bind(Result<&2, &2, M.Error, M.Resolved>, Result<&2, &2, M.Error, List<&2, String>>, resolve(cfg, name, rtype),
    r => IO.pure(Result<&2, &2, M.Error, List<&2, String>>, addresses.of(r)))

# The IPv4 addresses of name (A records, through CNAMEs), as dotted quads.
def lookup_ipv4(+cfg: Config, +name: String) -> IO(Result<&2, &2, M.Error, List<&2, String>>):
  lookup(cfg, name, M.TA{})

# The IPv6 addresses of name (AAAA records), as RFC 5952 text.
def lookup_ipv6(+cfg: Config, +name: String) -> IO(Result<&2, &2, M.Error, List<&2, String>>):
  lookup(cfg, name, M.TAAAA{})

# Texts
# -----

def rcode_name(+rc: Nat) -> String:
  Bool.pick(String, Nat.is_eq(rc, 0n), "NOERROR",
  Bool.pick(String, Nat.is_eq(rc, 1n), "FORMERR",
  Bool.pick(String, Nat.is_eq(rc, 2n), "SERVFAIL",
  Bool.pick(String, Nat.is_eq(rc, 3n), "NXDOMAIN",
  Bool.pick(String, Nat.is_eq(rc, 4n), "NOTIMP",
  Bool.pick(String, Nat.is_eq(rc, 5n), "REFUSED",
  "RCODE" ++ Nat.show(rc)))))))

def name_error_show(e: M.NameError) -> String:
  match e:
    case M.EmptyLabel{}:
      "empty label"
    case M.LabelTooLong{}:
      "label longer than 63 bytes"
    case M.NameTooLong{}:
      "name longer than 255 bytes"
    case M.BadEscape{}:
      "bad escape"
    case M.BadChar{}:
      "character that is not visible ASCII"

def decode_error_show(e: M.DecodeError) -> String:
  match e:
    case M.Short{}:
      "the message ended early"
    case M.BadPointer{}:
      "bad compression pointer"
    case M.BadLabel{}:
      "bad label"
    case M.BadRdata{}:
      "bad record data"
    case M.Trailing{}:
      "bytes after the message"

def coded(what: String, code: U32, message: String) -> String:
  what ++ " error " ++ U32.show(code) ++ ": " ++ message

# One line saying why a lookup failed.
def error_show(e: M.Error) -> String:
  match e:
    case M.BadName{n}:
      "bad name: " ++ name_error_show(n)
    case M.NxDomain{n}:
      n ++ ": no such name (NXDOMAIN)"
    case M.NoData{n}:
      n ++ ": no record of that type"
    case M.ServFail{+rc}:
      "server failure (" ++ rcode_name(rc) ++ ")"
    case M.Malformed{d}:
      "malformed response: " ++ decode_error_show(d)
    case M.Mismatch{}:
      "a response did not match the query"
    case M.NoServers{}:
      "no nameservers"
    case M.Connect{c, m}:
      coded("connect", c, m)
    case M.Io{c, m}:
      coded("I/O", c, m)
    case M.Timeout{}:
      "timed out"
    case M.Os{c, m}:
      coded("resolver", c, m)
    case M.Config{m}:
      "configuration: " ++ m

# Types by name
# -------------

def type_name(t: M.RType) -> String:
  match t:
    case M.TA{}:
      "A"
    case M.TNS{}:
      "NS"
    case M.TCNAME{}:
      "CNAME"
    case M.TSOA{}:
      "SOA"
    case M.TPTR{}:
      "PTR"
    case M.TMX{}:
      "MX"
    case M.TTXT{}:
      "TXT"
    case M.TAAAA{}:
      "AAAA"
    case M.TSRV{}:
      "SRV"
    case M.TOPT{}:
      "OPT"
    case M.TANY{}:
      "ANY"
    case M.TOther{c}:
      "TYPE" ++ Nat.show(c)

def type_pick(hit: Bool, t: M.RType, rest: Maybe<&2, M.RType>) -> Maybe<&2, M.RType>:
  match hit:
    case True{}:
      Some{t}
    case False{}:
      rest

def drop.go(k: Nat, s: String) -> String:
  match k s:
    case 0n _:
      s
    case 1n+p SCon{c, t}:
      drop.go(p, t)
    case 1n+p SNil{}:
      SNil{}

def code_type(+c: Nat, known: Maybe<&2, M.RType>) -> M.RType:
  match known:
    case Some{t}:
      t
    case None{}:
      M.TOther{c}

def numbered.in(ok: Bool, +c: Nat) -> Maybe<&2, M.RType>:
  match ok:
    case True{}:
      Some{code_type(c, E.type_known(c))}
    case False{}:
      None{}

def numbered.of(m: Maybe<&2, Nat>) -> Maybe<&2, M.RType>:
  match m:
    case Some{+c}:
      numbered.in(Nat.is_le(c, 65535n), c)
    case None{}:
      None{}

# "TYPEnnn" (RFC 3597), lowercased.
def numbered(pre: Bool, l: String) -> Maybe<&2, M.RType>:
  match pre:
    case True{}:
      numbered.of(N.read(drop.go(4n, l)))
    case False{}:
      None{}

def type_of.l(+l: String) -> Maybe<&2, M.RType>:
  type_pick(String.eq(l, "a"), M.TA{},
  type_pick(String.eq(l, "ns"), M.TNS{},
  type_pick(String.eq(l, "cname"), M.TCNAME{},
  type_pick(String.eq(l, "soa"), M.TSOA{},
  type_pick(String.eq(l, "ptr"), M.TPTR{},
  type_pick(String.eq(l, "mx"), M.TMX{},
  type_pick(String.eq(l, "txt"), M.TTXT{},
  type_pick(String.eq(l, "aaaa"), M.TAAAA{},
  type_pick(String.eq(l, "srv"), M.TSRV{},
  type_pick(String.eq(l, "opt"), M.TOPT{},
  type_pick(String.eq(l, "any"), M.TANY{},
  numbered(String.starts_with(l, "type"), l))))))))))))

# A type by its name, ASCII case-insensitively: "A", "aaaa", "MX", ...,
# or "TYPEnnn" (nnn <= 65535; a known code gives the known type).
def type_of(s: String) -> Maybe<&2, M.RType>:
  type_of.l(CF.lower(s))

# Presentation
# ------------

# A name with its trailing dot: "example.com.", the root ".".
def fqdn(n: M.Name()) -> String:
  match n:
    case Nil{}:
      "."
    case Con{l, t}:
      NM.to_text(Con{l, t}) ++ "."

def lit(b: U32) -> String:
  SCon{Char.from_u32(b), SNil{}}

def txt.delim(+b: U32) -> String:
  Bool.pick(String, U32.is_eq(b, 34) || U32.is_eq(b, 92), SCon{'\\', lit(b)}, lit(b))

def txt.char(k: B.Class, +b: U32) -> String:
  match k:
    case B.Delim{}:
      txt.delim(b)
    case B.Sp{}:
      lit(b)
    case B.Ctl{}:
      NM.ddd(b)
    case B.Htab{}:
      NM.ddd(b)
    case B.Cr{}:
      NM.ddd(b)
    case B.Lf{}:
      NM.ddd(b)
    case B.High{}:
      NM.ddd(b)
    case B.Invalid{}:
      "\\999"
    case _:
      lit(b)

# A character-string's bytes as text, reversed onto acc (a loop).
def txt.go(xs: List<&2, U32>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{+b, t}:
      txt.go(t, String.reverse.go(txt.char(B.class(b), b), acc))

# "\"...\"": '"' and '\' escaped, other bytes outside 0x20..0x7E as \DDD.
def quoted(s: List<&2, U32>) -> String:
  String.reverse(SCon{'"', txt.go(s, SCon{'"', SNil{}})})

# The strings quoted and joined by spaces, as text reversed onto acc (a loop).
def txts.go(ss: List<&2, List<&2, U32>>, first: Bool, acc: String) -> String:
  match ss:
    case Nil{}:
      acc
    case Con{s, t}:
      match first:
        case True{}:
          txts.go(t, False{}, String.reverse.go(quoted(s), acc))
        case False{}:
          txts.go(t, False{}, String.reverse.go(quoted(s), SCon{' ', acc}))

def hex2(+b: U32) -> String:
  +h = N.hex_show(U32.to_nat(b))
  Bool.pick(String, Nat.is_lt(U32.to_nat(b), 16n), "0" ++ h, h)

# The bytes as hex, reversed onto acc (a loop).
def hex.go(xs: List<&2, U32>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{b, t}:
      hex.go(t, String.reverse.go(hex2(b), acc))

def count.go(xs: List<&2, U32>, k: Nat) -> Nat:
  match xs:
    case Nil{}:
      k
    case Con{h, t}:
      count.go(t, 1n+k)

# RFC 3597: "\# length hex".
def raw_text(+xs: List<&2, U32>) -> String:
  "\\# " ++ Nat.show(count.go(xs, 0n)) ++ String.reverse(hex.go(xs, " "))

# The RDATA in presentation form, as dig shows it.
def rdata_text(d: M.RData) -> String:
  match d:
    case M.RIpv4{a, b, c, e}:
      IP.show4(a, b, c, e)
    case M.RIpv6{gs}:
      IP.show6(gs)
    case M.RName{n}:
      fqdn(n)
    case M.RMx{p, n}:
      Nat.show(p) ++ " " ++ fqdn(n)
    case M.RTxt{ss}:
      String.reverse(txts.go(ss, True{}, SNil{}))
    case M.RSoa{mn, rn, se, rf, rt, ex, mi}:
      fqdn(mn) ++ " " ++ fqdn(rn) ++ " " ++ Nat.show(se) ++ " " ++ Nat.show(rf) ++ " " ++ Nat.show(rt)
        ++ " " ++ Nat.show(ex) ++ " " ++ Nat.show(mi)
    case M.RSrv{pr, w, po, t}:
      Nat.show(pr) ++ " " ++ Nat.show(w) ++ " " ++ Nat.show(po) ++ " " ++ fqdn(t)
    case M.RRaw{xs}:
      raw_text(xs)

def class_name(c: M.RClass) -> String:
  match c:
    case M.CIN{}:
      "IN"
    case M.COther{k}:
      "CLASS" ++ Nat.show(k)

# "owner. TTL CLASS TYPE rdata", tab-separated as in dig's answer section.
def record_text(r: M.Record) -> String:
  match r:
    case M.Record{n, t, c, ttl, d}:
      fqdn(n) ++ "\t" ++ Nat.show(ttl) ++ "\t" ++ class_name(c) ++ "\t" ++ type_name(t) ++ "\t" ++ rdata_text(d)
