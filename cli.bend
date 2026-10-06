import Base
import ./main.bend as P

# bender-dns: a small DNS query CLI using only the public library API.
# Build: bend cli.bend -o bender-dns
# Run:   ./bender-dns [options] [@server]... name [type]
#
# Answers use dig +short presentation: one line per record, preceded by
# the canonical owner when a CNAME or search suffix changed the name.
# IO.die exits explicitly so a timed-out read cannot keep the process alive
# (Base cannot cancel it). A successful query leaves a blank line on stderr.

def usage() -> String:
  "usage: bender-dns [options] [@server]... name [type]"

def help_text() -> String:
  usage() ++ "\n\n" ++
  "Query DNS over TCP using /etc/resolv.conf and /etc/hosts.\n" ++
  "The default type is A; type names are case-insensitive.\n\n" ++
  "  -s, --server IPv4  Nameserver (repeatable; also @IPv4)\n" ++
  "  -p, --port N       DNS port, 1..65535 (default: 53)\n" ++
  "      --timeout MS   Per-step timeout in milliseconds, 1..4294967295\n" ++
  "      --attempts N   Positive number of tries per server\n" ++
  "      --os           Use the OS resolver (A/AAAA; both if type omitted)\n" ++
  "  -h, --help         Show this help\n\n" ++
  "Types: A AAAA MX TXT NS CNAME SOA PTR SRV OPT ANY TYPEnnn\n" ++
  "Aliases: +tcp-port N, +timeout MS, +attempts N\n" ++
  "Timeout and attempt defaults come from resolv.conf.\n" ++
  "--os cannot be combined with server, port, timeout or attempt options.\n\n" ++
  "Examples:\n" ++
  "  bender-dns example.com\n" ++
  "  bender-dns @1.1.1.1 example.com AAAA\n" ++
  "  bender-dns --server 8.8.8.8 gmail.com MX\n" ++
  "  bender-dns --os localhost\n\n" ++
  "Prints one answer per line; exits 0 on success, 1 on error."

# Command line
# ------------

type Flag is Data:
  FPort{}
  FTimeout{}
  FAttempts{}
  FOs{}
  FServer{}
  FServerValue{}
  FHelp{}
  FUnknown{}
  FWord{}

def is_option(+a: String) -> Bool:
  (String.starts_with(a, "+") || String.starts_with(a, "-")) && Nat.is_lt(1n, String.length(a))

def flag(+a: String) -> Flag:
  Bool.pick(Flag, String.eq(a, "--port") || String.eq(a, "-p") || String.eq(a, "+tcp-port"), FPort{},
  Bool.pick(Flag, String.eq(a, "--timeout") || String.eq(a, "+timeout"), FTimeout{},
  Bool.pick(Flag, String.eq(a, "--attempts") || String.eq(a, "+attempts"), FAttempts{},
  Bool.pick(Flag, String.eq(a, "--server") || String.eq(a, "-s"), FServerValue{},
  Bool.pick(Flag, String.eq(a, "--help") || String.eq(a, "-h"), FHelp{},
  Bool.pick(Flag, String.eq(a, "--os"), FOs{},
  Bool.pick(Flag, String.starts_with(a, "@"), FServer{},
  Bool.pick(Flag, is_option(a), FUnknown{},
  FWord{}))))))))

type Opts is Data:
  Opts{servers: List<&2, String>, port: Maybe<&2, Nat>, timeout: Maybe<&2, Nat>, attempts: Maybe<&2, Nat>,
    os: Bool, name: Maybe<&2, String>, rtype: Maybe<&2, String>, bad: Maybe<&2, String>, help: Bool}

def opts0() -> Opts:
  Opts{Nil{}, None{}, None{}, None{}, False{}, None{}, None{}, None{}, False{}}

# The first complaint wins.
def complain(o: Opts, msg: String) -> Opts:
  match o:
    case Opts{s, p, t, at, os, n, ty, bad, help}:
      Opts{s, p, t, at, os, n, ty, Maybe.or(&2, String, bad, Some{msg}), help}

def drop1(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      t

# `a` is the value of the option `k`.
def value.of(m: Maybe<&2, Nat>, k: Flag, a: String, o: Opts) -> Opts:
  match m:
    case None{}:
      complain(o, "an option needs a number: " ++ a)
    case Some{n}:
      match k o:
        case FPort{} Opts{s, p, t, at, os, nm, ty, bad, help}:
          Opts{s, Some{n}, t, at, os, nm, ty, bad, help}
        case FTimeout{} Opts{s, p, t, at, os, nm, ty, bad, help}:
          Opts{s, p, Some{n}, at, os, nm, ty, bad, help}
        case FAttempts{} Opts{s, p, t, at, os, nm, ty, bad, help}:
          Opts{s, p, t, Some{n}, os, nm, ty, bad, help}
        case _ _:
          o

def server_value(ok: Bool, a: String, o: Opts) -> Opts:
  match ok o:
    case True{} Opts{s, p, t, at, os, nm, ty, bad, help}:
      Opts{a <> s, p, t, at, os, nm, ty, bad, help}
    case False{} _:
      complain(o, "server must be an IPv4 address: " ++ a)

def number_valid(k: Flag, +n: Nat) -> Bool:
  match k:
    case FPort{}:
      Nat.is_lt(0n, n) && Nat.is_le(n, 65535n)
    case FTimeout{}:
      Nat.is_lt(0n, n) && Nat.is_le(n, 4294967295n)
    case _:
      Nat.is_lt(0n, n)

def number_error(k: Flag) -> String:
  match k:
    case FPort{}:
      "port must be an integer from 1 to 65535"
    case FTimeout{}:
      "timeout must be an integer from 1 to 4294967295 (milliseconds)"
    case _:
      "attempts must be a positive integer"

def number_checked(ok: Bool, +k: Flag, n: Nat, a: String, o: Opts) -> Opts:
  match ok:
    case True{}:
      value.of(Some{n}, k, a, o)
    case False{}:
      complain(o, number_error(k) ++ ": " ++ a)

def number(m: Maybe<&2, Nat>, +k: Flag, a: String, o: Opts) -> Opts:
  match m:
    case None{}:
      complain(o, number_error(k) ++ ": " ++ a)
    case Some{+n}:
      number_checked(number_valid(k, n), k, n, a, o)

def value(+k: Flag, +a: String, o: Opts) -> Opts:
  match k:
    case FServerValue{}:
      server_value(P.Dns.Ip.is_ipv4(a), a, o)
    case _:
      number(Nat.read(a), k, a, o)

def positional(o: Opts, +a: String) -> Opts:
  match o:
    case Opts{s, p, t, at, os, nm, ty, bad, help}:
      match nm ty:
        case None{} _:
          Opts{s, p, t, at, os, Some{a}, ty, bad, help}
        case Some{x} None{}:
          Opts{s, p, t, at, os, Some{x}, Some{a}, bad, help}
        case Some{x} Some{y}:
          complain(Opts{s, p, t, at, os, Some{x}, Some{y}, bad, help}, "too many arguments: " ++ a)

# `a` is not an option's value.
def word(k: Flag, +a: String, o: Opts) -> Opts:
  match k o:
    case FOs{} Opts{s, p, t, at, os, nm, ty, bad, help}:
      Opts{s, p, t, at, True{}, nm, ty, bad, help}
    case FHelp{} Opts{s, p, t, at, os, nm, ty, bad, help}:
      Opts{s, p, t, at, os, nm, ty, bad, True{}}
    case FServer{} _:
      +server = drop1(a)
      server_value(P.Dns.Ip.is_ipv4(server), server, o)
    case FUnknown{} _:
      complain(o, "unknown option: " ++ a)
    case FWord{} _:
      positional(o, a)
    case _ _:
      o

def takes_value(k: Flag) -> Bool:
  match k:
    case FPort{}:
      True{}
    case FTimeout{}:
      True{}
    case FAttempts{}:
      True{}
    case FServerValue{}:
      True{}
    case _:
      False{}

def pending_after(waiting: Maybe<&2, Flag>, +a: String) -> Maybe<&2, Flag>:
  match waiting:
    case Some{p}:
      None{}
    case None{}:
      +k = flag(a)
      Bool.pick(Maybe<&2, Flag>, takes_value(k), Some{k}, None{})

def step(waiting: Maybe<&2, Flag>, +a: String, o: Opts) -> Opts:
  match waiting:
    case Some{p}:
      value(p, a, o)
    case None{}:
      word(flag(a), a, o)

def finish(waiting: Maybe<&2, Flag>, o: Opts) -> Opts:
  match waiting:
    case Some{p}:
      complain(o, "an option is missing its value")
    case None{}:
      o

def parse(args: List<String>, +waiting: Maybe<&2, Flag>, o: Opts) -> Opts:
  match args:
    case Nil{}:
      finish(waiting, o)
    case Con{+a, t}:
      parse(t, pending_after(waiting, a), step(waiting, a, o))

# Output
# ------

def die(msg: String) -> IO(Unit):
  IO.die(Unit, 1, "bender-dns: " ++ msg)

# Success: exit at once (see the top of the file).
def ok_exit() -> IO(Unit):
  IO.die(Unit, 0, "")

def print_lines(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{x, t}:
      do IO<Unit>:
        IO.print(x)
        print_lines(t)

def print_records(rs: List<&2, P.Dns.Record()>) -> IO(Unit):
  match rs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{r, t}:
      do IO<Unit>:
        IO.print(P.Dns.RData.show(P.Dns.Record.data(r)))
        print_records(t)

def same_name(asked: Result<&2, &2, P.Dns.NameError(), P.Dns.Name()>, n: P.Dns.Name()) -> Bool:
  match asked:
    case Done{a}:
      P.Dns.Name.eq(a, n)
    case Fail{e}:
      False{}

def print_owner(same: Bool, n: P.Dns.Name()) -> IO(Unit):
  match same:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.print(P.Dns.Name.fqdn(n))

def resolved(r: Result<&2, &2, P.Dns.Error(), P.Dns.Resolved()>, name: String) -> IO(Unit):
  match r:
    case Fail{e}:
      die(P.Dns.Error.show(e))
    case Done{+x}:
      +n = P.Dns.Resolved.name(x)
      do IO<Unit>:
        print_owner(same_name(P.Dns.Name.parse(name), n), n)
        print_records(P.Dns.Resolved.records(x))
        ok_exit()

def os_done(r: Result<&2, &2, P.Dns.Error(), List<&2, String>>) -> IO(Unit):
  match r:
    case Fail{e}:
      die(P.Dns.Error.show(e))
    case Done{ips}:
      do IO<Unit>:
        print_lines(ips)
        ok_exit()

# Running
# -------

def or_keep(m: Maybe<&2, Nat>, cfg: P.Dns.Config(), set: P.Dns.Config() -> Nat -> P.Dns.Config()) -> P.Dns.Config():
  match m:
    case Some{n}:
      set(cfg, n)
    case None{}:
      cfg

def servers_or_keep(s: List<&2, String>, cfg: P.Dns.Config()) -> P.Dns.Config():
  match s:
    case Nil{}:
      cfg
    case Con{h, t}:
      P.Dns.with_servers(cfg, List.reverse(&2, String, h <> t))

def configured(r: Result<&2, &2, P.Dns.Error(), P.Dns.Config()>, s: List<&2, String>, p: Maybe<&2, Nat>,
  t: Maybe<&2, Nat>, at: Maybe<&2, Nat>, +name: String, rtype: P.Dns.RType()) -> IO(Unit):
  match r:
    case Fail{e}:
      die(P.Dns.Error.show(e))
    case Done{cfg}:
      +c = or_keep(at, or_keep(t, or_keep(p, servers_or_keep(s, cfg), P.Dns.with_port), P.Dns.with_timeout),
        P.Dns.with_attempts)
      IO.bind(Result<&2, &2, P.Dns.Error(), P.Dns.Resolved()>, Unit, P.Dns.resolve(c, name, rtype),
        x => resolved(x, name))

def native(s: List<&2, String>, p: Maybe<&2, Nat>, t: Maybe<&2, Nat>, at: Maybe<&2, Nat>, name: String,
  rtype: P.Dns.RType()) -> IO(Unit):
  IO.bind(Result<&2, &2, P.Dns.Error(), P.Dns.Config()>, Unit, P.Dns.system(),
    r => configured(r, s, p, t, at, name, rtype))

def family.of(m: Maybe<&2, P.Dns.RType()>) -> Maybe<&2, U32>:
  match m:
    case Some{t}:
      +c = P.Dns.RType.code(t)
      Bool.pick(Maybe<&2, U32>, Nat.is_eq(c, 1n), Some{4},
      Bool.pick(Maybe<&2, U32>, Nat.is_eq(c, 28n), Some{6}, None{}))
    case None{}:
      None{}

def os_family(f: Maybe<&2, U32>, name: String) -> IO(Unit):
  match f:
    case Some{fam}:
      IO.bind(Result<&2, &2, P.Dns.Error(), List<&2, String>>, Unit, P.Dns.os_lookup(name, fam), r => os_done(r))
    case None{}:
      die("--os looks up addresses only (A or AAAA)")

def typed(o: Bool, ty: Maybe<&2, P.Dns.RType()>, given: Bool, s: List<&2, String>, p: Maybe<&2, Nat>,
  t: Maybe<&2, Nat>, at: Maybe<&2, Nat>, +name: String) -> IO(Unit):
  match o given:
    case True{} False{}:
      IO.bind(Result<&2, &2, P.Dns.Error(), List<&2, String>>, Unit, P.Dns.os_lookup(name, 0), r => os_done(r))
    case True{} True{}:
      os_family(family.of(ty), name)
    case False{} _:
      match ty:
        case Some{rt}:
          native(s, p, t, at, name, rt)
        case None{}:
          native(s, p, t, at, name, P.Dns.A())

def has_number(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def has_servers(s: List<&2, String>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case Con{h, t}:
      True{}

def parsed_type(r: Maybe<&2, P.Dns.RType()>, ty: String, o: Bool, s: List<&2, String>, p: Maybe<&2, Nat>,
  t: Maybe<&2, Nat>, at: Maybe<&2, Nat>, +name: String) -> IO(Unit):
  match r:
    case None{}:
      die("unknown type: " ++ ty)
    case Some{rt}:
      typed(o, Some{rt}, True{}, s, p, t, at, name)

def with_type(m: Maybe<&2, String>, o: Bool, s: List<&2, String>, p: Maybe<&2, Nat>, t: Maybe<&2, Nat>,
  at: Maybe<&2, Nat>, +name: String) -> IO(Unit):
  match m:
    case None{}:
      typed(o, None{}, False{}, s, p, t, at, name)
    case Some{+ty}:
      parsed_type(P.Dns.RType.parse(ty), ty, o, s, p, t, at, name)

def run_query(conflict: Bool, ty: Maybe<&2, String>, os: Bool, s: List<&2, String>, p: Maybe<&2, Nat>,
  t: Maybe<&2, Nat>, at: Maybe<&2, Nat>, name: String) -> IO(Unit):
  match conflict:
    case True{}:
      die("--os cannot be combined with server, port, timeout or attempt options")
    case False{}:
      with_type(ty, os, s, p, t, at, name)

def run(o: Opts) -> IO(Unit):
  match o:
    case Opts{+s, +p, +t, +at, +os, nm, ty, bad, help}:
      match nm bad help:
        case _ _ True{}:
          IO.print(help_text())
        case _ Some{msg} False{}:
          die(msg ++ "\n" ++ usage())
        case None{} None{} False{}:
          die(usage())
        case Some{name} None{} False{}:
          run_query(os && (has_servers(s) || has_number(p) || has_number(t) || has_number(at)),
            ty, os, s, p, t, at, name)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(parse(List.tail(&1, String, args), None{}, opts0()))
