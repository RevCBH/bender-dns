import Base
import ../main.bend as P

# bend examples/dig.bend -- [@server]... [--port N] [+timeout MS] [+attempts N] [--os] name [type]
#
# Looks name up and prints the answer like `dig +short`: one line per
# record, in presentation form ("93.184.215.14", "10 smtp.google.com.",
# "\"v=spf1 ...\""), preceded by the owner name ("github.com.") when the
# records belong to another name than the one asked (a CNAME was followed,
# or a search suffix applied). The type is A by default (any name dig
# knows: A, AAAA, MX, TXT, NS, CNAME, SOA, PTR, SRV, ANY, TYPEnnn).
#
# The native stack, configured from /etc/resolv.conf and /etc/hosts:
# @server (repeatable) replaces the nameservers, --port (or dig's
# +tcp-port) the port (53),
# +timeout each step's limit in ms (default: resolv.conf's timeout),
# +attempts the tries per server. --os asks the OS resolver (getaddrinfo)
# instead: A, AAAA, or both when no type is given; it prints addresses only.
# On failure it prints why and exits with 1; on success it exits with 0.
# Both exits are explicit (IO.die), so a read that timed out on an earlier
# server, which Base cannot cancel, does not hold the program open (the
# success exit writes one empty line to stderr).
#
#   bend examples/dig.bend -- example.com
#   bend examples/dig.bend -- @1.1.1.1 gmail.com MX
#   bend examples/dig.bend -- --os example.com AAAA

def usage() -> String:
  "usage: dig [@server]... [--port N] [+timeout MS] [+attempts N] [--os] name [type]"

# Command line
# ------------

type Flag is Data:
  FPort{}
  FTimeout{}
  FAttempts{}
  FOs{}
  FServer{}
  FUnknown{}
  FWord{}

def is_option(+a: String) -> Bool:
  (String.starts_with(a, "+") || String.starts_with(a, "-")) && Nat.is_lt(1n, String.length(a))

def flag(+a: String) -> Flag:
  Bool.pick(Flag, String.eq(a, "--port") || String.eq(a, "+tcp-port"), FPort{},
  Bool.pick(Flag, String.eq(a, "+timeout"), FTimeout{},
  Bool.pick(Flag, String.eq(a, "+attempts"), FAttempts{},
  Bool.pick(Flag, String.eq(a, "--os"), FOs{},
  Bool.pick(Flag, String.starts_with(a, "@"), FServer{},
  Bool.pick(Flag, is_option(a), FUnknown{},
  FWord{}))))))

type Opts is Data:
  Opts{servers: List<&2, String>, port: Maybe<&2, Nat>, timeout: Maybe<&2, Nat>, attempts: Maybe<&2, Nat>,
    os: Bool, name: Maybe<&2, String>, rtype: Maybe<&2, String>, bad: Maybe<&2, String>}

def opts0() -> Opts:
  Opts{Nil{}, None{}, None{}, None{}, False{}, None{}, None{}, None{}}

# The first complaint wins.
def complain(o: Opts, msg: String) -> Opts:
  match o:
    case Opts{s, p, t, at, os, n, ty, bad}:
      Opts{s, p, t, at, os, n, ty, Maybe.or(&2, String, bad, Some{msg})}

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
        case FPort{} Opts{s, p, t, at, os, nm, ty, bad}:
          Opts{s, Some{n}, t, at, os, nm, ty, bad}
        case FTimeout{} Opts{s, p, t, at, os, nm, ty, bad}:
          Opts{s, p, Some{n}, at, os, nm, ty, bad}
        case FAttempts{} Opts{s, p, t, at, os, nm, ty, bad}:
          Opts{s, p, t, Some{n}, os, nm, ty, bad}
        case _ _:
          o

def value(k: Flag, +a: String, o: Opts) -> Opts:
  value.of(Nat.read(a), k, a, o)

def positional(o: Opts, +a: String) -> Opts:
  match o:
    case Opts{s, p, t, at, os, nm, ty, bad}:
      match nm ty:
        case None{} _:
          Opts{s, p, t, at, os, Some{a}, ty, bad}
        case Some{x} None{}:
          Opts{s, p, t, at, os, Some{x}, Some{a}, bad}
        case Some{x} Some{y}:
          complain(Opts{s, p, t, at, os, Some{x}, Some{y}, bad}, "too many arguments: " ++ a)

# `a` is not an option's value.
def word(k: Flag, +a: String, o: Opts) -> Opts:
  match k o:
    case FOs{} Opts{s, p, t, at, os, nm, ty, bad}:
      Opts{s, p, t, at, True{}, nm, ty, bad}
    case FServer{} Opts{s, p, t, at, os, nm, ty, bad}:
      Opts{drop1(a) <> s, p, t, at, os, nm, ty, bad}
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
  IO.die(Unit, 1, "dig: " ++ msg)

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

def is_some(m: Maybe<&2, String>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

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

def run(o: Opts) -> IO(Unit):
  match o:
    case Opts{s, p, t, at, os, nm, ty, bad}:
      match nm bad:
        case _ Some{msg}:
          die(msg ++ "\n" ++ usage())
        case None{} None{}:
          die(usage())
        case Some{name} None{}:
          with_type(ty, os, s, p, t, at, name)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(parse(List.tail(&1, String, args), None{}, opts0()))
