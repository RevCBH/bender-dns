import Base
import ../main.bend as P

# bend examples/host.bend -- name [server]
#
# Like host(1) without options: the name's A and AAAA records through the
# native stack (/etc/resolv.conf and /etc/hosts; `server`, an IPv4
# address, replaces the nameservers):
#
#   www.github.com is an alias for github.com.
#   github.com has address 140.82.121.3
#   example.com has IPv6 address 2600:1406:3a00:21::173e:2e65
#
# A name that does not exist prints "Host NAME not found: 3(NXDOMAIN)" and
# exits with 1; a name with neither type prints "NAME has no A or AAAA
# record". Any other failure (a timeout, a server failure) prints why and
# exits with 1, after whatever the other type found. Every exit is explicit
# (IO.die; on success with 0 and one empty line on stderr), so a read that
# timed out, which Base cannot cancel, does not hold the program open.
#
#   bend examples/host.bend -- example.com
#   bend examples/host.bend -- www.github.com 1.1.1.1

def R() -> Data:
  Result<&2, &2, P.Dns.Error(), P.Dns.Resolved()>

def die(msg: String) -> IO(Unit):
  IO.die(Unit, 1, msg)

def ok_exit() -> IO(Unit):
  IO.die(Unit, 0, "")

# The owner as host prints it in "has address" lines (no trailing dot).
def owner_text(n: P.Dns.Name()) -> String:
  P.Dns.Name.show(n)

def print_addrs(rs: List<&2, P.Dns.Record()>, +who: String, +what: String) -> IO(Unit):
  match rs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{r, t}:
      do IO<Unit>:
        IO.print(who ++ " " ++ what ++ " " ++ P.Dns.RData.show(P.Dns.Record.data(r)))
        print_addrs(t, who, what)

def print_found(r: R(), what: String) -> IO(Unit):
  match r:
    case Done{+x}:
      print_addrs(P.Dns.Resolved.records(x), owner_text(P.Dns.Resolved.name(x)), what)
    case Fail{e}:
      IO.pure(Unit, Unit{})

def asked_eq(asked: Result<&2, &2, P.Dns.NameError(), P.Dns.Name()>, n: P.Dns.Name()) -> Bool:
  match asked:
    case Done{a}:
      P.Dns.Name.eq(a, n)
    case Fail{e}:
      True{}

def alias_line(same: Bool, name: String, n: P.Dns.Name()) -> IO(Unit):
  match same:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.print(name ++ " is an alias for " ++ P.Dns.Name.fqdn(n))

# The alias line, from the first answer that found records.
def print_alias(a: R(), b: R(), +name: String) -> IO(Unit):
  match a b:
    case Done{+x} _:
      +n = P.Dns.Resolved.name(x)
      alias_line(asked_eq(P.Dns.Name.parse(name), n), name, n)
    case Fail{e} Done{+x}:
      +n = P.Dns.Resolved.name(x)
      alias_line(asked_eq(P.Dns.Name.parse(name), n), name, n)
    case Fail{e} Fail{f}:
      IO.pure(Unit, Unit{})

def kind_nodata(k: P.Dns.ErrorKind()) -> Bool:
  match k:
    case P.NoData{}:
      True{}
    case _:
      False{}

def kind_nx(k: P.Dns.ErrorKind()) -> Bool:
  match k:
    case P.NxDomain{}:
      True{}
    case _:
      False{}

def is_nodata(e: P.Dns.Error()) -> Bool:
  kind_nodata(P.Dns.Error.kind(e))

def is_nx(e: P.Dns.Error()) -> Bool:
  kind_nx(P.Dns.Error.kind(e))

def soft(r: R()) -> Bool:
  match r:
    case Done{x}:
      True{}
    case Fail{e}:
      is_nodata(e)

# After printing: a failure other than NoData ends with it.
def verdict(a: R(), b: R(), +name: String) -> IO(Unit):
  match a b:
    case Fail{+e} Fail{+f}:
      Bool.pick(IO(Unit), is_nx(e), die("Host " ++ name ++ " not found: 3(NXDOMAIN)"),
      Bool.pick(IO(Unit), is_nodata(e) && is_nodata(f), IO.bind(Unit, Unit, IO.print(name ++ " has no A or AAAA record"), u => ok_exit()),
      Bool.pick(IO(Unit), is_nodata(e), die("host: " ++ P.Dns.Error.show(f)),
      die("host: " ++ P.Dns.Error.show(e)))))
    case Fail{+e} Done{x}:
      Bool.pick(IO(Unit), is_nodata(e), ok_exit(), die("host: " ++ P.Dns.Error.show(e)))
    case Done{x} Fail{+f}:
      Bool.pick(IO(Unit), is_nodata(f), ok_exit(), die("host: " ++ P.Dns.Error.show(f)))
    case Done{x} Done{y}:
      ok_exit()

def report(+a: R(), +b: R(), +name: String) -> IO(Unit):
  do IO<Unit>:
    print_alias(a, b, name)
    print_found(a, "has address")
    print_found(b, "has IPv6 address")
    verdict(a, b, name)

def asked(+cfg: P.Dns.Config(), +name: String) -> IO(Unit):
  do IO<Unit>:
    a : R() <- P.Dns.resolve(cfg, name, P.Dns.A())
    b : R() <- P.Dns.resolve(cfg, name, P.Dns.AAAA())
    report(a, b, name)

def configured(r: Result<&2, &2, P.Dns.Error(), P.Dns.Config()>, server: Maybe<&2, String>, +name: String) ->
  IO(Unit):
  match r:
    case Fail{e}:
      die("host: " ++ P.Dns.Error.show(e))
    case Done{cfg}:
      match server:
        case Some{s}:
          asked(P.Dns.with_servers(cfg, [s]), name)
        case None{}:
          asked(cfg, name)

def start(name: String, server: Maybe<&2, String>) -> IO(Unit):
  IO.bind(Result<&2, &2, P.Dns.Error(), P.Dns.Config()>, Unit, P.Dns.system(), r => configured(r, server, name))

def run(args: List<String>) -> IO(Unit):
  match args:
    case Con{name, Nil{}}:
      start(name, None{})
    case Con{name, Con{server, Nil{}}}:
      start(name, Some{server})
    case _:
      die("usage: host name [server]")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(List.tail(&1, String, args))
