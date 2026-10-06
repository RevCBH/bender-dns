import Base
import ../src/os.bend as O

# Os.lookup on both lanes: input checks, numeric hosts, literals, and real
# lookups (localhost from /etc/hosts; example.com and ipv6.google.com need
# the network and a working resolver).
#   bend tests/os_run.bend
#   bend tests/os_run.bend -o "$BEND_OUT/os_run" && "$BEND_OUT/os_run"
# Prints PASS / FAIL per case with what the resolver answered, then
# "ALL PASS" or "SOME FAIL".

def R() -> Type:
  Result<&1, &1, U32 & String, List<&2, String>>

type Want is Data:
  Code{code: U32}               # this failure
  NotCode{code: U32}            # a failure, but not this one
  Fails{}                       # any failure
  Addrs{ips: List<&2, String>}  # exactly these addresses
  Has{ip: String}               # the addresses include this one
  HasV4{ip: String}             # ... and are all IPv4 text
  HasV6{ip: String}             # ... and are all IPv6 text
  AllV4{}                       # one or more, all IPv4 text
  AllV6{}                       # one or more, all IPv6 text
  Both{}                        # at least one IPv4 and one IPv6 address

def strings_eq(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, s} Con{y, t}:
      String.eq(x, y) && strings_eq(s, t)
    case _ _:
      False{}

def has(+ip: String, ips: List<&2, String>) -> Bool:
  match ips:
    case Nil{}:
      False{}
    case Con{x, t}:
      String.eq(ip, x) || has(ip, t)

def is_v6(s: String) -> Bool:
  String.contains(s, ":")

def all_v4(ips: List<&2, String>) -> Bool:
  match ips:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.not(is_v6(x)) && all_v4(t)

def all_v6(ips: List<&2, String>) -> Bool:
  match ips:
    case Nil{}:
      True{}
    case Con{x, t}:
      is_v6(x) && all_v6(t)

def any_v4(ips: List<&2, String>) -> Bool:
  match ips:
    case Nil{}:
      False{}
    case Con{x, t}:
      Bool.not(is_v6(x)) || any_v4(t)

def any_v6(ips: List<&2, String>) -> Bool:
  match ips:
    case Nil{}:
      False{}
    case Con{x, t}:
      is_v6(x) || any_v6(t)

def nonempty(ips: List<&2, String>) -> Bool:
  match ips:
    case Nil{}:
      False{}
    case Con{x, t}:
      True{}

def want_code(w: Want, +c: U32) -> Bool:
  match w:
    case Code{k}:
      U32.is_eq(k, c)
    case NotCode{k}:
      Bool.not(U32.is_eq(k, c))
    case Fails{}:
      True{}
    case _:
      False{}

def want_ips(w: Want, +ips: List<&2, String>) -> Bool:
  match w:
    case Addrs{xs}:
      strings_eq(xs, ips)
    case Has{x}:
      has(x, ips)
    case HasV4{x}:
      has(x, ips) && all_v4(ips)
    case HasV6{x}:
      has(x, ips) && all_v6(ips)
    case AllV4{}:
      nonempty(ips) && all_v4(ips)
    case AllV6{}:
      nonempty(ips) && all_v6(ips)
    case Both{}:
      any_v4(ips) && any_v6(ips)
    case _:
      False{}

def verdict(name: String, ok: Bool, got: String, fails: Nat) -> IO(Nat):
  match ok:
    case True{}:
      do IO<Nat>:
        IO.print("PASS " ++ name ++ " (" ++ got ++ ")")
        return fails
    case False{}:
      do IO<Nat>:
        IO.print("FAIL " ++ name ++ ": got " ++ got)
        return 1n+fails

def expect(name: String, w: Want, r: R(), fails: Nat) -> IO(Nat):
  match r:
    case Fail{e}:
      (c, m) = e
      +k = c
      verdict(name, want_code(w, k), "error " ++ U32.show(k) ++ ": " ++ m, fails)
    case Done{ips}:
      +xs = ips
      verdict(name, want_ips(w, xs), String.join(xs, ", "), fails)

def check(name: String, host: String, family: U32, w: Want, fails: Nat) -> IO(Nat):
  IO.bind(R(), Nat, O.Os.lookup(host, family), r => expect(name, w, r, fails))

def finish(fails: Nat) -> IO(Unit):
  match fails:
    case 0n:
      IO.print("ALL PASS")
    case 1n+p:
      IO.print("SOME FAIL: " ++ Nat.show(1n+p))

def main() -> IO(Unit):
  do IO<Unit>:
    f : Nat = 0n
    # input checks
    f : Nat <- check("empty name", "", 0, Code{22}, f)
    f : Nat <- check("empty name, family 6", "", 6, Code{22}, f)
    f : Nat <- check("name with NUL", "a\0b", 0, Code{22}, f)
    f : Nat <- check("bad family 5", "localhost", 5, Code{22}, f)
    f : Nat <- check("bad family 2 (AF_INET's own number)", "localhost", 2, Code{22}, f)
    f : Nat <- check("bad family 10 (AF_INET6's own number)", "localhost", 10, Code{22}, f)
    f : Nat <- check("bad family 4294967295", "localhost", 4294967295, Code{22}, f)
    # numeric hosts that are not canonical dotted quads, every family
    f : Nat <- check("short form 127.1", "127.1", 0, Code{22}, f)
    f : Nat <- check("short form 127.1, family 4", "127.1", 4, Code{22}, f)
    f : Nat <- check("short form 127.1, family 6", "127.1", 6, Code{22}, f)
    f : Nat <- check("bare number 2130706433", "2130706433", 0, Code{22}, f)
    f : Nat <- check("hex 0x7f.1", "0x7f.1", 4, Code{22}, f)
    f : Nat <- check("octal 010.0.0.1", "010.0.0.1", 0, Code{22}, f)
    f : Nat <- check("leading zero 127.0.0.010", "127.0.0.010", 6, Code{22}, f)
    f : Nat <- check("trailing dot makes 127.1. a name", "127.1.", 0, NotCode{22}, f)
    # literals
    f : Nat <- check("canonical 1.2.3.4", "1.2.3.4", 0, Addrs{["1.2.3.4"]}, f)
    f : Nat <- check("canonical 1.2.3.4, family 4", "1.2.3.4", 4, Addrs{["1.2.3.4"]}, f)
    f : Nat <- check("canonical 1.2.3.4, family 6 (not mapped)", "1.2.3.4", 6, Fails{}, f)
    f : Nat <- check("::1", "::1", 0, Addrs{["::1"]}, f)
    f : Nat <- check("::1, family 6", "::1", 6, Addrs{["::1"]}, f)
    f : Nat <- check("::1, family 4", "::1", 4, Fails{}, f)
    f : Nat <- check("2001:DB8:0:0:0:0:0:1 prints as 2001:db8::1", "2001:DB8:0:0:0:0:0:1", 6, Addrs{["2001:db8::1"]}, f)
    f : Nat <- check("::ffff:1.2.3.4", "::ffff:1.2.3.4", 6, Addrs{["::ffff:1.2.3.4"]}, f)
    f : Nat <- check("2001:db8:0:0:1:0:0:1", "2001:db8:0:0:1:0:0:1", 0, Addrs{["2001:db8::1:0:0:1"]}, f)
    # localhost (/etc/hosts)
    f : Nat <- check("localhost", "localhost", 0, Has{"127.0.0.1"}, f)
    f : Nat <- check("localhost, family 4", "localhost", 4, HasV4{"127.0.0.1"}, f)
    f : Nat <- check("localhost, family 6", "localhost", 6, HasV6{"::1"}, f)
    # the network
    f : Nat <- check("example.com", "example.com", 0, Both{}, f)
    f : Nat <- check("example.com, family 4", "example.com", 4, AllV4{}, f)
    f : Nat <- check("example.com, family 6", "example.com", 6, AllV6{}, f)
    f : Nat <- check("ipv6.google.com, family 6", "ipv6.google.com", 6, AllV6{}, f)
    f : Nat <- check("ipv6.google.com, family 4 (IPv6-only name)", "ipv6.google.com", 4, Code{2}, f)
    f : Nat <- check("ipv6.google.com, family 0", "ipv6.google.com", 0, AllV6{}, f)
    f : Nat <- check("nonexistent name", "no-such-host.bender-dns.invalid", 0, Code{2}, f)
    f : Nat <- check("nonexistent name, family 6", "no-such-host.bender-dns.invalid", 6, Code{2}, f)
    finish(f)
