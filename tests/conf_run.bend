import Base
import ../src/types.bend as M
import ../src/conf.bend as CF

# Runtime tests for conf.bend on both lanes, at sizes the JS lane's stack
# cannot nest (it overflows near 20-40k calls), then the machine's own
# /etc/resolv.conf and /etc/hosts read with File.read:
#   bend tests/conf_run.bend
#   bend tests/conf_run.bend -o "$BEND_OUT/conf_run" && "$BEND_OUT/conf_run"
# Prints PASS / FAIL per case (the real files' parse is printed too), then
# "ALL PASS" or "SOME FAIL". The helpers here are loops too.

# Builders and checks (loops)
# ---------------------------

# n copies of c, prepended to acc.
def chars.go(n: Nat, +c: Char, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      chars.go(p, c, SCon{c, acc})

# n copies of the (short) text s, prepended to acc.
def rep.go(n: Nat, +s: String, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      rep.go(p, s, s ++ acc)

# n copies of the word w, prepended to acc.
def words.go(n: Nat, +w: String, acc: List<&2, String>) -> List<&2, String>:
  match n:
    case 0n:
      acc
    case 1n+p:
      words.go(p, w, w <> acc)

def slen.go(s: String, n: Nat) -> Nat:
  match s:
    case SNil{}:
      n
    case SCon{c, t}:
      slen.go(t, 1n+n)

def len.go(-A: Data, xs: List<&2, A>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      len.go(A, t, 1n+n)

def str_eq.go(a: String, b: String, ok: Bool) -> Bool:
  match a b:
    case SNil{} SNil{}:
      ok
    case SCon{x, xs} SCon{y, ys}:
      str_eq.go(xs, ys, ok && Char.is_eq(x, y))
    case _ _:
      False{}

def strs_eq(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      String.eq(x, y) && strs_eq(xs, ys)
    case _ _:
      False{}

def conf_is(c: M.Conf, ns: List<&2, String>, ss: List<&2, String>, nd: Nat, t: Nat, a: Nat) -> Bool:
  match c:
    case M.Conf{ns2, ss2, nd2, t2, a2}:
      strs_eq(ns2, ns) && strs_eq(ss2, ss) && Nat.is_eq(nd2, nd) && Nat.is_eq(t2, t)
        && Nat.is_eq(a2, a)

def search_len(c: M.Conf) -> Nat:
  match c:
    case M.Conf{ns, ss, nd, t, a}:
      len.go(String, ss, 0n)

def second_len(xs: List<&2, String>) -> Nat:
  match xs:
    case Con{a, Con{b, t}}:
      slen.go(b, 0n)
    case _:
      0n

def K200() -> Nat:
  200000n

def K50() -> Nat:
  50000n

# A 50k-line hosts file (two names per line), then one more entry.
def big_hosts() -> String:
  rep.go(K50(), "10.0.0.1 h1  H2\t# a comment\n", "10.9.9.9 Target.Example\n")

def big_search() -> M.Conf:
  M.Conf{Nil{}, words.go(K50(), "s.example", Nil{}), 1n, 5n, 2n}

def dflt() -> M.Conf:
  M.Conf{Nil{}, Nil{}, 1n, 5n, 2n}

# The cases
# ---------

def cases() -> List<(String & Bool)>:
  [
    ("lines 200k-char word", Nat.is_eq(len.go(List<&2, String>, CF.lines(chars.go(K200(), 'w', SNil{}), True{}), 0n), 1n)),
    ("resolv 50k comment lines, then a nameserver",
      conf_is(CF.resolv(rep.go(K50(), "# comment line\n", "nameserver 1.2.3.4\n")), ["1.2.3.4"], Nil{}, 1n, 5n, 2n)),
    ("resolv 50k nameserver lines keep 3",
      conf_is(CF.resolv(rep.go(K50(), "nameserver 9.9.9.9\n", SNil{})), ["9.9.9.9", "9.9.9.9", "9.9.9.9"], Nil{}, 1n, 5n, 2n)),
    ("resolv 200k-char nameserver word",
      conf_is(CF.resolv("nameserver " ++ chars.go(K200(), '1', SNil{})), Nil{}, Nil{}, 1n, 5n, 2n)),
    ("resolv ndots of 200k nines clamps to 15",
      conf_is(CF.resolv("options ndots:" ++ chars.go(K200(), '9', "\n")), Nil{}, Nil{}, 15n, 5n, 2n)),
    ("resolv ndots of 200k zeros then 3",
      conf_is(CF.resolv("options ndots:" ++ chars.go(K200(), '0', "3")), Nil{}, Nil{}, 3n, 5n, 2n)),
    ("resolv ndots:999999999999 timeout:99999999999999 attempts:4294967296",
      conf_is(CF.resolv("options ndots:999999999999 timeout:99999999999999 attempts:4294967296"), Nil{}, Nil{}, 15n, 30n, 5n)),
    ("resolv 50k options words",
      conf_is(CF.resolv("options " ++ rep.go(K50(), "rotate ", "ndots:4")), Nil{}, Nil{}, 4n, 5n, 2n)),
    ("resolv search of 50k domains",
      Nat.is_eq(search_len(CF.resolv("search " ++ rep.go(K50(), "a.example ", SNil{}))), K50())),
    ("hosts 50k lines", Nat.is_eq(len.go(M.HostEntry, CF.hosts(big_hosts()), 0n), 1n+K50())),
    ("hosts_lookup last of 50k", strs_eq(CF.hosts_lookup(CF.hosts(big_hosts()), "target.EXAMPLE"), ["10.9.9.9"])),
    ("hosts_lookup 50k hits", Nat.is_eq(len.go(String, CF.hosts_lookup(CF.hosts(big_hosts()), "h2"), 0n), K50())),
    ("hosts_lookup 200k-char name", strs_eq(CF.hosts_lookup(CF.hosts(big_hosts()), chars.go(K200(), 'h', SNil{})), Nil{})),
    ("hosts 200k-char name", Nat.is_eq(len.go(String, CF.hosts_lookup(CF.hosts("1.1.1.1 " ++ chars.go(K200(), 'N', SNil{})), chars.go(K200(), 'n', SNil{})), 0n), 1n)),
    ("lower 200k", str_eq.go(CF.lower(chars.go(K200(), 'Q', SNil{})), chars.go(K200(), 'q', SNil{}), True{})),
    ("candidates 50k suffixes", Nat.is_eq(len.go(String, CF.candidates(big_search(), "h"), 0n), 1n+K50())),
    ("candidates 100k-char name, 50k dots",
      Nat.is_eq(len.go(String, CF.candidates(dflt(), rep.go(K50(), "a.", "b")), 0n), 1n)),
    ("candidates 200k-char name with a suffix",
      Nat.is_eq(second_len(CF.candidates(M.Conf{Nil{}, ["x.y."], 1n, 5n, 2n}, chars.go(K200(), 'a', ".b"))), 200006n)),
    ("candidates 200k-char absolute name",
      Nat.is_eq(len.go(String, CF.candidates(big_search(), chars.go(K200(), 'a', ".")), 0n), 1n))
  ]

def report(xs: List<(String & Bool)>, fails: Nat) -> IO(Nat):
  match xs:
    case Nil{}:
      IO.pure(Nat, fails)
    case Con{c, t}:
      match c:
        case (name, ok):
          match ok:
            case True{}:
              do IO<Nat>:
                IO.print("PASS " ++ name)
                report(t, fails)
            case False{}:
              do IO<Nat>:
                IO.print("FAIL " ++ name)
                report(t, 1n+fails)

# The real files
# --------------

def R() -> Type:
  Result<&1, &1, U32 & String, String>

def read.close(p: File & R()) -> IO(R()):
  (f, r) = p
  IO.bind(Unit, R(), File.close(f), u => IO.pure(R(), r))

def read.opened(r: Result<&1, &1, U32 & String, File>) -> IO(R()):
  match r:
    case Fail{e}:
      IO.pure(R(), Fail{e})
    case Done{f}:
      IO.bind(File & R(), R(), File.read(f, 4194304), p => read.close(p))

# The text of the file at path (at most 4 MiB).
def read_file(path: String) -> IO(R()):
  IO.bind(Result<&1, &1, U32 & String, File>, R(), File.open(path, "r"), r => read.opened(r))

def show_conf(c: M.Conf) -> String:
  match c:
    case M.Conf{ns, ss, nd, t, a}:
      "nameservers [" ++ String.join(ns, ", ") ++ "] search [" ++ String.join(ss, ", ")
        ++ "] ndots " ++ Nat.show(nd) ++ " timeout " ++ Nat.show(t) ++ " attempts " ++ Nat.show(a)

def real_resolv(r: R(), fails: Nat) -> IO(Nat):
  match r:
    case Fail{e}:
      (code, m) = e
      do IO<Nat>:
        IO.print("SKIP real /etc/resolv.conf: error " ++ U32.show(code) ++ ": " ++ m)
        return fails
    case Done{text}:
      do IO<Nat>:
        IO.print("PASS real /etc/resolv.conf: " ++ show_conf(CF.resolv(text)))
        return fails

def real_hosts.found(ips: List<&2, String>, n: Nat, fails: Nat) -> IO(Nat):
  match ips:
    case Nil{}:
      do IO<Nat>:
        IO.print("FAIL real /etc/hosts: " ++ Nat.show(n) ++ " entries, no localhost")
        return 1n+fails
    case Con{h, t}:
      do IO<Nat>:
        IO.print("PASS real /etc/hosts: " ++ Nat.show(n) ++ " entries, localhost is "
          ++ String.join(Con{h, t}, ", "))
        return fails

def real_hosts(r: R(), fails: Nat) -> IO(Nat):
  match r:
    case Fail{e}:
      (code, m) = e
      do IO<Nat>:
        IO.print("SKIP real /etc/hosts: error " ++ U32.show(code) ++ ": " ++ m)
        return fails
    case Done{text}:
      +es = CF.hosts(text)
      real_hosts.found(CF.hosts_lookup(es, "localhost"), len.go(M.HostEntry, es, 0n), fails)

def finish(fails: Nat) -> IO(Unit):
  match fails:
    case 0n:
      IO.print("ALL PASS")
    case 1n+p:
      IO.print("SOME FAIL: " ++ Nat.show(1n+p))

def main() -> IO(Unit):
  do IO<Unit>:
    f0 : Nat <- report(cases(), 0n)
    rc : R() <- read_file("/etc/resolv.conf")
    f1 : Nat <- real_resolv(rc, f0)
    hs : R() <- read_file("/etc/hosts")
    f2 : Nat <- real_hosts(hs, f1)
    finish(f2)
