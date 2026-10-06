import Base
import ../src/types.bend as M
import ../src/conf.bend as CF

# Checker-evaluated tests for conf.bend: `bend tests/conf_test.bend` (or
# --check-only) printing ALL PROOFS CHECK is a pass.

def C() -> Data:
  M.Conf

def SS() -> Data:
  List<&2, String>

def dflt() -> M.Conf:
  M.Conf{Nil{}, Nil{}, 1n, 5n, 2n}

def ns(xs: List<&2, String>) -> M.Conf:
  M.Conf{xs, Nil{}, 1n, 5n, 2n}

def srch(xs: List<&2, String>) -> M.Conf:
  M.Conf{Nil{}, xs, 1n, 5n, 2n}

def opts(nd: Nat, t: Nat, a: Nat) -> M.Conf:
  M.Conf{Nil{}, Nil{}, nd, t, a}

# A typical systemd-resolved stub file.
def stub() -> String:
  "# This is /run/systemd/resolve/stub-resolv.conf managed by man:systemd-resolved(8).\n# Do not edit.\n#\n\nnameserver 127.0.0.53\noptions edns0 trust-ad\nsearch .\n"

# A messy file: leading whitespace, tabs, CRLF, comments of both kinds,
# trailing comments, blank lines, no final newline.
def messy() -> String:
  "   \n\t# comment\n; another comment\r\n  nameserver\t 10.0.0.1  \r\n\tnameserver 10.0.0.2# after\nnameserver   10.0.0.3;after\n\n\nsearch\tcorp.example   lab.example\t # the search list\r\noptions\tndots:2 \t timeout:3   attempts:4"

def hosts_text() -> String:
  "# /etc/hosts\n127.0.0.1\tlocalhost\n::1     localhost ip6-localhost ip6-loopback  # v6\n\n  10.1.2.3   Web.Example  web   \n10.1.2.4\tweb.example\n# 10.9.9.9 commented.example\n10.1.2.5\n192.168.0.1 router;x\r\n10.1.2.6 WEB.EXAMPLE"

def entries() -> List<&2, M.HostEntry>:
  CF.hosts(hosts_text())

def main() ->
  # lines of words
  {CF.lines("", True{}) == Nil{} : List<&2, SS()>} &
  {CF.lines("a b\nc", True{}) == [["a", "b"], ["c"]] : List<&2, SS()>} &
  {CF.lines("\n\n  \t\r\n", True{}) == Nil{} : List<&2, SS()>} &
  {CF.lines(" a\t\tb \r\n# x y\n c ;d\n", True{}) == [["a", "b"], ["c"]] : List<&2, SS()>} &
  {CF.lines("a;b # c\n", False{}) == [["a;b"]] : List<&2, SS()>} &
  {CF.lines("a#b\nc", False{}) == [["a"], ["c"]] : List<&2, SS()>} &
  # IPv4 text
  {CF.is_ipv4("1.2.3.4") == True{} : Bool} &
  {CF.is_ipv4("0.0.0.0") == True{} : Bool} &
  {CF.is_ipv4("255.255.255.255") == True{} : Bool} &
  {CF.is_ipv4("256.1.1.1") == False{} : Bool} &
  {CF.is_ipv4("01.2.3.4") == False{} : Bool} &
  {CF.is_ipv4("1.2.3") == False{} : Bool} &
  {CF.is_ipv4("1.2.3.4.5") == False{} : Bool} &
  {CF.is_ipv4("1.2.3.4.") == False{} : Bool} &
  {CF.is_ipv4("1..3.4") == False{} : Bool} &
  {CF.is_ipv4("1.2.3.x") == False{} : Bool} &
  {CF.is_ipv4("1.2.3.4444") == False{} : Bool} &
  {CF.is_ipv4("1111.2.3.4") == False{} : Bool} &
  {CF.is_ipv4("999999999999999999") == False{} : Bool} &
  {CF.is_ipv4("::1") == False{} : Bool} &
  {CF.is_ipv4("") == False{} : Bool} &
  # lowercase
  {CF.lower("WeB.ExAmPlE-1") == "web.example-1" : String} &
  {CF.lower("\u{c0}Z@[") == "\u{c0}z@[" : String} &
  # resolv: defaults and nameservers
  {CF.resolv("") == dflt() : C()} &
  {CF.resolv("# nothing\n; here\n") == dflt() : C()} &
  {CF.resolv("nameserver 8.8.8.8\n") == ns(["8.8.8.8"]) : C()} &
  {CF.resolv("nameserver 8.8.8.8") == ns(["8.8.8.8"]) : C()} &
  {CF.resolv("nameserver 8.8.8.8 1.1.1.1\n") == ns(["8.8.8.8"]) : C()} &
  {CF.resolv("nameserver 1.1.1.1\nnameserver 2.2.2.2\nnameserver 3.3.3.3\nnameserver 4.4.4.4\n")
    == ns(["1.1.1.1", "2.2.2.2", "3.3.3.3"]) : C()} &
  {CF.resolv("nameserver ::1\nnameserver fe80::1%eth0\nnameserver 2001:4860:4860::8888\nnameserver 10.0.0.1\n")
    == ns(["10.0.0.1"]) : C()} &
  {CF.resolv("nameserver ::1\nnameserver ::2\nnameserver ::3\nnameserver 10.0.0.1\n")
    == ns(["10.0.0.1"]) : C()} &
  {CF.resolv("nameserver 256.1.1.1\nnameserver 01.2.3.4\nnameserver 1.2.3\nnameserver 127.0.0.1.\nnameserver 127.1\n")
    == dflt() : C()} &
  {CF.resolv("nameserver\nsearch\ndomain\noptions\nnameserver \t \n") == dflt() : C()} &
  {CF.resolv("NAMESERVER 1.2.3.4\nNameserver 1.2.3.4\nnameservers 1.2.3.4\n") == dflt() : C()} &
  {CF.resolv("#nameserver 1.2.3.4\n ;nameserver 1.2.3.5\nnameserver 1.2.3.6#x\n") == ns(["1.2.3.6"]) : C()} &
  {CF.resolv("sortlist 130.155.160.0/255.255.240.0\nlookup file bind\nnameserver 9.9.9.9\n") == ns(["9.9.9.9"]) : C()} &
  # resolv: search and domain (the last one wins)
  {CF.resolv("search a.example b.example\n") == srch(["a.example", "b.example"]) : C()} &
  {CF.resolv("domain corp.example\n") == srch(["corp.example"]) : C()} &
  {CF.resolv("domain d.example extra\n") == srch(["d.example"]) : C()} &
  {CF.resolv("domain d.example\nsearch a.example b.example\n") == srch(["a.example", "b.example"]) : C()} &
  {CF.resolv("search a.example b.example\ndomain d.example\n") == srch(["d.example"]) : C()} &
  {CF.resolv("search a.example\nsearch b.example c.example\n") == srch(["b.example", "c.example"]) : C()} &
  {CF.resolv("search a.example\nsearch\n") == srch(["a.example"]) : C()} &
  {CF.resolv("search a.example\ndomain # nothing\n") == srch(["a.example"]) : C()} &
  {CF.resolv("search a.example # b.example\n") == srch(["a.example"]) : C()} &
  # resolv: options
  {CF.resolv("options ndots:3 timeout:1 attempts:4\n") == opts(3n, 1n, 4n) : C()} &
  {CF.resolv("options rotate edns0 trust-ad single-request inet6\n") == dflt() : C()} &
  {CF.resolv("options ndots:2\noptions ndots:4\n") == opts(4n, 5n, 2n) : C()} &
  {CF.resolv("options ndots:2 ndots:5\n") == opts(5n, 5n, 2n) : C()} &
  {CF.resolv("options ndots:0 timeout:0 attempts:0\n") == opts(0n, 1n, 1n) : C()} &
  {CF.resolv("options ndots:15 timeout:30 attempts:5\n") == opts(15n, 30n, 5n) : C()} &
  {CF.resolv("options ndots:16 timeout:31 attempts:6\n") == opts(15n, 30n, 5n) : C()} &
  {CF.resolv("options ndots:99 timeout:99 attempts:99\n") == opts(15n, 30n, 5n) : C()} &
  {CF.resolv("options ndots:999999999999 timeout:99999999999999999999999 attempts:4294967296\n")
    == opts(15n, 30n, 5n) : C()} &
  {CF.resolv("options ndots:000000000000000000007 timeout:0000002\n") == opts(7n, 2n, 2n) : C()} &
  {CF.resolv("options ndots:00000000000000000000016\n") == opts(15n, 5n, 2n) : C()} &
  {CF.resolv("options ndots:3x timeout:2.5 attempts:3:4\n") == opts(3n, 2n, 3n) : C()} &
  {CF.resolv("options ndots: timeout:x attempts:-1 ndots:+2\n") == dflt() : C()} &
  {CF.resolv("options ndots timeout attempts\n") == dflt() : C()} &
  {CF.resolv("options NDOTS:3 Timeout:2\n") == dflt() : C()} &
  {CF.resolv("options ndots:3 # timeout:9\n") == opts(3n, 5n, 2n) : C()} &
  # resolv: whole files
  {CF.resolv(stub()) == M.Conf{["127.0.0.53"], ["."], 1n, 5n, 2n} : C()} &
  {CF.resolv(messy())
    == M.Conf{["10.0.0.1", "10.0.0.2", "10.0.0.3"], ["corp.example", "lab.example"], 2n, 3n, 4n} : C()} &
  # hosts
  {CF.hosts("") == Nil{} : List<&2, M.HostEntry>} &
  {CF.hosts("10.0.0.1\n# x\n\n") == Nil{} : List<&2, M.HostEntry>} &
  {entries() ==
    [M.HostEntry{"127.0.0.1", ["localhost"]},
     M.HostEntry{"::1", ["localhost", "ip6-localhost", "ip6-loopback"]},
     M.HostEntry{"10.1.2.3", ["Web.Example", "web"]},
     M.HostEntry{"10.1.2.4", ["web.example"]},
     M.HostEntry{"192.168.0.1", ["router;x"]},
     M.HostEntry{"10.1.2.6", ["WEB.EXAMPLE"]}] : List<&2, M.HostEntry>} &
  {CF.hosts_lookup(entries(), "localhost") == ["127.0.0.1", "::1"] : SS()} &
  {CF.hosts_lookup(entries(), "LocalHost") == ["127.0.0.1", "::1"] : SS()} &
  {CF.hosts_lookup(entries(), "ip6-loopback") == ["::1"] : SS()} &
  {CF.hosts_lookup(entries(), "web.example") == ["10.1.2.3", "10.1.2.4", "10.1.2.6"] : SS()} &
  {CF.hosts_lookup(entries(), "WEB") == ["10.1.2.3"] : SS()} &
  {CF.hosts_lookup(entries(), "commented.example") == Nil{} : SS()} &
  {CF.hosts_lookup(entries(), "router") == Nil{} : SS()} &
  {CF.hosts_lookup(entries(), "") == Nil{} : SS()} &
  {CF.hosts_lookup(entries(), "localhost.") == Nil{} : SS()} &
  # candidates (default ndots 1)
  {CF.candidates(dflt(), "host") == ["host"] : SS()} &
  {CF.candidates(dflt(), "host.") == ["host."] : SS()} &
  {CF.candidates(srch(["a.example", "b.example"]), "host")
    == ["host.a.example", "host.b.example", "host"] : SS()} &
  {CF.candidates(srch(["a.example", "b.example"]), "www.host")
    == ["www.host", "www.host.a.example", "www.host.b.example"] : SS()} &
  {CF.candidates(srch(["a.example", "b.example"]), "www.host.")
    == ["www.host."] : SS()} &
  {CF.candidates(srch(["a.example", "b.example"]), "") == [""] : SS()} &
  {CF.candidates(srch(["a.example.", "."]), "host") == ["host.a.example", "host.", "host"] : SS()} &
  {CF.candidates(M.Conf{Nil{}, ["k8s.local", "svc.local"], 5n, 5n, 2n}, "api.svc")
    == ["api.svc.k8s.local", "api.svc.svc.local", "api.svc"] : SS()} &
  {CF.candidates(M.Conf{Nil{}, ["k8s.local"], 2n, 5n, 2n}, "a.b.c")
    == ["a.b.c", "a.b.c.k8s.local"] : SS()} &
  {CF.candidates(M.Conf{Nil{}, ["k8s.local"], 0n, 5n, 2n}, "host")
    == ["host", "host.k8s.local"] : SS()} &
  {CF.candidates(CF.resolv(messy()), "db")
    == ["db.corp.example", "db.lab.example", "db"] : SS()} &
  {CF.candidates(CF.resolv(messy()), "db.x.y")
    == ["db.x.y", "db.x.y.corp.example", "db.x.y.lab.example"] : SS()} &
  {CF.candidates(CF.resolv(stub()), "host") == ["host.", "host"] : SS()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
