import Base
import ../src/bytes.bend as B
import ../src/types.bend as M
import ../src/wire.bend as W
import ../src/name.bend as NM
import ../src/ip.bend as IP
import ../src/frame.bend as F

# Runtime tests for wire, name, ip and frame, on both lanes:
#   bend tests/core_run.bend
#   bend tests/core_run.bend -o "$BEND_OUT/core_run" && "$BEND_OUT/core_run"
# Prints PASS / FAIL per case, then "ALL PASS" or "SOME FAIL: n".
# These cover what the checker cannot evaluate: full-range numbers (u16 and
# u32 sweeps), 255-byte names and 63-byte labels, 65535-byte frames, and
# hostile input of 100k+ chars or bytes (which must fail cleanly, not
# overflow the JS lane's stack or a Nat).

# Helpers (all loops)
# -------------------

def bytes_eq.go(a: List<&2, U32>, b: List<&2, U32>, ok: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      ok
    case Con{x, xs} Con{y, ys}:
      bytes_eq.go(xs, ys, ok && U32.is_eq(x, y))
    case _ _:
      False{}

def bytes_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  bytes_eq.go(a, b, True{})

def names_eq.go(a: M.Name(), b: M.Name(), ok: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      ok
    case Con{x, xs} Con{y, ys}:
      names_eq.go(xs, ys, ok && bytes_eq(x, y))
    case _ _:
      False{}

def names_eq(a: M.Name(), b: M.Name()) -> Bool:
  names_eq.go(a, b, True{})

def nats_eq.go(a: List<&2, Nat>, b: List<&2, Nat>, ok: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      ok
    case Con{x, xs} Con{y, ys}:
      nats_eq.go(xs, ys, ok && Nat.is_eq(x, y))
    case _ _:
      False{}

def str_eq.go(a: String, b: String, ok: Bool) -> Bool:
  match a b:
    case SNil{} SNil{}:
      ok
    case SCon{x, xs} SCon{y, ys}:
      str_eq.go(xs, ys, ok && Char.is_eq(x, y))
    case _ _:
      False{}

def str_eq(a: String, b: String) -> Bool:
  str_eq.go(a, b, True{})

def slen.go(s: String, k: Nat) -> Nat:
  match s:
    case SNil{}:
      k
    case SCon{c, t}:
      slen.go(t, 1n+k)

def slen(s: String) -> Nat:
  slen.go(s, 0n)

# n copies of a char, prepended to acc.
def rep.go(n: Nat, +c: Char, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      rep.go(p, c, SCon{c, acc})

def rep(n: Nat, c: Char) -> String:
  rep.go(n, c, SNil{})

# n copies of a string.
def reps.go(n: Nat, +s: String, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      reps.go(p, s, String.append(s, acc))

def reps(n: Nat, s: String) -> String:
  reps.go(n, s, SNil{})

# n copies of a cell.
def fill.go(n: Nat, +b: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      fill.go(p, b, b <> acc)

def fill(n: Nat, b: U32) -> List<&2, U32>:
  fill.go(n, b, Nil{})

# The cells lo, lo+1, ..., lo+n-1.
def span.go(n: Nat, +lo: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+(+p):
      span.go(p, lo, U32.from_nat(Nat.add(lo, p)) <> acc)

def span(lo: Nat, n: Nat) -> List<&2, U32>:
  span.go(n, lo, Nil{})

# n labels [97] ("a").
def many_labels.go(n: Nat, acc: M.Name()) -> M.Name():
  match n:
    case 0n:
      acc
    case 1n+p:
      many_labels.go(p, [97] <> acc)

# n zero groups.
def groups_zero.go(n: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      acc
    case 1n+p:
      groups_zero.go(p, 0n <> acc)

def groups_zero(n: Nat) -> List<&2, Nat>:
  groups_zero.go(n, Nil{})

# xs ++ ys, stack-safe.
def app(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  B.rev(U32, B.rev(U32, xs, Nil{}), ys)

def len(xs: List<&2, U32>) -> Nat:
  F.len(xs)

# Result checks
# -------------

def got_is(m: Maybe<&2, M.Got>, +v: Nat, rest: List<&2, U32>) -> Bool:
  match m:
    case Some{g}:
      match g:
        case M.Got{x, r}:
          Nat.is_eq(x, v) && bytes_eq(r, rest)
    case None{}:
      False{}

def got_none(m: Maybe<&2, M.Got>) -> Bool:
  Maybe.is_none(&2, M.Got, m)

def name_is(r: Result<&2, &2, M.NameError, M.Name()>, n: M.Name()) -> Bool:
  match r:
    case Done{x}:
      names_eq(x, n)
    case Fail{e}:
      False{}

def name_ok(r: Result<&2, &2, M.NameError, M.Name()>) -> Bool:
  match r:
    case Done{x}:
      True{}
    case Fail{e}:
      False{}

def err_tag(e: M.NameError) -> Nat:
  match e:
    case M.EmptyLabel{}:
      1n
    case M.LabelTooLong{}:
      2n
    case M.NameTooLong{}:
      3n
    case M.BadEscape{}:
      4n
    case M.BadChar{}:
      5n

def EMPTY() -> Nat:
  1n

def LONG_LABEL() -> Nat:
  2n

def LONG_NAME() -> Nat:
  3n

def BAD_ESCAPE() -> Nat:
  4n

def BAD_CHAR() -> Nat:
  5n

def name_err(r: Result<&2, &2, M.NameError, M.Name()>, tag: Nat) -> Bool:
  match r:
    case Done{x}:
      False{}
    case Fail{e}:
      Nat.is_eq(err_tag(e), tag)

# The name's text read back as the name.
def text_rt(+n: M.Name()) -> Bool:
  name_is(NM.from_text(NM.to_text(n)), n)

def v4_is(m: Maybe<&2, M.RData>, +a: Nat, +b: Nat, +c: Nat, +d: Nat) -> Bool:
  match m:
    case Some{r}:
      match r:
        case M.RIpv4{w, x, y, z}:
          Nat.is_eq(w, a) && Nat.is_eq(x, b) && Nat.is_eq(y, c) && Nat.is_eq(z, d)
        case _:
          False{}
    case None{}:
      False{}

def v6_is(m: Maybe<&2, M.RData>, gs: List<&2, Nat>) -> Bool:
  match m:
    case Some{r}:
      match r:
        case M.RIpv6{xs}:
          nats_eq.go(xs, gs, True{})
        case _:
          False{}
    case None{}:
      False{}

def data_none(m: Maybe<&2, M.RData>) -> Bool:
  Maybe.is_none(&2, M.RData, m)

def framed_is(r: Result<&2, &2, F.FrameError, F.Framed>, m: List<&2, U32>, rest: List<&2, U32>) -> Bool:
  match r:
    case Done{f}:
      match f:
        case F.Framed{x, y}:
          bytes_eq(x, m) && bytes_eq(y, rest)
    case Fail{e}:
      False{}

def framed_rest_len(r: Result<&2, &2, F.FrameError, F.Framed>, +mlen: Nat, +rlen: Nat) -> Bool:
  match r:
    case Done{f}:
      match f:
        case F.Framed{x, y}:
          Nat.is_eq(len(x), mlen) && Nat.is_eq(len(y), rlen)
    case Fail{e}:
      False{}

def frame_err_tag(e: F.FrameError) -> Nat:
  match e:
    case F.Cut{}:
      1n
    case F.TooLarge{n}:
      Nat.add(1000000n, n)
    case F.NotByte{}:
      3n

def frame_err(r: Result<&2, &2, F.FrameError, F.Framed>, tag: Nat) -> Bool:
  match r:
    case Done{f}:
      False{}
    case Fail{e}:
      Nat.is_eq(frame_err_tag(e), tag)

# Sweeps
# ------

def rt8(+n: Nat) -> Bool:
  got_is(W.get_u8(app(W.put_u8(n), [7])), n, [7])

def rt16(+n: Nat) -> Bool:
  got_is(W.get_u16(app(W.put_u16(n), [7])), n, [7])

def rt32(+n: Nat) -> Bool:
  got_is(W.get_u32(app(W.put_u32(n), [7])), n, [7])

# rt8(k) for every k <= n.
def sweep8(n: Nat, ok: Bool) -> Bool:
  match n:
    case 0n:
      ok && rt8(0n)
    case 1n+(+p):
      sweep8(p, ok && rt8(1n+p))

def sweep16(n: Nat, ok: Bool) -> Bool:
  match n:
    case 0n:
      ok && rt16(0n)
    case 1n+(+p):
      sweep16(p, ok && rt16(1n+p))

# rt32(k * 65537) for every k <= n (65535 * 65537 = 2^32 - 1).
def sweep32(n: Nat, ok: Bool) -> Bool:
  match n:
    case 0n:
      ok && rt32(0n)
    case 1n+(+p):
      sweep32(p, ok && rt32(Nat.mul(1n+p, 65537n)) && rt32(Nat.add(Nat.mul(p, 65537n), 12345n)))

def rt4(+k: Nat) -> Bool:
  +j = Nat.sub(255n, k)
  v4_is(IP.parse4(IP.show4(k, j, k, 0n)), k, j, k, 0n)

def sweep4(n: Nat, ok: Bool) -> Bool:
  match n:
    case 0n:
      ok && rt4(0n)
    case 1n+(+p):
      sweep4(p, ok && rt4(1n+p))

def groups6(+k: Nat) -> List<&2, Nat>:
  +g = Nat.mul(k, 257n)
  [g, 0n, 0n, k, Nat.sub(65535n, g), 0n, 0n, 0n]

def rt6(+k: Nat) -> Bool:
  v6_is(IP.parse6(IP.show6(groups6(k))), groups6(k))

def sweep6(n: Nat, ok: Bool) -> Bool:
  match n:
    case 0n:
      ok && rt6(0n)
    case 1n+(+p):
      sweep6(p, ok && rt6(1n+p))

# Every byte value 0..255 in some label read back through text: five
# one-label names (0..62, 63..125, 126..188, 189..251, 252..255).
def all_bytes_rt() -> Bool:
  text_rt([span(0n, 63n)]) && text_rt([span(63n, 63n)]) && text_rt([span(126n, 63n)])
    && text_rt([span(189n, 63n)]) && text_rt([span(252n, 4n)])

# Fixtures
# --------

# 255 bytes on the wire: labels of 63, 63, 63 and 61.
def max_text() -> String:
  rep(63n, 'a') ++ "." ++ rep(63n, 'b') ++ "." ++ rep(63n, 'c') ++ "." ++ rep(61n, 'd')

def max_name() -> M.Name():
  [fill(63n, 97), fill(63n, 98), fill(63n, 99), fill(61n, 100)]

def big() -> List<&2, U32>:
  fill(65535n, 171)

# Feeds each byte on its own (a loop).
def feed_each(xs: List<&2, U32>, s: F.Reader) -> F.Reader:
  match xs:
    case Nil{}:
      s
    case Con{h, t}:
      feed_each(t, F.feed(s, [h]))

# The cases
# ---------

def cases() -> List<(String & Bool)>:
  [
    # wire
    ("u8 sweep 0..255", sweep8(255n, True{})),
    ("u16 sweep 0..65535", sweep16(65535n, True{})),
    ("u32 sweep 65536 samples", sweep32(65535n, True{})),
    ("put_u16 65535", bytes_eq(W.put_u16(65535n), [255, 255])),
    ("put_u16 258", bytes_eq(W.put_u16(258n), [1, 2])),
    ("put_u32 max", bytes_eq(W.put_u32(4294967295n), [255, 255, 255, 255])),
    ("put_u32 0x01020304", bytes_eq(W.put_u32(16909060n), [1, 2, 3, 4])),
    ("get_u32 max", got_is(W.get_u32([255, 255, 255, 255]), 4294967295n, [])),
    ("get_u16 non-byte", got_none(W.get_u16([0, 256])) && got_none(W.get_u16([4294967295, 0]))),
    ("get_u32 non-byte", got_none(W.get_u32([0, 0, 0, 65536]))),
    ("get short", got_none(W.get_u8([])) && got_none(W.get_u16([1])) && got_none(W.get_u32([1, 2, 3]))),
    # name: limits
    ("63-byte label", name_is(NM.from_text(rep(63n, 'x')), [fill(63n, 120)])),
    ("64-byte label", name_err(NM.from_text(rep(64n, 'x')), LONG_LABEL())),
    ("255-byte name", name_is(NM.from_text(max_text()), max_name())),
    ("255-byte name, trailing dot", name_is(NM.from_text(max_text() ++ "."), max_name())),
    ("255-byte name ok", NM.ok(max_name()) && Nat.is_eq(NM.wire_size(max_name()), 255n)),
    ("255-byte name wire", Nat.is_eq(len(NM.wire(max_name())), 255n)),
    ("255-byte name text", str_eq(NM.to_text(max_name()), max_text())),
    ("255-byte name roundtrip", text_rt(max_name())),
    ("256-byte name", name_err(NM.from_text(max_text() ++ "e"), LONG_NAME())),
    ("256-byte name not ok", Bool.not(NM.ok([fill(63n, 97), fill(63n, 98), fill(63n, 99), fill(62n, 100)]))),
    ("127 one-byte labels", name_ok(NM.from_text(reps(126n, "a.") ++ "a"))),
    ("128 one-byte labels", name_err(NM.from_text(reps(127n, "a.") ++ "a"), LONG_NAME())),
    ("all bytes roundtrip", all_bytes_rt()),
    ("escaped 63-byte label", name_is(NM.from_text(reps(63n, "\\255")), [fill(63n, 255)])),
    ("eq 255-byte name", NM.eq(max_name(), [fill(63n, 65), fill(63n, 66), fill(63n, 67), fill(61n, 68)])),
    ("lower 255-byte name", names_eq(NM.lower([fill(63n, 65), fill(63n, 98), fill(63n, 67), fill(61n, 100)]), max_name())),
    # name: hostile text
    ("100k-char label", name_err(NM.from_text(rep(100000n, 'a')), LONG_LABEL())),
    ("100k one-byte labels", name_err(NM.from_text(reps(100000n, "a.")), LONG_NAME())),
    ("100k dots", name_err(NM.from_text(rep(100000n, '.')), EMPTY())),
    ("100k backslash pairs", name_err(NM.from_text(rep(200000n, '\\')), LONG_LABEL())),
    ("odd backslashes", name_err(NM.from_text(rep(100001n, '\\')), BAD_ESCAPE())),
    ("100k escapes", name_err(NM.from_text(reps(100000n, "\\000")), LONG_LABEL())),
    ("100k digits after escape", name_err(NM.from_text("\\" ++ rep(100000n, '9')), BAD_ESCAPE())),
    ("100k emoji", name_err(NM.from_text(rep(100000n, '\u{1F600}')), BAD_CHAR())),
    ("100k spaces", name_err(NM.from_text(rep(100000n, ' ')), BAD_CHAR())),
    ("NUL char", name_err(NM.from_text("a\u{0}b"), BAD_CHAR())),
    ("non-byte char escaped", name_err(NM.from_text("\\\u{100}"), BAD_CHAR())),
    # name: hostile names (caller-built)
    ("100k labels: not ok, wire, text", Bool.not(NM.ok(many_labels.go(100000n, Nil{})))
      && Nat.is_eq(len(NM.wire(many_labels.go(100000n, Nil{}))), 200001n)
      && Nat.is_eq(slen(NM.to_text(many_labels.go(100000n, Nil{}))), 199999n)),
    ("100k-byte label: not ok, wire", Bool.not(NM.ok([fill(100000n, 97)]))
      && Nat.is_eq(len(NM.wire([fill(100000n, 97)])), 100002n)),
    ("100k-byte label eq", NM.eq([fill(100000n, 65)], [fill(100000n, 97)])
      && Bool.not(NM.eq([fill(100000n, 65)], [fill(99999n, 97)]))),
    ("70k-byte label text", name_err(NM.from_text(NM.to_text([fill(70000n, 32)])), LONG_LABEL())
      && Nat.is_eq(slen(NM.to_text([fill(70000n, 32)])), 280000n)),
    ("non-byte cell text", str_eq(NM.to_text([[97, 4294967295]]), "a\\999")),
    # ip
    ("show4 max", str_eq(IP.show4(255n, 255n, 255n, 255n), "255.255.255.255")),
    ("parse4 max", v4_is(IP.parse4("255.255.255.255"), 255n, 255n, 255n, 255n)),
    ("parse4 sweep 0..255", sweep4(255n, True{})),
    ("parse4 huge octet", data_none(IP.parse4("1.2.3." ++ rep(100000n, '9')))),
    ("parse4 100k digits", data_none(IP.parse4(rep(100000n, '1')))),
    ("parse4 100k dots", data_none(IP.parse4(rep(100000n, '.')))),
    ("parse4 4294967297", data_none(IP.parse4("1.2.3.4294967297"))),
    ("show6 doc", str_eq(IP.show6([8193n, 3512n, 0n, 0n, 0n, 65280n, 66n, 33577n]), "2001:db8::ff00:42:8329")),
    ("show6 max", str_eq(IP.show6([65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n]),
      "ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff")),
    ("show6 mapped", str_eq(IP.show6([0n, 0n, 0n, 0n, 0n, 65535n, 49152n, 513n]), "::ffff:c000:201")),
    ("parse6 doc", v6_is(IP.parse6("2001:DB8:0:0:0:FF00:42:8329"), [8193n, 3512n, 0n, 0n, 0n, 65280n, 66n, 33577n])),
    ("parse6 mapped v4", v6_is(IP.parse6("::ffff:192.0.2.1"), [0n, 0n, 0n, 0n, 0n, 65535n, 49152n, 513n])),
    ("parse6 max", v6_is(IP.parse6("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff"),
      [65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n])),
    ("parse6 sweep 256", sweep6(255n, True{})),
    ("parse6 100k colons", data_none(IP.parse6(rep(100000n, ':')))),
    ("parse6 100k hex", data_none(IP.parse6(rep(100000n, 'f')))),
    ("parse6 50k groups", data_none(IP.parse6(reps(50000n, "1:") ++ "1"))),
    ("parse6 50k groups after ::", data_none(IP.parse6("::" ++ reps(50000n, "1:") ++ "1"))),
    ("parse6 long v4 tail", data_none(IP.parse6("::" ++ reps(50000n, "1.")))),
    ("show6 100k zeros", str_eq(IP.show6(groups_zero(100000n)), "::")),
    # frame
    ("frame 65535", Nat.is_eq(len(F.frame(big())), 65537n)
      && bytes_eq(B.rev(U32, B.rev(U32, F.frame([1]), Nil{}), Nil{}), [0, 1, 1])),
    ("read 65535", framed_is(F.read(65535n, app(F.frame(big()), [1, 2])), big(), [1, 2])),
    ("read 65535 budget-1", frame_err(F.read(65534n, F.frame(big())), 1065535n)),
    ("read 65535 cut", frame_err(F.read(65535n, app([255, 255], fill(65534n, 171))), 1n)),
    ("feed each byte", framed_is(F.finish(feed_each(app(F.frame(big()), [5]), F.init(65535n))), big(), [5])),
    ("feed split", framed_is(F.finish(F.feed(F.feed(F.init(65535n), [255]), app([255], app(big(), [9])))),
      big(), [9])),
    ("garbage 200k 0xff", framed_rest_len(F.read(65535n, fill(200000n, 255)), 65535n, 134463n)),
    ("garbage too large", frame_err(F.read(1000n, fill(200000n, 255)), 1065535n)),
    ("garbage non-byte", frame_err(F.read(65535n, fill(200000n, 70000)), 3n)),
    ("zero frame then rest", framed_rest_len(F.read(65535n, app([0, 0], fill(100000n, 1))), 0n, 100000n)),
    ("done", F.done(F.feed(F.init(65535n), F.frame(big())))
      && Bool.not(F.done(F.feed(F.init(65535n), fill(30000n, 171)))))
  ]

def report(xs: List<(String & Bool)>, fails: Nat) -> IO(Unit):
  match xs:
    case Nil{}:
      match fails:
        case 0n:
          IO.print("ALL PASS")
        case 1n+p:
          IO.print("SOME FAIL: " ++ Nat.show(1n+p))
    case Con{c, t}:
      match c:
        case (name, ok):
          match ok:
            case True{}:
              do IO<Unit>:
                IO.print("PASS " ++ name)
                report(t, fails)
            case False{}:
              do IO<Unit>:
                IO.print("FAIL " ++ name)
                report(t, 1n+fails)

def main() -> IO(Unit):
  report(cases(), 0n)
