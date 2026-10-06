# Laws 10 (ipv4_roundtrip), 11 (frame_split) and 12 (frame_roundtrip).
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/types.bend as M
import ../src/num.bend as N
import ../src/wire.bend as W
import ../src/ip.bend as IP
import ../src/frame.bend as F
import ../proofs/num.bend as NP
import ../proofs/wire.bend as WP

def BL() -> Data:
  List<&2, U32>

def FRes() -> Data:
  Result<&2, &2, F.FrameError, F.Framed>

# Lists
# -----

def fr_cat_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %fr_cat_nil(A, t) : {Con{h, List.append(&2, A, t, Nil{})} == Con{h, _} : List<&2, A>}
      {==}

def fr_rev_rev_onto(-A: Data, xs: List<&2, A>, acc: List<&2, A>, -ys: List<&2, A>)
  -> {B.rev(A, B.rev(A, xs, acc), ys) == B.rev(A, acc, List.append(&2, A, xs, ys)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      fr_rev_rev_onto(A, t, h <> acc, ys)

def fr_rev_rev(-A: Data, +xs: List<&2, A>) -> {B.rev(A, B.rev(A, xs, Nil{}), Nil{}) == xs : List<&2, A>}:
  Equal.trans(List<&2, A>, B.rev(A, B.rev(A, xs, Nil{}), Nil{}), List.append(&2, A, xs, Nil{}), xs,
    fr_rev_rev_onto(A, xs, Nil{}, Nil{}), fr_cat_nil(A, xs))

# Law 10
# ------

def MNat() -> Data:
  Maybe<&2, Nat>

def ipf_and_tt(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, NP.false_true(ea))

# Strings

def ipf_sapp_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %ipf_sapp_nil(t) : {SCon{c, String.append(t, SNil{})} == SCon{c, _} : String}
      {==}

def ipf_srev_onto(x: String, a: String, -b: String)
  -> {String.reverse.go(String.reverse.go(x, a), b) == String.reverse.go(a, String.append(x, b)) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{h, t}:
      ipf_srev_onto(t, SCon{h, a}, b)

def ipf_srev_rev(+x: String) -> {String.reverse(String.reverse(x)) == x : String}:
  Equal.trans(String, String.reverse.go(String.reverse.go(x, SNil{}), SNil{}), String.append(x, SNil{}), x,
    ipf_srev_onto(x, SNil{}, SNil{}), ipf_sapp_nil(x))

# Digit chars

def ipf_is_digit(k: B.Class) -> Bool:
  match k:
    case B.Digit{v}:
      True{}
    case _:
      False{}

def ipf_digit_chars(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(ipf_is_digit(B.char_class(c)), ipf_digit_chars(t))

def ipf_dot_of_digit(k: B.Class, -c: Char, e: {ipf_is_digit(k) == True{} : Bool}) -> {IP.is_dot.of(k, c) == False{} : Bool}:
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      Empty.absurd({IP.is_dot.of(B.HexLetter{v}, c) == False{} : Bool}, NP.false_true(e))
    case B.Letter{}:
      Empty.absurd({IP.is_dot.of(B.Letter{}, c) == False{} : Bool}, NP.false_true(e))
    case B.Tchar{}:
      Empty.absurd({IP.is_dot.of(B.Tchar{}, c) == False{} : Bool}, NP.false_true(e))
    case B.Colon{}:
      Empty.absurd({IP.is_dot.of(B.Colon{}, c) == False{} : Bool}, NP.false_true(e))
    case B.Semi{}:
      Empty.absurd({IP.is_dot.of(B.Semi{}, c) == False{} : Bool}, NP.false_true(e))
    case B.Slash{}:
      Empty.absurd({IP.is_dot.of(B.Slash{}, c) == False{} : Bool}, NP.false_true(e))
    case B.Sp{}:
      Empty.absurd({IP.is_dot.of(B.Sp{}, c) == False{} : Bool}, NP.false_true(e))
    case B.Htab{}:
      Empty.absurd({IP.is_dot.of(B.Htab{}, c) == False{} : Bool}, NP.false_true(e))
    case B.Cr{}:
      Empty.absurd({IP.is_dot.of(B.Cr{}, c) == False{} : Bool}, NP.false_true(e))
    case B.Lf{}:
      Empty.absurd({IP.is_dot.of(B.Lf{}, c) == False{} : Bool}, NP.false_true(e))
    case B.Delim{}:
      Empty.absurd({IP.is_dot.of(B.Delim{}, c) == False{} : Bool}, NP.false_true(e))
    case B.Ctl{}:
      Empty.absurd({IP.is_dot.of(B.Ctl{}, c) == False{} : Bool}, NP.false_true(e))
    case B.High{}:
      Empty.absurd({IP.is_dot.of(B.High{}, c) == False{} : Bool}, NP.false_true(e))
    case B.Invalid{}:
      Empty.absurd({IP.is_dot.of(B.Invalid{}, c) == False{} : Bool}, NP.false_true(e))

def ipf_digit_char(d: Nat, e: {Nat.is_le(d, 9n) == True{} : Bool}) -> {ipf_is_digit(B.char_class(N.digit_char(d))) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+k:
      Empty.absurd({ipf_is_digit(B.char_class(N.digit_char(10n+k))) == True{} : Bool}, NP.false_true(e))

def ipf_text_digits(ds: List<&2, Nat>, +acc: String, +ok: {NP.digits_ok(9n, ds) == True{} : Bool}, ha: {ipf_digit_chars(acc) == True{} : Bool})
  -> {ipf_digit_chars(N.digits_text(ds, acc)) == True{} : Bool}:
  match ds:
    case Nil{}:
      ha
    case Con{+d, +t}:
      ipf_text_digits(t, SCon{N.digit_char(d), acc}, NP.and_r(Nat.is_le(d, 9n), NP.digits_ok(9n, t), ok),
        ipf_and_tt(ipf_is_digit(B.char_class(N.digit_char(d))), ipf_digit_chars(acc),
          ipf_digit_char(d, NP.and_l(Nat.is_le(d, 9n), NP.digits_ok(9n, t), ok)), ha))

def ipf_show_digits(+n: Nat) -> {ipf_digit_chars(N.show(n)) == True{} : Bool}:
  ipf_text_digits(N.dec_count(n, [0n]), SNil{}, NP.dec_count_ok(n, [0n], {==}), {==})

# No leading zero: the most significant digit of a count from [1] is nonzero.

def ipf_nzt.go(t: List<&2, Nat>, d: Nat) -> Bool:
  match t:
    case Nil{}:
      Bool.not(Nat.is_eq(d, 0n))
    case Con{e, r}:
      ipf_nzt.go(r, e)

def ipf_nzt(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, t}:
      ipf_nzt.go(t, d)

def ipf_go_con(x: List<&2, Nat>, -d: Nat, hc: {NP.is_con(x) == True{} : Bool}) -> {ipf_nzt.go(x, d) == ipf_nzt(x) : Bool}:
  match x:
    case Nil{}:
      Empty.absurd({ipf_nzt.go(Nil{}, d) == ipf_nzt(Nil{}) : Bool}, NP.false_true(hc))
    case Con{e, r}:
      {==}

def ipf_go_nzt(t: List<&2, Nat>, -d: Nat, e: {ipf_nzt.go(t, d) == True{} : Bool}) -> {ipf_nzt(t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{x, r}:
      e

def ipf_go_succ(t: List<&2, Nat>, -k: Nat, e: {ipf_nzt.go(t, k) == True{} : Bool}) -> {ipf_nzt.go(t, 1n+k) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{x, r}:
      e

def ipf_inc_nzt(ds: List<&2, Nat>, e: {ipf_nzt(ds) == True{} : Bool}) -> {ipf_nzt(N.dec_inc(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, +t}:
      match d:
        case 0n:
          ipf_go_succ(t, 0n, e)
        case 1n:
          ipf_go_succ(t, 1n, e)
        case 2n:
          ipf_go_succ(t, 2n, e)
        case 3n:
          ipf_go_succ(t, 3n, e)
        case 4n:
          ipf_go_succ(t, 4n, e)
        case 5n:
          ipf_go_succ(t, 5n, e)
        case 6n:
          ipf_go_succ(t, 6n, e)
        case 7n:
          ipf_go_succ(t, 7n, e)
        case 8n:
          ipf_go_succ(t, 8n, e)
        case 9n:
          Equal.trans(Bool, ipf_nzt.go(N.dec_inc(t), 0n), ipf_nzt(N.dec_inc(t)), True{},
            ipf_go_con(N.dec_inc(t), 0n, NP.dec_inc_con(t)), ipf_inc_nzt(t, ipf_go_nzt(t, 9n, e)))
        case 10n+k:
          ipf_go_succ(t, 10n+k, e)

def ipf_count_nzt(n: Nat, +ds: List<&2, Nat>, e: {ipf_nzt(ds) == True{} : Bool}) -> {ipf_nzt(N.dec_count(n, ds)) == True{} : Bool}:
  match n:
    case 0n:
      e
    case 1n+p:
      ipf_count_nzt(p, N.dec_inc(ds), ipf_inc_nzt(ds, e))

def ipf_lead_char(d: Nat, e9: {Nat.is_le(d, 9n) == True{} : Bool}, nz: {Bool.not(Nat.is_eq(d, 0n)) == True{} : Bool})
  -> {Bool.not(IP.is_zero_digit(B.char_class(N.digit_char(d)))) == True{} : Bool}:
  match d:
    case 0n:
      Empty.absurd({Bool.not(IP.is_zero_digit(B.char_class(N.digit_char(0n)))) == True{} : Bool}, NP.false_true(nz))
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+k:
      Empty.absurd({Bool.not(IP.is_zero_digit(B.char_class(N.digit_char(10n+k)))) == True{} : Bool}, NP.false_true(e9))

def ipf_lead(acc: String, +d: Nat, e9: {Nat.is_le(d, 9n) == True{} : Bool}, nz: {Bool.not(Nat.is_eq(d, 0n)) == True{} : Bool})
  -> {IP.no_lead_zero(SCon{N.digit_char(d), acc}) == True{} : Bool}:
  match acc:
    case SNil{}:
      {==}
    case SCon{c, r}:
      ipf_lead_char(d, e9, nz)

def ipf_nlz_go(t: List<&2, Nat>, +d: Nat, +acc: String, +ok: {NP.digits_ok(9n, Con{d, t}) == True{} : Bool}, nz: {ipf_nzt.go(t, d) == True{} : Bool})
  -> {IP.no_lead_zero(N.digits_text(t, SCon{N.digit_char(d), acc})) == True{} : Bool}:
  match t:
    case Nil{}:
      ipf_lead(acc, d, NP.and_l(Nat.is_le(d, 9n), True{}, ok), nz)
    case Con{+x, +r}:
      ipf_nlz_go(r, x, SCon{N.digit_char(d), acc}, NP.and_r(Nat.is_le(d, 9n), NP.digits_ok(9n, Con{x, r}), ok), nz)

def ipf_nlz_digits(ds: List<&2, Nat>, +acc: String, ok: {NP.digits_ok(9n, ds) == True{} : Bool}, nz: {ipf_nzt(ds) == True{} : Bool}, hc: {NP.is_con(ds) == True{} : Bool})
  -> {IP.no_lead_zero(N.digits_text(ds, acc)) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({IP.no_lead_zero(N.digits_text(Nil{}, acc)) == True{} : Bool}, NP.false_true(hc))
    case Con{d, t}:
      ipf_nlz_go(t, d, acc, ok, nz)

def ipf_nlz_show(n: Nat) -> {IP.no_lead_zero(N.show(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      ipf_nlz_digits(N.dec_count(p, [1n]), SNil{}, NP.dec_count_ok(p, [1n], {==}), ipf_count_nzt(p, [1n], {==}), NP.dec_count_con(p, [1n], {==}))

# An octet reads back.
def ipf_octet(+n: Nat, +e: {Nat.is_le(n, 255n) == True{} : Bool}) -> {IP.octet(N.show(n)) == Some{n} : MNat()}:
  +lim = NP.le_trans(n, 255n, N.LIMIT(), e, {==})
  %Equal.sym(MNat(), N.read(N.show(n)), Some{n}, Laws.dec_roundtrip(n, lim)) :
    {IP.octet.of(_, IP.no_lead_zero(N.show(n))) == Some{n} : MNat()}
  %Equal.sym(Bool, IP.no_lead_zero(N.show(n)), True{}, ipf_nlz_show(n)) :
    {IP.octet.of(Some{n}, _) == Some{n} : MNat()}
  %Equal.sym(Bool, Nat.is_le(n, 255n), True{}, e) :
    {N.bound.pick(_, n) == Some{n} : MNat()}
  {==}

# Cutting

def ipf_cut_app(x: String, -y: String, -st: IP.Cut)
  -> {IP.cut.go(String.append(x, y), IP.SepDot{}, st) == IP.cut.go(y, IP.SepDot{}, IP.cut.go(x, IP.SepDot{}, st)) : IP.Cut}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, t}:
      ipf_cut_app(t, y, IP.cut.step(IP.SepDot{}, st, c))

def ipf_cut_digits(x: String, cur: String, -acc: List<&2, String>, +h: {ipf_digit_chars(x) == True{} : Bool})
  -> {IP.cut.go(x, IP.SepDot{}, IP.Cut{cur, acc}) == IP.Cut{String.reverse.go(x, cur), acc} : IP.Cut}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, IP.is_dot.of(B.char_class(c), c), False{},
        ipf_dot_of_digit(B.char_class(c), c, NP.and_l(ipf_is_digit(B.char_class(c)), ipf_digit_chars(t), h))) :
        {IP.cut.go(t, IP.SepDot{}, IP.cut.char(_, c, cur, acc)) == IP.Cut{String.reverse.go(t, SCon{c, cur}), acc} : IP.Cut}
      ipf_cut_digits(t, SCon{c, cur}, acc, NP.and_r(ipf_is_digit(B.char_class(c)), ipf_digit_chars(t), h))

# One piece of digits, then a dot.
def ipf_seg(+x: String, +r: String, +acc: List<&2, String>, h: {ipf_digit_chars(x) == True{} : Bool})
  -> {IP.cut.go(String.append(x, SCon{'.', r}), IP.SepDot{}, IP.Cut{SNil{}, acc}) == IP.cut.go(r, IP.SepDot{}, IP.Cut{SNil{}, x <> acc}) : IP.Cut}:
  %Equal.sym(IP.Cut, IP.cut.go(String.append(x, SCon{'.', r}), IP.SepDot{}, IP.Cut{SNil{}, acc}),
    IP.cut.go(SCon{'.', r}, IP.SepDot{}, IP.cut.go(x, IP.SepDot{}, IP.Cut{SNil{}, acc})), ipf_cut_app(x, SCon{'.', r}, IP.Cut{SNil{}, acc})) :
    {_ == IP.cut.go(r, IP.SepDot{}, IP.Cut{SNil{}, x <> acc}) : IP.Cut}
  %Equal.sym(IP.Cut, IP.cut.go(x, IP.SepDot{}, IP.Cut{SNil{}, acc}), IP.Cut{String.reverse.go(x, SNil{}), acc}, ipf_cut_digits(x, SNil{}, acc, h)) :
    {IP.cut.go(SCon{'.', r}, IP.SepDot{}, _) == IP.cut.go(r, IP.SepDot{}, IP.Cut{SNil{}, x <> acc}) : IP.Cut}
  %Equal.sym(String, String.reverse(String.reverse(x)), x, ipf_srev_rev(x)) :
    {IP.cut.go(r, IP.SepDot{}, IP.Cut{SNil{}, _ <> acc}) == IP.cut.go(r, IP.SepDot{}, IP.Cut{SNil{}, x <> acc}) : IP.Cut}
  {==}

def ipf_cut4(+a: Nat, +b: Nat, +c: Nat, +d: Nat)
  -> {IP.cut(IP.SepDot{}, IP.show4(a, b, c, d)) == [N.show(d), N.show(c), N.show(b), N.show(a)] : List<&2, String>}:
  %Equal.sym(IP.Cut,
    IP.cut.go(String.append(N.show(a), SCon{'.', String.append(N.show(b), SCon{'.', String.append(N.show(c), SCon{'.', N.show(d)})})}), IP.SepDot{}, IP.Cut{SNil{}, Nil{}}),
    IP.cut.go(String.append(N.show(b), SCon{'.', String.append(N.show(c), SCon{'.', N.show(d)})}), IP.SepDot{}, IP.Cut{SNil{}, [N.show(a)]}),
    ipf_seg(N.show(a), String.append(N.show(b), SCon{'.', String.append(N.show(c), SCon{'.', N.show(d)})}), Nil{}, ipf_show_digits(a))) :
    {IP.cut.end(_) == [N.show(d), N.show(c), N.show(b), N.show(a)] : List<&2, String>}
  %Equal.sym(IP.Cut,
    IP.cut.go(String.append(N.show(b), SCon{'.', String.append(N.show(c), SCon{'.', N.show(d)})}), IP.SepDot{}, IP.Cut{SNil{}, [N.show(a)]}),
    IP.cut.go(String.append(N.show(c), SCon{'.', N.show(d)}), IP.SepDot{}, IP.Cut{SNil{}, [N.show(b), N.show(a)]}),
    ipf_seg(N.show(b), String.append(N.show(c), SCon{'.', N.show(d)}), [N.show(a)], ipf_show_digits(b))) :
    {IP.cut.end(_) == [N.show(d), N.show(c), N.show(b), N.show(a)] : List<&2, String>}
  %Equal.sym(IP.Cut,
    IP.cut.go(String.append(N.show(c), SCon{'.', N.show(d)}), IP.SepDot{}, IP.Cut{SNil{}, [N.show(b), N.show(a)]}),
    IP.cut.go(N.show(d), IP.SepDot{}, IP.Cut{SNil{}, [N.show(c), N.show(b), N.show(a)]}),
    ipf_seg(N.show(c), N.show(d), [N.show(b), N.show(a)], ipf_show_digits(c))) :
    {IP.cut.end(_) == [N.show(d), N.show(c), N.show(b), N.show(a)] : List<&2, String>}
  %Equal.sym(IP.Cut,
    IP.cut.go(N.show(d), IP.SepDot{}, IP.Cut{SNil{}, [N.show(c), N.show(b), N.show(a)]}),
    IP.Cut{String.reverse.go(N.show(d), SNil{}), [N.show(c), N.show(b), N.show(a)]},
    ipf_cut_digits(N.show(d), SNil{}, [N.show(c), N.show(b), N.show(a)], ipf_show_digits(d))) :
    {IP.cut.end(_) == [N.show(d), N.show(c), N.show(b), N.show(a)] : List<&2, String>}
  %Equal.sym(String, String.reverse(String.reverse(N.show(d))), N.show(d), ipf_srev_rev(N.show(d))) :
    {Con{_, [N.show(c), N.show(b), N.show(a)]} == [N.show(d), N.show(c), N.show(b), N.show(a)] : List<&2, String>}
  {==}

def Laws.ipv4_roundtrip(a, b, c, d, ea, eb, ec, ed):
  %Equal.sym(List<&2, String>, IP.cut(IP.SepDot{}, IP.show4(a, b, c, d)), [N.show(d), N.show(c), N.show(b), N.show(a)], ipf_cut4(a, b, c, d)) :
    {IP.quad.of(_) == Some{M.RIpv4{a, b, c, d}} : Maybe<&2, M.RData>}
  %Equal.sym(MNat(), IP.octet(N.show(a)), Some{a}, ipf_octet(a, ea)) :
    {IP.quad(_, IP.octet(N.show(b)), IP.octet(N.show(c)), IP.octet(N.show(d))) == Some{M.RIpv4{a, b, c, d}} : Maybe<&2, M.RData>}
  %Equal.sym(MNat(), IP.octet(N.show(b)), Some{b}, ipf_octet(b, eb)) :
    {IP.quad(Some{a}, _, IP.octet(N.show(c)), IP.octet(N.show(d))) == Some{M.RIpv4{a, b, c, d}} : Maybe<&2, M.RData>}
  %Equal.sym(MNat(), IP.octet(N.show(c)), Some{c}, ipf_octet(c, ec)) :
    {IP.quad(Some{a}, Some{b}, _, IP.octet(N.show(d))) == Some{M.RIpv4{a, b, c, d}} : Maybe<&2, M.RData>}
  %Equal.sym(MNat(), IP.octet(N.show(d)), Some{d}, ipf_octet(d, ed)) :
    {IP.quad(Some{a}, Some{b}, Some{c}, _) == Some{M.RIpv4{a, b, c, d}} : Maybe<&2, M.RData>}
  {==}

# Law 11
# ------

def feed_go_split(a: BL(), -b: BL(), -s: F.Reader)
  -> {F.feed.go(b, F.feed.go(a, s)) == F.feed.go(List.append(&2, U32, a, b), s) : F.Reader}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      feed_go_split(t, b, F.step(s, h))

def Laws.frame_split(s, x, y):
  feed_go_split(x, y, s)

# Law 12
# ------

# len is List.length.
def frame_len_go(xs: BL(), +k: Nat) -> {F.len.go(xs, k) == Nat.add(List.length(&2, U32, xs), k) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.trans(Nat, F.len.go(t, 1n+k), Nat.add(List.length(&2, U32, t), 1n+k), 1n+Nat.add(List.length(&2, U32, t), k),
        frame_len_go(t, 1n+k), NP.add_succ(List.length(&2, U32, t), k))

def frame_len(+xs: BL()) -> {F.len(xs) == List.length(&2, U32, xs) : Nat}:
  Equal.trans(Nat, F.len.go(xs, 0n), Nat.add(List.length(&2, U32, xs), 0n), List.length(&2, U32, xs),
    frame_len_go(xs, 0n), NP.add_zero(List.length(&2, U32, xs)))

# After the frame, every byte is rest (kept reversed).
def frame_feed_complete(xs: BL(), -m: BL(), r: BL())
  -> {F.feed.go(xs, F.Complete{m, r}) == F.Complete{m, B.rev(U32, xs, r)} : F.Reader}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      frame_feed_complete(t, m, h <> r)

# The body phase, h <> t to go (1 + len(t) bytes), consumes exactly h <> t.
def frame_body(t: BL(), h: U32, -rest: BL(), acc: BL())
  -> {F.feed.go(Con{h, List.append(&2, U32, t, rest)}, F.Body{List.length(&2, U32, t), acc})
      == F.feed.go(rest, F.Complete{B.rev(U32, B.rev(U32, t, h <> acc), Nil{}), Nil{}}) : F.Reader}:
  match t:
    case Nil{}:
      {==}
    case Con{h2, t2}:
      frame_body(t2, h2, rest, h <> acc)

# Once the prefix is read and the length fits.
def frame_fits(xs: BL(), +rest: BL())
  -> {F.finish(F.feed.go(List.append(&2, U32, xs, rest), F.body.start(True{}, List.length(&2, U32, xs))))
      == Done{F.Framed{xs, rest}} : FRes()}:
  match xs:
    case Nil{}:
      %Equal.sym(F.Reader, F.feed.go(rest, F.Complete{Nil{}, Nil{}}), F.Complete{Nil{}, B.rev(U32, rest, Nil{})}, frame_feed_complete(rest, Nil{}, Nil{})) :
        {F.finish(_) == Done{F.Framed{Nil{}, rest}} : FRes()}
      %Equal.sym(BL(), B.rev(U32, B.rev(U32, rest, Nil{}), Nil{}), rest, fr_rev_rev(U32, rest)) :
        {Done{F.Framed{Nil{}, _}} == Done{F.Framed{Nil{}, rest}} : FRes()}
      {==}
    case Con{+h, +t}:
      %Equal.sym(F.Reader, F.feed.go(Con{h, List.append(&2, U32, t, rest)}, F.Body{List.length(&2, U32, t), Nil{}}),
        F.feed.go(rest, F.Complete{B.rev(U32, B.rev(U32, t, [h]), Nil{}), Nil{}}), frame_body(t, h, rest, Nil{})) :
        {F.finish(_) == Done{F.Framed{Con{h, t}, rest}} : FRes()}
      %Equal.sym(F.Reader, F.feed.go(rest, F.Complete{B.rev(U32, B.rev(U32, t, [h]), Nil{}), Nil{}}),
        F.Complete{B.rev(U32, B.rev(U32, t, [h]), Nil{}), B.rev(U32, rest, Nil{})},
        frame_feed_complete(rest, B.rev(U32, B.rev(U32, t, [h]), Nil{}), Nil{})) :
        {F.finish(_) == Done{F.Framed{Con{h, t}, rest}} : FRes()}
      %Equal.sym(BL(), B.rev(U32, B.rev(U32, rest, Nil{}), Nil{}), rest, fr_rev_rev(U32, rest)) :
        {Done{F.Framed{B.rev(U32, B.rev(U32, t, [h]), Nil{}), _}} == Done{F.Framed{Con{h, t}, rest}} : FRes()}
      %Equal.sym(BL(), B.rev(U32, B.rev(U32, Con{h, t}, Nil{}), Nil{}), Con{h, t}, fr_rev_rev(U32, Con{h, t})) :
        {Done{F.Framed{_, rest}} == Done{F.Framed{Con{h, t}, rest}} : FRes()}
      {==}

def frame_after_prefix(+xs: BL(), +rest: BL(), +max: Nat, e1: {Nat.is_le(List.length(&2, U32, xs), max) == True{} : Bool})
  -> {F.finish(F.feed.go(List.append(&2, U32, xs, rest), F.body.start(Nat.is_le(List.length(&2, U32, xs), max), List.length(&2, U32, xs))))
      == Done{F.Framed{xs, rest}} : FRes()}:
  %Equal.sym(Bool, Nat.is_le(List.length(&2, U32, xs), max), True{}, e1) :
    {F.finish(F.feed.go(List.append(&2, U32, xs, rest), F.body.start(_, List.length(&2, U32, xs)))) == Done{F.Framed{xs, rest}} : FRes()}
  frame_fits(xs, rest)

# W's u16 law with nothing after the two bytes.
def frame_u16(+n: Nat, e: {Nat.is_le(n, 65535n) == True{} : Bool})
  -> {W.get_u16(W.put_u16(n)) == Some{M.Got{n, Nil{}}} : Maybe<&2, M.Got>}:
  Laws.u16_roundtrip(n, Nil{}, e)

def Laws.frame_roundtrip(xs, rest, max, e0, e1):
  +a = e0
  +b = e1
  %Equal.sym(Nat, F.len(xs), List.length(&2, U32, xs), frame_len(xs)) :
    {F.finish(F.feed.go(List.append(&2, U32, List.append(&2, U32, W.put_u16(_), xs), rest), F.Prefix0{max})) == Done{F.Framed{xs, rest}} : FRes()}
  %Equal.sym(Maybe<&2, M.Got>, W.get_u16(W.put_u16(List.length(&2, U32, xs))), Some{M.Got{List.length(&2, U32, xs), Nil{}}},
    frame_u16(List.length(&2, U32, xs), a)) :
    {F.finish(F.feed.go(List.append(&2, U32, xs, rest), F.length(max, _))) == Done{F.Framed{xs, rest}} : FRes()}
  frame_after_prefix(xs, rest, max, b)
