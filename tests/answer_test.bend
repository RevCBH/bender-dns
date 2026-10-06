import Base
import ../src/types.bend as M
import ../src/answer.bend as A
import ./fixtures.bend as FX

# Checker-evaluated tests for answer.bend: `bend tests/answer_test.bend --check-only`
# printing ALL PROOFS CHECK is a pass (a plain run checks every def the same
# way, then prints main's Unit{}). The cases sit in one def per group, as
# in decode_test.bend. The real responses are tests/fixtures.bend's (as decoded; tests/decode_test.bend checks the
# decoding); tests/codec_run.bend runs addresses on them after decoding.

def Ans() -> Type:
  M.Answer

def ex() -> M.Name():
  [[101, 120, 97, 109, 112, 108, 101], [99, 111, 109]]

def ex_upper() -> M.Name():
  [[69, 88, 97, 77, 112, 108, 101], [67, 111, 77]]

def www_github() -> M.Name():
  [[119, 119, 119], [103, 105, 116, 104, 117, 98], [99, 111, 109]]

def github() -> M.Name():
  [[103, 105, 116, 104, 117, 98], [99, 111, 109]]

def gmail() -> M.Name():
  [[103, 109, 97, 105, 108], [99, 111, 109]]

def hd(id: Nat, qr: Bool, op: Nat, tc: Bool, rc: Nat) -> M.Header:
  M.Header{id, qr, op, False{}, tc, True{}, True{}, False{}, False{}, rc}

def qa(n: M.Name()) -> M.Question:
  M.Question{n, M.TA{}, M.CIN{}}

def resp(qs: List<&2, M.Question>, an: List<&2, M.Record>) -> M.Message:
  M.Message{hd(7n, True{}, 0n, False{}, 0n), qs, an, Nil{}, Nil{}}

def a(n: M.Name(), x: Nat) -> M.Record:
  M.Record{n, M.TA{}, M.CIN{}, 60n, M.RIpv4{10n, 0n, 0n, x}}

def cn(n: M.Name(), t: M.Name()) -> M.Record:
  M.Record{n, M.TCNAME{}, M.CIN{}, 60n, M.RName{t}}

# The one-label name [[k]].
def nk(k: U32) -> M.Name():
  [[k]]

# CNAMEs [[k]] -> [[k + 1]] for k = from .. from + n - 1, onto acc (built backwards).
def chain.go(n: Nat, +from: Nat, acc: List<&2, M.Record>) -> List<&2, M.Record>:
  match n:
    case 0n:
      acc
    case 1n+(+p):
      chain.go(p, from, cn(nk(U32.from_nat(Nat.add(from, p))), nk(U32.from_nat(1n+Nat.add(from, p)))) <> acc)

# n CNAMEs from [[97]] on, then an A record at the end of the chain.
def long(+n: Nat) -> M.Message:
  resp([qa(nk(97))], List.append(&2, M.Record, chain.go(n, 97n, Nil{}), [a(nk(U32.from_nat(Nat.add(97n, n))), 1n)]))

def accept() ->
  {A.accept(4660n, qa(ex()), FX.example_a.msg()) == True{} : Bool} &
  {A.accept(4660n, qa(ex_upper()), FX.example_a.msg()) == True{} : Bool} &
  {A.accept(4661n, qa(ex()), FX.example_a.msg()) == False{} : Bool} &
  {A.accept(4660n, M.Question{ex(), M.TAAAA{}, M.CIN{}}, FX.example_a.msg()) == False{} : Bool} &
  {A.accept(4660n, M.Question{ex(), M.TA{}, M.COther{3n}}, FX.example_a.msg()) == False{} : Bool} &
  {A.accept(4660n, qa(github()), FX.example_a.msg()) == False{} : Bool} &
  {A.accept(7n, qa(ex()), resp([qa(ex())], Nil{})) == True{} : Bool} &
  {A.accept(7n, qa(ex()), resp([qa(ex()), qa(ex())], Nil{})) == False{} : Bool} &
  {A.accept(7n, qa(ex()), resp(Nil{}, Nil{})) == False{} : Bool} &
  {A.accept(7n, qa(ex()), M.Message{hd(7n, False{}, 0n, False{}, 0n), [qa(ex())], Nil{}, Nil{}, Nil{}}) == False{} : Bool} &
  {A.accept(7n, qa(ex()), M.Message{hd(7n, True{}, 2n, False{}, 0n), [qa(ex())], Nil{}, Nil{}, Nil{}}) == False{} : Bool} &
  # rcode and TC are not judged by accept
  {A.accept(7n, qa(ex()), M.Message{hd(7n, True{}, 0n, True{}, 3n), [qa(ex())], Nil{}, Nil{}, Nil{}}) == True{} : Bool}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def header() ->
  {A.rcode(M.Message{hd(7n, True{}, 0n, True{}, 3n), Nil{}, Nil{}, Nil{}, Nil{}}) == 3n : Nat} &
  {A.truncated(M.Message{hd(7n, True{}, 0n, True{}, 3n), Nil{}, Nil{}, Nil{}, Nil{}}) == True{} : Bool} &
  {A.rcode(FX.example_a.msg()) == 0n : Nat} &
  {A.truncated(FX.example_a.msg()) == False{} : Bool}:
  ({==}, {==}, {==}, {==})

def real() ->
  {A.addresses(ex(), M.TA{}, FX.example_a.msg())
    == M.Found{ex(), [M.Record{ex(), M.TA{}, M.CIN{}, 300n, M.RIpv4{104n, 20n, 23n, 154n}},
                      M.Record{ex(), M.TA{}, M.CIN{}, 300n, M.RIpv4{172n, 66n, 147n, 243n}}]} : Ans()} &
  {A.addresses(ex_upper(), M.TA{}, FX.example_a.msg())
    == M.Found{ex_upper(), [M.Record{ex(), M.TA{}, M.CIN{}, 300n, M.RIpv4{104n, 20n, 23n, 154n}},
                            M.Record{ex(), M.TA{}, M.CIN{}, 300n, M.RIpv4{172n, 66n, 147n, 243n}}]} : Ans()} &
  {A.addresses(www_github(), M.TA{}, FX.github_cname.msg())
    == M.Found{github(), [M.Record{github(), M.TA{}, M.CIN{}, 60n, M.RIpv4{140n, 82n, 121n, 3n}}]} : Ans()} &
  {A.addresses(www_github(), M.TCNAME{}, FX.github_cname.msg())
    == M.Found{www_github(), [M.Record{www_github(), M.TCNAME{}, M.CIN{}, 3410n, M.RName{github()}}]} : Ans()} &
  {A.addresses(www_github(), M.TANY{}, FX.github_cname.msg())
    == M.Found{www_github(), [M.Record{www_github(), M.TCNAME{}, M.CIN{}, 3410n, M.RName{github()}}]} : Ans()} &
  {A.addresses(ex(), M.TAAAA{}, FX.example_a.msg()) == M.Nothing{} : Ans()} &
  {A.addresses(github(), M.TA{}, FX.example_a.msg()) == M.Nothing{} : Ans()} &
  {A.addresses(www_github(), M.TMX{}, FX.github_cname.msg()) == M.Alias{github()} : Ans()} &
  {A.addresses(ex(), M.TA{}, FX.example_a_edns.msg())
    == M.Found{ex(), [M.Record{ex(), M.TA{}, M.CIN{}, 300n, M.RIpv4{104n, 20n, 23n, 154n}},
                      M.Record{ex(), M.TA{}, M.CIN{}, 300n, M.RIpv4{172n, 66n, 147n, 243n}}]} : Ans()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def answers(m: M.Message) -> List<&2, M.Record>:
  match m:
    case M.Message{h, qs, an, ns, ar}:
      an

# all five MX records, in order
def mx() ->
  {A.addresses(gmail(), M.TMX{}, FX.gmail_mx.msg()) == M.Found{gmail(), answers(FX.gmail_mx.msg())} : Ans()}:
  {==}

def chains() ->
  # an alias only: the chain leaves the answer section
  {A.addresses(nk(97), M.TA{}, resp([qa(nk(97))], [cn(nk(97), nk(98))])) == M.Alias{nk(98)} : Ans()} &
  # two hops, records in any order, other owners ignored
  {A.addresses(nk(97), M.TA{}, resp([qa(nk(97))],
     [a(nk(99), 1n), a(nk(100), 9n), cn(nk(98), nk(99)), cn(nk(97), nk(98)), a(nk(99), 2n)]))
    == M.Found{nk(99), [a(nk(99), 1n), a(nk(99), 2n)]} : Ans()} &
  # records at the question name win over its CNAME
  {A.addresses(nk(97), M.TA{}, resp([qa(nk(97))], [cn(nk(97), nk(98)), a(nk(97), 1n), a(nk(98), 2n)]))
    == M.Found{nk(97), [a(nk(97), 1n)]} : Ans()} &
  # the first CNAME is followed
  {A.addresses(nk(97), M.TA{}, resp([qa(nk(97))], [cn(nk(97), nk(98)), cn(nk(97), nk(99)), a(nk(98), 2n), a(nk(99), 3n)]))
    == M.Found{nk(98), [a(nk(98), 2n)]} : Ans()} &
  # a loop
  {A.addresses(nk(97), M.TA{}, resp([qa(nk(97))], [cn(nk(97), nk(98)), cn(nk(98), nk(97))])) == M.Nothing{} : Ans()} &
  # case-insensitive owners
  {A.addresses(nk(65), M.TA{}, resp([qa(nk(65))], [cn(nk(97), nk(66)), a(nk(98), 5n)]))
    == M.Found{nk(66), [a(nk(98), 5n)]} : Ans()} &
  # 16 hops are followed, 17 are not
  {A.addresses(nk(97), M.TA{}, long(16n)) == M.Found{nk(113), [a(nk(113), 1n)]} : Ans()} &
  {A.addresses(nk(97), M.TA{}, long(17n)) == M.Nothing{} : Ans()} &
  # nothing at all
  {A.addresses(nk(97), M.TA{}, resp([qa(nk(97))], Nil{})) == M.Nothing{} : Ans()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def main() -> Unit:
  Unit{}
