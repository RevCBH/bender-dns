import Base
import ../src/types.bend as M
import ../src/encode.bend as E
import ../src/decode.bend as D

# Checker-evaluated tests for encode.bend (and the roundtrip through
# decode.bend): `bend tests/encode_test.bend --check-only` printing ALL
# PROOFS CHECK is a pass (a plain run checks every def the same way, then
# prints main's Unit{}). One def per group; the checker computes Nat in
# unary, so numbers stay small (tests/codec_run.bend covers full ranges).

def BS() -> Type:
  List<&2, U32>

def R() -> Type:
  Result<&2, &2, M.DecodeError, M.Message>

# example.com
def ex() -> M.Name():
  [[101, 120, 97, 109, 112, 108, 101], [99, 111, 109]]

def hd() -> M.Header:
  M.Header{4660n, True{}, 0n, False{}, False{}, True{}, True{}, False{}, False{}, 0n}

def rec(t: M.RType, d: M.RData) -> M.Record:
  M.Record{ex(), t, M.CIN{}, 300n, d}

def with_answers(an: List<&2, M.Record>) -> M.Message:
  M.Message{hd(), [M.Question{ex(), M.TA{}, M.CIN{}}], an, Nil{}, Nil{}}

# One record of every RDATA form, small numbers, every flag set.
def every() -> M.Message:
  M.Message{M.Header{258n, True{}, 15n, True{}, True{}, True{}, True{}, True{}, True{}, 15n},
    [M.Question{ex(), M.TANY{}, M.CIN{}}, M.Question{[], M.TOther{99n}, M.COther{3n}}],
    [rec(M.TA{}, M.RIpv4{1n, 2n, 255n, 0n}),
     rec(M.TAAAA{}, M.RIpv6{[1n, 0n, 0n, 0n, 0n, 0n, 0n, 255n]}),
     rec(M.TNS{}, M.RName{[[110, 115], [65, 66]]}),
     rec(M.TCNAME{}, M.RName{[]}),
     rec(M.TPTR{}, M.RName{ex()}),
     rec(M.TMX{}, M.RMx{10n, ex()})],
    [rec(M.TTXT{}, M.RTxt{[[118, 61], [], [0, 255]]}),
     rec(M.TTXT{}, M.RTxt{[]}),
     rec(M.TSOA{}, M.RSoa{ex(), [[104], [109]], 1n, 2n, 3n, 4n, 5n}),
     rec(M.TSRV{}, M.RSrv{1n, 2n, 443n, ex()})],
    [M.Record{[], M.TOPT{}, M.COther{512n}, 0n, M.RRaw{[0, 10, 0, 2, 1, 2]}},
     M.Record{ex(), M.TOther{99n}, M.COther{254n}, 0n, M.RRaw{[1, 2, 3]}},
     M.Record{ex(), M.TANY{}, M.CIN{}, 7n, M.RRaw{[]}}]}

def query_bytes() ->
  {E.query(4660n, ex(), M.TA{}) == [18, 52, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1,
     7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0, 0, 1, 0, 1,
     0, 0, 41, 16, 0, 0, 0, 0, 0, 0, 0] : BS()} &
  {E.query_plain(4660n, ex(), M.TMX{}) == [18, 52, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0,
     7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0, 0, 15, 0, 1] : BS()} &
  {E.query(1n, [], M.TNS{}) == [0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 1,
     0, 0, 41, 16, 0, 0, 0, 0, 0, 0, 0] : BS()}:
  ({==}, {==}, {==})

def query_ok() ->
  {E.message_ok(E.query_message(4660n, ex(), M.TA{})) == True{} : Bool} &
  {E.message_ok(E.query_plain_message(4660n, ex(), M.TAAAA{})) == True{} : Bool} &
  {D.message(E.query(4660n, ex(), M.TA{})) == Done{E.query_message(4660n, ex(), M.TA{})} : R()} &
  {D.message(E.query_plain(4660n, ex(), M.TSRV{})) == Done{E.query_plain_message(4660n, ex(), M.TSRV{})} : R()}:
  ({==}, {==}, {==}, {==})

def message_bytes() ->
  {E.message(with_answers([rec(M.TA{}, M.RIpv4{1n, 2n, 3n, 4n})])) == [18, 52, 129, 128, 0, 1, 0, 1, 0, 0, 0, 0,
     7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0, 0, 1, 0, 1,
     7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0, 0, 1, 0, 1, 0, 0, 1, 44, 0, 4, 1, 2, 3, 4] : BS()} &
  {E.rdata(M.RMx{10n, [[97]]}) == [0, 10, 1, 97, 0] : BS()} &
  {E.rdata(M.RTxt{[[118, 61], [], [0]]}) == [2, 118, 61, 0, 1, 0] : BS()} &
  {E.rdata(M.RIpv6{[1n, 0n, 0n, 0n, 0n, 0n, 0n, 258n]}) == [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2] : BS()} &
  {E.rdata(M.RSrv{1n, 2n, 3n, []}) == [0, 1, 0, 2, 0, 3, 0] : BS()} &
  {E.rdata(M.RSoa{[], [[97]], 1n, 2n, 3n, 4n, 5n}) == [0, 1, 97, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 5] : BS()} &
  {E.flags_hi(True{}, 15n, True{}, True{}, True{}) == 255n : Nat} &
  {E.flags_lo(True{}, True{}, True{}, 15n) == 191n : Nat}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def every_ok() ->
  {E.message_ok(every()) == True{} : Bool}:
  {==}

def every_roundtrip() ->
  {D.message(E.message(every())) == Done{every()} : R()}:
  {==}

# message_ok refuses: type and RDATA disagreeing, a TOther or COther with a
# known code, numbers out of range, 7 groups, a bad name, a non-byte.
def refused() ->
  {E.message_ok(with_answers([rec(M.TA{}, M.RRaw{[1, 2, 3, 4]})])) == False{} : Bool} &
  {E.message_ok(with_answers([rec(M.TMX{}, M.RIpv4{1n, 2n, 3n, 4n})])) == False{} : Bool} &
  {E.message_ok(with_answers([rec(M.TOther{1n}, M.RRaw{[1, 2, 3, 4]})])) == False{} : Bool} &
  {E.message_ok(with_answers([rec(M.TOther{28n}, M.RRaw{[]})])) == False{} : Bool} &
  {E.message_ok(with_answers([M.Record{ex(), M.TA{}, M.COther{1n}, 0n, M.RIpv4{1n, 2n, 3n, 4n}}])) == False{} : Bool} &
  {E.message_ok(with_answers([rec(M.TA{}, M.RIpv4{1n, 2n, 3n, 256n})])) == False{} : Bool} &
  {E.message_ok(with_answers([rec(M.TAAAA{}, M.RIpv6{[1n, 2n, 3n, 4n, 5n, 6n, 7n]})])) == False{} : Bool} &
  {E.message_ok(with_answers([rec(M.TNS{}, M.RName{[[]]})])) == False{} : Bool} &
  {E.message_ok(with_answers([rec(M.TOPT{}, M.RRaw{[256]})])) == False{} : Bool} &
  {E.message_ok(with_answers([rec(M.TTXT{}, M.RTxt{[[97, 256]]})])) == False{} : Bool} &
  {E.message_ok(with_answers([M.Record{[[97, 256]], M.TA{}, M.CIN{}, 0n, M.RIpv4{1n, 2n, 3n, 4n}}])) == False{} : Bool} &
  {E.message_ok(M.Message{M.Header{1n, False{}, 16n, False{}, False{}, False{}, False{}, False{}, False{}, 0n},
     Nil{}, Nil{}, Nil{}, Nil{}}) == False{} : Bool} &
  {E.message_ok(M.Message{M.Header{1n, False{}, 0n, False{}, False{}, False{}, False{}, False{}, False{}, 16n},
     Nil{}, Nil{}, Nil{}, Nil{}}) == False{} : Bool}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def codes() ->
  {E.type_known(41n) == Some{M.TOPT{}} : Maybe<&2, M.RType>} &
  {E.type_known(42n) == None{} : Maybe<&2, M.RType>} &
  {E.type_code(M.TSRV{}) == 33n : Nat} &
  {E.class_code(M.COther{3n}) == 3n : Nat} &
  {E.u32_ok(300n) == True{} : Bool} &
  {E.count(U32, [1, 2, 3]) == 3n : Nat}:
  ({==}, {==}, {==}, {==}, {==}, {==})

def main() -> Unit:
  Unit{}
