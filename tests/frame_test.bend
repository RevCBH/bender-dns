import Base
import ../src/frame.bend as F

# Checker-evaluated tests for frame.bend: `bend tests/frame_test.bend` (or
# --check-only) printing ALL PROOFS CHECK is a pass. tests/core_run.bend
# covers 65535-byte frames and long streams.

def BS() -> Type:
  List<&2, U32>

def R() -> Type:
  Result<&2, &2, F.FrameError, F.Framed>

def main() ->
  # frame
  {F.frame([]) == [0, 0] : BS()} &
  {F.frame([7, 8, 9]) == [0, 3, 7, 8, 9] : BS()} &
  # read
  {F.read(512n, [0, 3, 7, 8, 9]) == Done{F.Framed{[7, 8, 9], []}} : R()} &
  {F.read(512n, [0, 3, 7, 8, 9, 1, 2]) == Done{F.Framed{[7, 8, 9], [1, 2]}} : R()} &
  {F.read(512n, [0, 0]) == Done{F.Framed{[], []}} : R()} &
  {F.read(0n, [0, 0, 5]) == Done{F.Framed{[], [5]}} : R()} &
  {F.read(3n, [0, 3, 7, 8, 9]) == Done{F.Framed{[7, 8, 9], []}} : R()} &
  {F.read(2n, [0, 3, 7, 8, 9]) == Fail{F.TooLarge{3n}} : R()} &
  {F.read(255n, [1, 0, 7]) == Fail{F.TooLarge{256n}} : R()} &
  {F.read(512n, [1, 0, 7]) == Fail{F.Cut{}} : R()} &
  {F.read(512n, []) == Fail{F.Cut{}} : R()} &
  {F.read(512n, [0]) == Fail{F.Cut{}} : R()} &
  {F.read(512n, [0, 3, 7, 8]) == Fail{F.Cut{}} : R()} &
  {F.read(512n, [0, 256, 1]) == Fail{F.NotByte{}} : R()} &
  {F.read(512n, F.frame([1, 2, 3, 4])) == Done{F.Framed{[1, 2, 3, 4], []}} : R()} &
  # feed in pieces, done
  {F.finish(F.feed(F.feed(F.init(9n), [0]), [2, 5, 6, 7])) == Done{F.Framed{[5, 6], [7]}} : R()} &
  {F.feed(F.feed(F.init(9n), [0, 2]), [5, 6]) == F.feed(F.init(9n), [0, 2, 5, 6]) : F.Reader} &
  {F.done(F.feed(F.init(9n), [0, 2, 5])) == False{} : Bool} &
  {F.done(F.feed(F.init(9n), [0, 2, 5, 6])) == True{} : Bool} &
  {F.done(F.feed(F.init(1n), [0, 2])) == True{} : Bool} &
  {F.done(F.init(1n)) == False{} : Bool}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
