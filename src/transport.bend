import Base
import ./types.bend as M
import ./frame.bend as F

# The wire: one DNS query to one nameserver over TCP (RFC 1035 4.2.2,
# RFC 7766), with a timeout.
#
#   query(server, port, q, max, timeout_ms)
#     connect to server:port (an IPv4 address as text), send F.frame(q),
#     read 64 KiB at a time, feeding each read to the frame reader
#     (F.feed) until it is done (the frame complete, or failed) or the peer
#     closes (an empty read), close the socket, and answer the message bytes
#     (whatever followed the frame is dropped). The connect, the send and
#     each read must each finish within timeout_ms (0: no limit).
#
# Errors: a refused or failed connect is Connect{errno, text}; a failed
# send or read Io{errno, text}; a deadline passed Timeout{}; a query over
# 65535 bytes (it cannot be framed) or an announced response length over
# `max` Io{90 (EMSGSIZE), text}; a peer that closes inside the frame
# Malformed{Short{}}. Decoding the message is the caller's business.
#
# Only Base's effects are used (TCP.connect / send_bytes / recv_bytes,
# channels, sleep): no foreign code.

# Clamps
# ------

# A Nat as a U32 for a Base effect, saturating at 2^32-1 (U32's conversion
# would wrap).
def u32(n: Nat) -> U32:
  U32.from_nat(Nat.min(n, 4294967295n))

# A port for TCP.connect: anything past 65535 becomes 65536, which
# TCP.connect refuses with EINVAL (instead of wrapping into a valid port).
def port_u32(p: Nat) -> U32:
  U32.from_nat(Nat.min(p, 65536n))

# Racing an action against a deadline
# -----------------------------------
#
# `within(A, ms, act, reap)` is IO.within with two differences, the first
# from bender-http:
#  - its timer stops once the action wins. Base's IO.within sleeps the whole
#    `ms` in a computation nobody can cancel, and a program ends only when
#    every computation is done, so each read under IO.within(5000, ..) would
#    keep the program alive 5 s after the answer came. Here the timer sleeps
#    in slices of 100 ms and, after each, sends a Tick on the race's
#    channel; once the action has won the channel is closed, the next
#    Tick's send answers False, and the timer ends (at most 100 ms later).
#  - when the deadline wins, a reaper waits for the late action's result
#    and hands it to `reap`, which closes the socket inside it. So a connect
#    or read that completes after its deadline does not leak its socket.
#
# What neither version can do is cancel the action: Base has no way to abort
# a blocked recv or connect. When the deadline wins, the action keeps running
# (and keeps the program alive) until the peer acts or the OS gives up; only
# then does the reaper close its socket. That is the limit of a timeout over
# Base's TCP: a caller that must end at once after a Timeout (a command-line
# tool) exits explicitly (IO.die).

type Race<-A: Type> is Type:
  Won{value: A}
  Tick{}
  Late{}

def SLICE() -> Nat:
  100n

# The timer's next slice, once its Tick was taken (True) or refused (False:
# the race is over).
def timer.next(open: Bool, rest: IO(Bool)) -> IO(Bool):
  match open:
    case True{}:
      rest
    case False{}:
      IO.pure(Bool, False{})

# `n` slices of SLICE ms, each followed by a Tick, then `r` ms and Late.
def timer(-A: Type, n: Nat, r: Nat, +c: Chan(Race<A>)) -> IO(Bool):
  match n:
    case 0n:
      do IO<Bool>:
        IO.sleep(u32(r))
        Chan.send(Race<A>, c, Late{})
    case 1n+p:
      do IO<Bool>:
        IO.sleep(u32(SLICE()))
        open : Bool <- Chan.send(Race<A>, c, Tick{})
        timer.next(open, timer(A, p, r, c))

def join.won(-A: Type, +c: Chan(Race<A>), x: A) -> IO(Maybe<&1, A>):
  do IO<Maybe<&1, A>>:
    Chan.close(Race<A>, c)
    return Some{x}

def join.got(-A: Type, got: Maybe<&1, Race<A>>, +c: Chan(Race<A>), rest: IO(Maybe<&1, A>)) ->
  IO(Maybe<&1, A>):
  match got:
    case None{}:
      IO.pure(Maybe<&1, A>, None{})
    case Some{Won{x}}:
      join.won(A, c, x)
    case Some{Tick{}}:
      rest
    case Some{Late{}}:
      IO.pure(Maybe<&1, A>, None{})

# Waits for Won or Late, skipping Ticks; the fuel covers every message the
# timer can send (its ticks and Late) plus the action's one. A Won closes
# the channel (which stops the timer); a Late leaves it open for the reaper.
def join(-A: Type, fuel: Nat, +c: Chan(Race<A>)) -> IO(Maybe<&1, A>):
  match fuel:
    case 0n:
      IO.pure(Maybe<&1, A>, None{})
    case 1n+p:
      IO.bind(Maybe<&1, Race<A>>, Maybe<&1, A>, Chan.recv(Race<A>, c),
        got => join.got(A, got, c, join(A, p, c)))

def reaped(-A: Type, got: Maybe<&1, Race<A>>, +c: Chan(Race<A>), reap: A -> IO(Unit)) -> IO(Unit):
  match got:
    case Some{Won{x}}:
      do IO<Unit>:
        reap(x)
        Chan.close(Race<A>, c)
    case _:
      Chan.close(Race<A>, c)

# After a Late, the only message left is the action's Won (whenever the
# action ends): its value goes to reap.
def reaper(-A: Type, +c: Chan(Race<A>), reap: A -> IO(Unit)) -> IO(Unit):
  IO.bind(Maybe<&1, Race<A>>, Unit, Chan.recv(Race<A>, c), got => reaped(A, got, c, reap))

def decided(-A: Type, m: Maybe<&1, A>, +c: Chan(Race<A>), reap: A -> IO(Unit)) -> IO(Maybe<&1, A>):
  match m:
    case Some{x}:
      IO.pure(Maybe<&1, A>, Some{x})
    case None{}:
      do IO<Maybe<&1, A>>:
        IO.spawn(Unit, reaper(A, c, reap))
        return None{}

def race.go(-A: Type, n: Nat, r: Nat, act: IO(A), reap: A -> IO(Unit), +c: Chan(Race<A>)) -> IO(Maybe<&1, A>):
  +slices = n
  do IO<Maybe<&1, A>>:
    IO.spawn(Bool, IO.bind(A, Bool, act, x => Chan.send(Race<A>, c, Won{x})))
    IO.spawn(Bool, timer(A, slices, r, c))
    m : Maybe<&1, A> <- join(A, 3n+slices, c)
    decided(A, m, c, reap)

# `nr` is the deadline as (whole slices, remaining ms).
def race(-A: Type, nr: Nat & Nat, act: IO(A), reap: A -> IO(Unit)) -> IO(Maybe<&1, A>):
  (n, r) = nr
  IO.bind(Chan(Race<A>), Maybe<&1, A>, Chan.new(Race<A>, 1), c => race.go(A, n, r, act, reap, c))

# Some{result} if `act` finishes within `ms` milliseconds, else None (and
# the late result goes to reap); 0 means no limit.
def within(-A: Type, ms: Nat, act: IO(A), reap: A -> IO(Unit)) -> IO(Maybe<&1, A>):
  match ms:
    case 0n:
      IO.bind(A, Maybe<&1, A>, act, x => IO.pure(Maybe<&1, A>, Some{x}))
    case 1n+p:
      race(A, Nat.divmod(1n+p, SLICE()), act, reap)

# Reapers: close the socket a late effect hands back.
def reap_connect(r: Result<&1, &1, U32 & String, Socket>) -> IO(Unit):
  match r:
    case Done{sock}:
      Socket.close(sock)
    case Fail{e}:
      IO.pure(Unit, Unit{})

def reap_sent(p: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (sock, r) = p
  Socket.close(sock)

def reap_read(p: Socket & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Unit):
  (sock, r) = p
  Socket.close(sock)

# One query over TCP
# ------------------

def Answer() -> Type:
  IO(Result<&2, &2, M.Error, List<&2, U32>>)

def fail(e: M.Error) -> Answer():
  IO.pure(Result<&2, &2, M.Error, List<&2, U32>>, Fail{e})

def EMSGSIZE() -> U32:
  90

# The frame reader's verdict at the end of input, as the resolver's error.
def verdict(+max: Nat, r: Result<&2, &2, F.FrameError, F.Framed>) -> Result<&2, &2, M.Error, List<&2, U32>>:
  match r:
    case Done{fr}:
      match fr:
        case F.Framed{m, rest}:
          Done{m}
    case Fail{e}:
      match e:
        case F.Cut{}:
          Fail{M.Malformed{M.Short{}}}
        case F.TooLarge{n}:
          Fail{M.Io{EMSGSIZE(), "response of " ++ Nat.show(n) ++ " bytes is over the limit of "
            ++ Nat.show(max) ++ " bytes"}}
        case F.NotByte{}:
          Fail{M.Malformed{M.Short{}}}

# Closes the socket, then answers the reader's verdict on s.
def close_with(sock: Socket, +max: Nat, s: F.Reader) -> Answer():
  do IO<Result<&2, &2, M.Error, List<&2, U32>>>:
    Socket.close(sock)
    return verdict(max, F.finish(s))

def close_fail(sock: Socket, e: M.Error) -> Answer():
  do IO<Result<&2, &2, M.Error, List<&2, U32>>>:
    Socket.close(sock)
    return Fail{e}

# After a productive read: stop when the reader is done, else read again.
def fed(done: Bool, sock: Socket, +max: Nat, s: F.Reader, more: Socket -> F.Reader -> Answer()) -> Answer():
  match done:
    case True{}:
      close_with(sock, max, s)
    case False{}:
      more(sock, s)

# What one read brought: an empty read is the peer's close (the end of
# input); otherwise feed the bytes to the reader.
def got(xs: List<&2, U32>, sock: Socket, +max: Nat, s: F.Reader, more: Socket -> F.Reader -> Answer()) -> Answer():
  match xs:
    case Nil{}:
      close_with(sock, max, s)
    case Con{h, t}:
      +s2 = F.feed(s, h <> t)
      fed(F.done(s2), sock, max, s2, more)

# One read's outcome: the deadline passed (the reaper closes the socket when
# the read ends), the read failed, or it brought bytes.
def read_got(r: Maybe<&1, Socket & Result<&1, &1, U32 & String, List<&2, U32>>>, +max: Nat, s: F.Reader,
  more: Socket -> F.Reader -> Answer()) -> Answer():
  match r:
    case None{}:
      fail(M.Timeout{})
    case Some{(sock, res)}:
      match res:
        case Fail{(code, message)}:
          close_fail(sock, M.Io{code, message})
        case Done{xs}:
          got(xs, sock, max, s, more)

# Reads until the reader is done or the peer closes. Each productive read
# either finishes the reader or takes at least one of the at most max + 2
# bytes the frame can hold, so fuel = max + 3 reads always suffice; running
# out is reported as the end of input.
def read_loop(fuel: Nat, sock: Socket, +max: Nat, s: F.Reader, +ms: Nat) -> Answer():
  match fuel:
    case 0n:
      close_with(sock, max, s)
    case 1n+p:
      IO.bind(Maybe<&1, Socket & Result<&1, &1, U32 & String, List<&2, U32>>>,
        Result<&2, &2, M.Error, List<&2, U32>>,
        within(Socket & Result<&1, &1, U32 & String, List<&2, U32>>, ms, TCP.recv_bytes(sock, 65536),
          reap_read),
        r => read_got(r, max, s, sock2 => s2 => read_loop(p, sock2, max, s2, ms)))

# The query was sent (or not): on success, read the response.
def sent(r: Maybe<&1, Socket & Result<&1, &1, U32 & String, Unit>>, +max: Nat, +ms: Nat) -> Answer():
  match r:
    case None{}:
      fail(M.Timeout{})
    case Some{(sock, res)}:
      match res:
        case Fail{(code, message)}:
          close_fail(sock, M.Io{code, message})
        case Done{u}:
          read_loop(3n+max, sock, max, F.init(max), ms)

# Connected (or not): on success, send the framed query.
def connected(r: Maybe<&1, Result<&1, &1, U32 & String, Socket>>, framed: List<&2, U32>, max: Nat, +ms: Nat) ->
  Answer():
  match r:
    case None{}:
      fail(M.Timeout{})
    case Some{res}:
      match res:
        case Fail{(code, message)}:
          fail(M.Connect{code, message})
        case Done{sock}:
          IO.bind(Maybe<&1, Socket & Result<&1, &1, U32 & String, Unit>>,
            Result<&2, &2, M.Error, List<&2, U32>>,
            within(Socket & Result<&1, &1, U32 & String, Unit>, ms, TCP.send_bytes(sock, framed), reap_sent),
            s => sent(s, max, ms))

def exchange(fits: Bool, server: String, port: Nat, +q: List<&2, U32>, max: Nat, +ms: Nat) -> Answer():
  match fits:
    case True{}:
      IO.bind(Maybe<&1, Result<&1, &1, U32 & String, Socket>>, Result<&2, &2, M.Error, List<&2, U32>>,
        within(Result<&1, &1, U32 & String, Socket>, ms, TCP.connect(server, port_u32(port)), reap_connect),
        r => connected(r, F.frame(q), max, ms))
    case False{}:
      fail(M.Io{EMSGSIZE(), "query of " ++ Nat.show(F.len(q)) ++ " bytes is over 65535 bytes"})

# One exchange with server:port: see the top of the file. `max` bounds the
# response message (65535 accepts any frame). The socket is closed on every
# path; after a Timeout, when the stalled effect ends (see `within`).
def query(server: String, port: Nat, +q: List<&2, U32>, max: Nat, +timeout_ms: Nat) -> Answer():
  exchange(Nat.is_le(F.len(q), 65535n), server, port, q, max, timeout_ms)
