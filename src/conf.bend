import Base
import ./bytes.bend as B
import ./num.bend as N
import ./types.bend as M

# /etc/resolv.conf and /etc/hosts, and the search-list expansion of a name.
#
#   resolv(text)            -> M.Conf          resolv.conf(5)
#   hosts(text)             -> [M.HostEntry]   hosts(5)
#   hosts_lookup(es, name)  -> [address]       ASCII case-insensitive
#   candidates(conf, name)  -> [name]          the names the resolver tries
#
# Both files are read in two steps: `lines` turns the text into lines of
# words (comments dropped, empty lines dropped), then a fold over the lines
# builds the result. Every def that walks file-sized text or lists (the
# text, its lines, the words of a line, the entries of a big hosts file) is
# a loop: it recurses only by a direct tail call (the JS lane's stack
# overflows near 20-40k nested calls; an ad-blocking /etc/hosts has 100k
# lines).
#
# NOTE (loops and specs). Two kinds of loop:
#  - Left folds whose step is O(1) (tok.go over the chars, resolv.go over the
#    lines, options.go over the options, dg.go over a number's chars). Each is
#    already a plain structural recursion: it is its own spec. The lemma a
#    proof needs is the split law, by induction on the first list:
#      tok.go(String.append(a, b), semi, st) == tok.go(b, semi, tok.go(a, semi, st))
#      resolv.go(List.append(a, b), c) == resolv.go(b, resolv.go(a, c))
#  - Map/filter loops that build a list in reverse and turn it around once.
#    The structural recursion each computes stays beside it as `<name>.spec`
#    (nothing calls a spec at runtime); one lemma per pair, by induction
#    with the accumulator generalized:
#      hosts.go(ls, acc) == B.rev(M.HostEntry, acc, hosts.spec(ls))
#      lookup.go(l, es, acc) == B.rev(String, acc, lookup.spec(l, es))
#      any_name.go(l, ns, found) == Bool.or(found, any_name.spec(l, ns))
#      same.go(a, b, ok) == Bool.and(ok, String.eq(a, b))
#      expand.go(n, ss, acc) == B.rev(String, expand.spec(n, ss), acc)
#      lower.go(s, acc) == String.reverse.go(acc, lower.spec(s))
#    and so, at acc = Nil{} / False{} / SNil{}:
#      hosts(text) == hosts.spec(lines(text, False{}))
#      hosts_lookup(es, n) == lookup.spec(lower(n), es)
#      lower == lower.spec
#      candidates: as-is first gives  name <> expand.spec(name, search),
#                  as-is last gives   List.append(expand.spec(name, search), [name]).
#
# What resolv reads (resolv.conf(5), glibc's res_init where the page is
# silent; DESIGN.md):
#  - Words are separated by spaces, tabs and CRs (so a CRLF file reads like
#    an LF one). A '#' or ';' starts a comment that runs to the end of the
#    line, wherever it is (glibc honours them only in column 1; here a
#    trailing comment never becomes a search domain or an option). Leading
#    whitespace is allowed. Keywords are case-sensitive, as in glibc.
#  - `nameserver ADDR`: the first word after the keyword; kept only if it is
#    a canonical dotted-quad IPv4 address (is_ipv4: no leading zeros, octets
#    0..255; IPv6 and scoped addresses are skipped, because Base's
#    TCP.connect reaches IPv4 only). At most 3 are kept (glibc's MAXNS): the
#    first 3 IPv4 ones, in file order.
#  - `search D...` and `domain D`: the last such line wins, and replaces the
#    whole search list (`domain` gives a one-entry list). A `search` or
#    `domain` line with no value is ignored, as glibc does. No search line
#    means an empty list (glibc would fall back to the host name's domain,
#    which this pure parser cannot know).
#  - `options`: each word; `ndots:N` (clamped to 0..15, glibc's
#    RES_MAXNDOTS), `timeout:N` (clamped to 1..30, RES_MAXRETRANS),
#    `attempts:N` (clamped to 1..5, RES_MAXRETRY). N is read like atoi: its
#    leading decimal digits ("3x" is 3); an option with no digit at all is
#    ignored (atoi would give 0). A huge N ("ndots:999999999999") clamps to
#    the maximum without ever being computed: only its significant digits
#    are counted (see Numbers). timeout:0 and attempts:0 become 1 (glibc
#    turns timeout 0 into a 1 second wait; attempts 0 would never query).
#    Other options (rotate, edns0, ...) are ignored. Later options win.
#  - Any other line is ignored. Defaults: no nameservers (the resolver
#    decides what that means), no search list, ndots 1, timeout 5,
#    attempts 2.
#
# What hosts reads (hosts(5)): '#' starts a comment (';' is an ordinary
# char there); each remaining line is an address then one or more names;
# a line with an address and no name is skipped. The address is kept as
# written: the resolver checks it when it turns an entry into a record.

# The conf char classifier
# ------------------------
#
# Every char is classified once, by `cclass`, and every cut and test here
# dispatches on the CClass (as url.bend's uclass in bender-http).
#
# NOTE (classifier use): cclass refines B.char_class. '#' and '.' share the
# Tchar class with other marks, so only inside that branch is the char
# compared with a literal (Char.is_eq); everything else comes straight from
# the B.Class. Case folding (lower_char) decides 'A'..'Z' with the classifier
# alone, as bender-http's headers.bend does.
type CClass is Data:
  KSpace{}              # SP, HTAB, CR: separates words
  KLine{}               # LF: ends a line
  KHash{}               # '#': starts a comment
  KSemi{}               # ';': starts a comment in resolv.conf
  KDot{}                # '.'
  KColon{}              # ':'
  KDigit{value: Nat}    # '0'..'9'
  KOther{}              # any other char

def tchar_kind(+c: Char) -> CClass:
  Bool.pick(CClass, Char.is_eq(c, '#'), KHash{},
  Bool.pick(CClass, Char.is_eq(c, '.'), KDot{},
  KOther{}))

def cclass.of(k: B.Class, +c: Char) -> CClass:
  match k:
    case B.Digit{v}:
      KDigit{v}
    case B.Sp{}:
      KSpace{}
    case B.Htab{}:
      KSpace{}
    case B.Cr{}:
      KSpace{}
    case B.Lf{}:
      KLine{}
    case B.Semi{}:
      KSemi{}
    case B.Colon{}:
      KColon{}
    case B.Tchar{}:
      tchar_kind(c)
    case _:
      KOther{}

# The conf class of a char.
def cclass(+c: Char) -> CClass:
  cclass.of(B.char_class(c), c)

def CClass.is_dot(k: CClass) -> Bool:
  match k:
    case KDot{}:
      True{}
    case _:
      False{}

# Case folding
# ------------

# Letter or HexLetter: an ASCII letter of either case.
def is_letter(k: B.Class) -> Bool:
  match k:
    case B.HexLetter{v}:
      True{}
    case B.Letter{}:
      True{}
    case _:
      False{}

# The code 32 places up: the same letter in lowercase, for 'A'..'Z'.
def up32(x: U32) -> U32:
  (x + 32 : U32)

# 'A'..'Z': class(c) is a letter, class(c + 32) is a letter, class(c + 64)
# is not (for 'a'..'z', c + 32 is High; for 'A'..'Z', c + 64 is High).
def is_upper(+c: Char) -> Bool:
  +x = Char.to_u32(c)
  is_letter(B.class(x)) && is_letter(B.class(up32(x)))
    && Bool.not(is_letter(B.class(up32(up32(x)))))

def lower_char.pick(up: Bool, +c: Char) -> Char:
  match up:
    case True{}:
      Char.from_u32(up32(Char.to_u32(c)))
    case False{}:
      c

# 'A'..'Z' to 'a'..'z'; every other char unchanged.
def lower_char(+c: Char) -> Char:
  lower_char.pick(is_upper(c), c)

def lower.spec(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      SCon{lower_char(c), lower.spec(t)}

def lower.go(s: String, acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{c, t}:
      lower.go(t, SCon{lower_char(c), acc})

# ASCII letters to lowercase; everything else unchanged.
def lower(s: String) -> String:
  lower.go(s, SNil{})

# Lines of words
# --------------

# The tokenizer's state: the word being read (reversed), the words of the
# line being read (reversed), the finished lines (reversed), and whether the
# rest of the line is a comment.
type Tok is Data:
  Tok{word: String, line: List<&2, String>, lines: List<&2, List<&2, String>>, comment: Bool}

# The line with the word (reversed) ended: unchanged when the word is empty.
def end_word(word: String, line: List<&2, String>) -> List<&2, String>:
  match word:
    case SNil{}:
      line
    case SCon{c, t}:
      String.reverse(SCon{c, t}) <> line

# The lines with the line (reversed) ended: unchanged when it has no word.
def end_line(line: List<&2, String>, lines: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match line:
    case Nil{}:
      lines
    case Con{w, t}:
      B.rev(String, Con{w, t}, Nil{}) <> lines

# A separator: the word ends; a comment starts if `start`.
def tok.cut(st: Tok, start: Bool) -> Tok:
  match st:
    case Tok{w, l, ls, c}:
      Tok{SNil{}, end_word(w, l), ls, c || start}

# LF: the word and the line end; the comment (if any) ends.
def tok.newline(st: Tok) -> Tok:
  match st:
    case Tok{w, l, ls, c}:
      Tok{SNil{}, Nil{}, end_line(end_word(w, l), ls), False{}}

def tok.push.pick(comment: Bool, ch: Char, w: String, l: List<&2, String>,
    ls: List<&2, List<&2, String>>) -> Tok:
  match comment:
    case True{}:
      Tok{w, l, ls, True{}}
    case False{}:
      Tok{SCon{ch, w}, l, ls, False{}}

# A word char: kept, unless inside a comment.
def tok.push(st: Tok, ch: Char) -> Tok:
  match st:
    case Tok{w, l, ls, c}:
      tok.push.pick(c, ch, w, l, ls)

# ';' starts a comment when `semi` (resolv.conf), else it is a word char.
def tok.semi(semi: Bool, st: Tok, ch: Char) -> Tok:
  match semi:
    case True{}:
      tok.cut(st, True{})
    case False{}:
      tok.push(st, ch)

def tok.step(k: CClass, semi: Bool, st: Tok, ch: Char) -> Tok:
  match k:
    case KLine{}:
      tok.newline(st)
    case KSpace{}:
      tok.cut(st, False{})
    case KHash{}:
      tok.cut(st, True{})
    case KSemi{}:
      tok.semi(semi, st, ch)
    case _:
      tok.push(st, ch)

# The tokenizer over the chars of s (a left fold, so a loop).
def tok.go(s: String, +semi: Bool, st: Tok) -> Tok:
  match s:
    case SNil{}:
      st
    case SCon{+c, t}:
      tok.go(t, semi, tok.step(cclass(c), semi, st, c))

def tok.finish(st: Tok) -> List<&2, List<&2, String>>:
  match st:
    case Tok{w, l, ls, c}:
      B.rev(List<&2, String>, end_line(end_word(w, l), ls), Nil{})

def tok.init() -> Tok:
  Tok{SNil{}, Nil{}, Nil{}, False{}}

# The text's lines as lists of words, in order: words split at SP, HTAB and
# CR, lines at LF; '#' (and ';' when `semi`) to the end of the line is a
# comment; lines with no word are dropped.
def lines(text: String, semi: Bool) -> List<&2, List<&2, String>>:
  tok.finish(tok.go(text, semi, tok.init()))

# IPv4 nameservers
# ----------------
#
# A canonical dotted quad: four decimal octets 0..255, no leading zeros
# (the text Base's TCP.connect takes). Text longer than 15 chars, and an
# octet longer than 3 digits, is refused before any number is read, so a
# hostile word never reaches N.read with a large value.

# s has more than n chars (looks at most n + 1 of them).
def longer(s: String, n: Nat) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      match n:
        case 0n:
          True{}
        case 1n+p:
          longer(t, p)

def dot_pieces.pick(dot: Bool, c: Char, ps: List<&2, String>) -> List<&2, String>:
  match dot:
    case True{}:
      SNil{} <> ps
    case False{}:
      match ps:
        case Nil{}:
          [SCon{c, SNil{}}]
        case Con{p, r}:
          SCon{c, p} <> r

# The pieces of s between dots: [""] for "", ["a", "b"] for "a.b". A plain
# recursion: only called on text of at most 15 chars.
def dot_pieces(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      [SNil{}]
    case SCon{+c, t}:
      dot_pieces.pick(CClass.is_dot(cclass(c)), c, dot_pieces(t))

def nat_zero(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

# The digit '0'.
def is_zero(k: CClass) -> Bool:
  match k:
    case KDigit{v}:
      nat_zero(v)
    case _:
      False{}

# One char, or a first char other than '0'.
def no_lead_zero(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, t}:
      match t:
        case SNil{}:
          True{}
        case SCon{d, u}:
          Bool.not(is_zero(cclass(c)))

def octet_value(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case Some{n}:
      Nat.is_le(n, 255n)
    case None{}:
      False{}

def octet.pick(short: Bool, +s: String) -> Bool:
  match short:
    case True{}:
      no_lead_zero(s) && octet_value(N.read(s))
    case False{}:
      False{}

# A decimal number 0..255 written without leading zeros.
def octet_ok(+s: String) -> Bool:
  octet.pick(Bool.not(longer(s, 3n)), s)

def octets4(ps: List<&2, String>) -> Bool:
  match ps:
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      octet_ok(a) && octet_ok(b) && octet_ok(c) && octet_ok(d)
    case _:
      False{}

def is_ipv4.pick(short: Bool, s: String) -> Bool:
  match short:
    case True{}:
      octets4(dot_pieces(s))
    case False{}:
      False{}

# Four decimal octets 0..255 separated by dots, no leading zeros.
def is_ipv4(+s: String) -> Bool:
  is_ipv4.pick(Bool.not(longer(s, 15n)), s)

# Numbers
# -------
#
# An option's value, read like atoi: its leading decimal digits. The digit
# state keeps the significant digits (leading zeros dropped) reversed, and
# whether any digit was seen; it stops at the first non-digit. A value with
# more than 2 significant digits is above every maximum here (15, 30, 5), so
# it is the maximum and is never read; at most 2 digits go to N.read.

type Dg is Data:
  Dg{digits: String, any: Bool, stop: Bool}

def dg.digit(ds: String, zero: Bool, +c: Char) -> String:
  match ds:
    case SNil{}:
      match zero:
        case True{}:
          SNil{}
        case False{}:
          SCon{c, SNil{}}
    case SCon{d, t}:
      SCon{c, SCon{d, t}}

def dg.class(k: CClass, ds: String, any: Bool, +c: Char) -> Dg:
  match k:
    case KDigit{v}:
      Dg{dg.digit(ds, nat_zero(v), c), True{}, False{}}
    case _:
      Dg{ds, any, True{}}

def dg.step(st: Dg, +c: Char) -> Dg:
  match st:
    case Dg{ds, any, stop}:
      match stop:
        case True{}:
          Dg{ds, any, True{}}
        case False{}:
          dg.class(cclass(c), ds, any, c)

def dg.go(s: String, st: Dg) -> Dg:
  match s:
    case SNil{}:
      st
    case SCon{+c, t}:
      dg.go(t, dg.step(st, c))

def clamp.read(m: Maybe<&2, Nat>, +max: Nat) -> Nat:
  match m:
    case Some{n}:
      Nat.min(n, max)
    case None{}:
      0n

def clamp.pick(long: Bool, ds: String, +max: Nat) -> Nat:
  match long:
    case True{}:
      max
    case False{}:
      clamp.read(N.read(String.reverse(ds)), max)

def num.fin(st: Dg, +max: Nat) -> Maybe<&2, Nat>:
  match st:
    case Dg{+ds, any, stop}:
      match any:
        case True{}:
          Some{clamp.pick(longer(ds, 2n), ds, max)}
        case False{}:
          None{}

# The value of s's leading digits, at most max; None if s has no leading digit.
def num(s: String, +max: Nat) -> Maybe<&2, Nat>:
  num.fin(dg.go(s, Dg{SNil{}, False{}, False{}}), max)

# 0 becomes 1.
def at_least1(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      1n+p

def at_least1.opt(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case Some{n}:
      Some{at_least1(n)}
    case None{}:
      None{}

# resolv.conf
# -----------

def default_conf() -> M.Conf:
  M.Conf{Nil{}, Nil{}, 1n, 5n, 2n}

type Kw is Data:
  KwNameserver{}
  KwSearch{}
  KwDomain{}
  KwOptions{}
  KwOther{}

def keyword(+w: String) -> Kw:
  Bool.pick(Kw, String.eq(w, "nameserver"), KwNameserver{},
  Bool.pick(Kw, String.eq(w, "search"), KwSearch{},
  Bool.pick(Kw, String.eq(w, "domain"), KwDomain{},
  Bool.pick(Kw, String.eq(w, "options"), KwOptions{},
  KwOther{}))))

# Fewer than 3 entries.
def under3(xs: List<&2, String>) -> Bool:
  match xs:
    case Con{a, Con{b, Con{c, t}}}:
      False{}
    case _:
      True{}

def add_server.pick(ok: Bool, a: String, ns: List<&2, String>) -> List<&2, String>:
  match ok:
    case True{}:
      a <> ns
    case False{}:
      ns

# `nameserver a ...`: a is kept (nameservers are reversed while reading)
# if it is IPv4 text and fewer than 3 are kept.
def add_server(args: List<&2, String>, conf: M.Conf) -> M.Conf:
  match args:
    case Nil{}:
      conf
    case Con{+a, rest}:
      match conf:
        case M.Conf{+ns, s, nd, t, at}:
          M.Conf{add_server.pick(is_ipv4(a) && under3(ns), a, ns), s, nd, t, at}

# `search d ...`: the list replaces the search list (unless empty).
def set_search(args: List<&2, String>, conf: M.Conf) -> M.Conf:
  match args:
    case Nil{}:
      conf
    case Con{d, rest}:
      match conf:
        case M.Conf{ns, s, nd, t, at}:
          M.Conf{ns, Con{d, rest}, nd, t, at}

# `domain d`: [d] replaces the search list (unless there is no d).
def set_domain(args: List<&2, String>, conf: M.Conf) -> M.Conf:
  match args:
    case Nil{}:
      conf
    case Con{d, rest}:
      match conf:
        case M.Conf{ns, s, nd, t, at}:
          M.Conf{ns, [d], nd, t, at}

type OptKw is Data:
  ONdots{}
  OTimeout{}
  OAttempts{}
  OOther{}

def opt_kw(+o: String) -> OptKw:
  Bool.pick(OptKw, String.starts_with(o, "ndots:"), ONdots{},
  Bool.pick(OptKw, String.starts_with(o, "timeout:"), OTimeout{},
  Bool.pick(OptKw, String.starts_with(o, "attempts:"), OAttempts{},
  OOther{})))

def set_ndots(m: Maybe<&2, Nat>, conf: M.Conf) -> M.Conf:
  match m:
    case Some{v}:
      match conf:
        case M.Conf{ns, s, nd, t, at}:
          M.Conf{ns, s, v, t, at}
    case None{}:
      conf

def set_timeout(m: Maybe<&2, Nat>, conf: M.Conf) -> M.Conf:
  match m:
    case Some{v}:
      match conf:
        case M.Conf{ns, s, nd, t, at}:
          M.Conf{ns, s, nd, v, at}
    case None{}:
      conf

def set_attempts(m: Maybe<&2, Nat>, conf: M.Conf) -> M.Conf:
  match m:
    case Some{v}:
      match conf:
        case M.Conf{ns, s, nd, t, at}:
          M.Conf{ns, s, nd, t, v}
    case None{}:
      conf

def option.kw(k: OptKw, o: String, conf: M.Conf) -> M.Conf:
  match k:
    case ONdots{}:
      set_ndots(num(String.drop(o, 6n), 15n), conf)
    case OTimeout{}:
      set_timeout(at_least1.opt(num(String.drop(o, 8n), 30n)), conf)
    case OAttempts{}:
      set_attempts(at_least1.opt(num(String.drop(o, 9n), 5n)), conf)
    case OOther{}:
      conf

# One word of an `options` line.
def option(+o: String, conf: M.Conf) -> M.Conf:
  option.kw(opt_kw(o), o, conf)

# The words of an `options` line, in order (a left fold).
def options.go(os: List<&2, String>, conf: M.Conf) -> M.Conf:
  match os:
    case Nil{}:
      conf
    case Con{o, t}:
      options.go(t, option(o, conf))

def resolv.kw(k: Kw, args: List<&2, String>, conf: M.Conf) -> M.Conf:
  match k:
    case KwNameserver{}:
      add_server(args, conf)
    case KwSearch{}:
      set_search(args, conf)
    case KwDomain{}:
      set_domain(args, conf)
    case KwOptions{}:
      options.go(args, conf)
    case KwOther{}:
      conf

# One line of words.
def resolv.line(words: List<&2, String>, conf: M.Conf) -> M.Conf:
  match words:
    case Nil{}:
      conf
    case Con{+w, args}:
      resolv.kw(keyword(w), args, conf)

# The lines, in order (a left fold).
def resolv.go(ls: List<&2, List<&2, String>>, conf: M.Conf) -> M.Conf:
  match ls:
    case Nil{}:
      conf
    case Con{l, t}:
      resolv.go(t, resolv.line(l, conf))

# The nameservers back in file order.
def resolv.fin(conf: M.Conf) -> M.Conf:
  match conf:
    case M.Conf{ns, s, nd, t, at}:
      M.Conf{B.rev(String, ns, Nil{}), s, nd, t, at}

# resolv.conf's text as a Conf (see the header for what is read).
def resolv(text: String) -> M.Conf:
  resolv.fin(resolv.go(lines(text, True{}), default_conf()))

# /etc/hosts
# ----------

# a and b are the same text (a loop: String.eq nests one call per char of
# the common prefix, which overflows the JS lane's stack on two long equal
# names). Law-facing: same.go(a, b, ok) == Bool.and(ok, String.eq(a, b)),
# by induction on a with ok generalized.
def same.go(a: String, b: String, ok: Bool) -> Bool:
  match a b:
    case SNil{} SNil{}:
      ok
    case SCon{x, xs} SCon{y, ys}:
      same.go(xs, ys, ok && Char.is_eq(x, y))
    case _ _:
      False{}

def same(a: String, b: String) -> Bool:
  same.go(a, b, True{})

# A line of at least two words is an entry; others are skipped.
def hosts.entry(l: List<&2, String>, acc: List<&2, M.HostEntry>) -> List<&2, M.HostEntry>:
  match l:
    case Con{a, Con{n, ns}}:
      M.HostEntry{a, Con{n, ns}} <> acc
    case _:
      acc

def hosts.spec(ls: List<&2, List<&2, String>>) -> List<&2, M.HostEntry>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      hosts.entry(l, hosts.spec(t))

def hosts.go(ls: List<&2, List<&2, String>>, acc: List<&2, M.HostEntry>) -> List<&2, M.HostEntry>:
  match ls:
    case Nil{}:
      B.rev(M.HostEntry, acc, Nil{})
    case Con{l, t}:
      hosts.go(t, hosts.entry(l, acc))

# /etc/hosts's text as its entries, in file order.
def hosts(text: String) -> List<&2, M.HostEntry>:
  hosts.go(lines(text, False{}), Nil{})

def any_name.spec(+l: String, ns: List<&2, String>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{n, t}:
      same(l, lower(n)) || any_name.spec(l, t)

def any_name.go(+l: String, ns: List<&2, String>, found: Bool) -> Bool:
  match ns:
    case Nil{}:
      found
    case Con{n, t}:
      any_name.go(l, t, found || same(l, lower(n)))

def lookup.pick(hit: Bool, a: String, acc: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      a <> acc
    case False{}:
      acc

def lookup.spec(+l: String, es: List<&2, M.HostEntry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      match e:
        case M.HostEntry{a, ns}:
          lookup.pick(any_name.go(l, ns, False{}), a, lookup.spec(l, t))

def lookup.go(+l: String, es: List<&2, M.HostEntry>, acc: List<&2, String>) -> List<&2, String>:
  match es:
    case Nil{}:
      B.rev(String, acc, Nil{})
    case Con{e, t}:
      match e:
        case M.HostEntry{a, ns}:
          lookup.go(l, t, lookup.pick(any_name.go(l, ns, False{}), a, acc))

# The addresses of every entry with a name equal to `name` ignoring ASCII
# case, in file order (duplicates kept).
def hosts_lookup(entries: List<&2, M.HostEntry>, name: String) -> List<&2, String>:
  lookup.go(lower(name), entries, Nil{})

# Search-list candidates
# ----------------------
#
# resolv.conf(5) / glibc's res_nsearch, with dots counted naively (every
# '.' char, as glibc does):
#  - "" or a name ending in '.' (absolute): [name] alone;
#  - at least ndots dots: name first, then name.suffix for each suffix;
#  - fewer: name.suffix for each suffix, then name.
# A suffix's own trailing dot is dropped ("example.com." gives
# "host.example.com"; "." gives "host.").

def dots.add(dot: Bool, n: Nat) -> Nat:
  match dot:
    case True{}:
      1n+n
    case False{}:
      n

# The number of '.' chars in s, plus n.
def dots.go(s: String, n: Nat) -> Nat:
  match s:
    case SNil{}:
      n
    case SCon{+c, t}:
      dots.go(t, dots.add(CClass.is_dot(cclass(c)), n))

# Whether the last char of s is '.' (`last` for "").
def ends_dot.go(s: String, last: Bool) -> Bool:
  match s:
    case SNil{}:
      last
    case SCon{+c, t}:
      ends_dot.go(t, CClass.is_dot(cclass(c)))

def ends_dot(s: String) -> Bool:
  ends_dot.go(s, False{})

def is_empty(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      False{}

def drop_dot.pick(dot: Bool, c: Char, t: String) -> String:
  match dot:
    case True{}:
      t
    case False{}:
      SCon{c, t}

# r without a first '.' (r is a reversed suffix).
def drop_dot(r: String) -> String:
  match r:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      drop_dot.pick(CClass.is_dot(cclass(c)), c, t)

# name ++ "." ++ suffix (without suffix's trailing dot), as loops.
def with_suffix(name: String, suffix: String) -> String:
  String.reverse.go(String.reverse(name), SCon{'.', String.reverse(drop_dot(String.reverse(suffix)))})

def expand.spec(+name: String, ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      with_suffix(name, s) <> expand.spec(name, t)

# name.suffix for each suffix, consed onto acc (so in reverse).
def expand.go(+name: String, ss: List<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      acc
    case Con{s, t}:
      expand.go(name, t, with_suffix(name, s) <> acc)

def cand.order(first: Bool, ss: List<&2, String>, +name: String) -> List<&2, String>:
  match first:
    case True{}:
      B.rev(String, expand.go(name, ss, [name]), Nil{})
    case False{}:
      B.rev(String, name <> expand.go(name, ss, Nil{}), Nil{})

def cand.pick(alone: Bool, first: Bool, ss: List<&2, String>, +name: String) -> List<&2, String>:
  match alone:
    case True{}:
      [name]
    case False{}:
      cand.order(first, ss, name)

# The names to try for `name`, in order (see above).
def candidates(conf: M.Conf, +name: String) -> List<&2, String>:
  match conf:
    case M.Conf{ns, ss, nd, t, at}:
      cand.pick(is_empty(name) || ends_dot(name), Nat.is_le(nd, dots.go(name, 0n)), ss, name)
