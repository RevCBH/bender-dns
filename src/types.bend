import Base

# The data DNS is made of. Every number is a Nat; names are label lists.

# A domain name: its labels, most specific first, each a byte list as it
# appears on the wire (case kept). The root is [].
def Name() -> Data:
  List<&2, List<&2, U32>>

type RType is Data:
  TA{}
  TNS{}
  TCNAME{}
  TSOA{}
  TPTR{}
  TMX{}
  TTXT{}
  TAAAA{}
  TSRV{}
  TOPT{}
  TANY{}
  TOther{code: Nat}         # any other type code (never one of the above)

type RClass is Data:
  CIN{}
  COther{code: Nat}         # any other class code (never 1); OPT's payload size

type Question is Data:
  Question{name: List<&2, List<&2, U32>>, qtype: RType, qclass: RClass}

type RData is Data:
  RIpv4{a: Nat, b: Nat, c: Nat, d: Nat}
  RIpv6{groups: List<&2, Nat>}                                   # 8 groups of 16 bits
  RName{name: List<&2, List<&2, U32>>}                           # NS, CNAME, PTR
  RMx{preference: Nat, exchange: List<&2, List<&2, U32>>}
  RTxt{strings: List<&2, List<&2, U32>>}                         # character-strings
  RSoa{mname: List<&2, List<&2, U32>>, rname: List<&2, List<&2, U32>>, serial: Nat,
    refresh: Nat, retry: Nat, expire: Nat, minimum: Nat}
  RSrv{priority: Nat, weight: Nat, port: Nat, target: List<&2, List<&2, U32>>}
  RRaw{bytes: List<&2, U32>}                                     # other types, and OPT

type Record is Data:
  Record{name: List<&2, List<&2, U32>>, rtype: RType, rclass: RClass, ttl: Nat, data: RData}

type Header is Data:
  Header{id: Nat, qr: Bool, opcode: Nat, aa: Bool, tc: Bool, rd: Bool, ra: Bool,
    ad: Bool, cd: Bool, rcode: Nat}

type Message is Data:
  Message{header: Header, questions: List<&2, Question>, answers: List<&2, Record>,
    authority: List<&2, Record>, additional: List<&2, Record>}

# A value read from the front of a byte list, and the bytes after it.
type Got is Data:
  Got{value: Nat, rest: List<&2, U32>}

# Why a name's text was refused.
type NameError is Data:
  EmptyLabel{}
  LabelTooLong{}            # over 63 bytes
  NameTooLong{}             # over 255 bytes on the wire
  BadEscape{}
  BadChar{}                 # a char that is not visible ASCII, unescaped

# Why a message could not be read.
type DecodeError is Data:
  Short{}                   # the message ended inside a field
  BadPointer{}              # a compression pointer forward, out of range, or looping
  BadLabel{}                # a label length with the reserved bits 01 or 10
  BadRdata{}                # RDATA not matching its type or RDLENGTH
  Trailing{}                # bytes after the last record

# resolv.conf, as the native resolver uses it.
type Conf is Data:
  Conf{nameservers: List<&2, String>, search: List<&2, String>, ndots: Nat,
    timeout_s: Nat, attempts: Nat}

# One /etc/hosts line: an address and its names.
type HostEntry is Data:
  HostEntry{address: String, names: List<&2, String>}

# What a response says about a question.
type Answer is Data:
  Found{name: List<&2, List<&2, U32>>, records: List<&2, Record>}   # records at the chain's end
  Alias{target: List<&2, List<&2, U32>>}                            # the chain leaves the answer
  Nothing{}

type Resolved is Data:
  Resolved{name: List<&2, List<&2, U32>>, records: List<&2, Record>}

# Why a lookup failed. Codes and messages are errno values and texts, as
# Base's effects report them.
type Error is Data:
  BadName{error: NameError}
  NxDomain{name: String}               # the name does not exist (every candidate)
  NoData{name: String}                 # it exists, with no record of the type
  ServFail{rcode: Nat}                 # every server failed or refused
  Malformed{error: DecodeError}        # a response could not be read
  Mismatch{}                           # a response did not answer the query
  NoServers{}
  Connect{code: U32, message: String}
  Io{code: U32, message: String}
  Timeout{}
  Os{code: U32, message: String}       # the OS resolver failed
  Config{message: String}
