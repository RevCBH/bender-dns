import Base

# Name resolution through the OS resolver (getaddrinfo), so nsswitch,
# /etc/hosts, search domains, mDNS, VPN split DNS and systemd-resolved apply
# as for any C program.
#
#   Os.lookup(host, family) -> IO(Result<&1, &1, U32 & String, List<&2, String>>)
#
# family is 0 (AF_UNSPEC: IPv4 and IPv6), 4 (AF_INET) or 6 (AF_INET6); any
# other value fails with EINVAL (22). The answer is the distinct addresses
# as text (inet_ntop: "93.184.215.14", "2606:2800:21f:cb07:6820:80da:af6b:8b2c",
# "::1"), in the resolver's order, at most 32. An empty name or one holding
# a NUL fails with EINVAL; a name with no address of the family fails with
# ENOENT (2). Other failures carry an errno value for the resolver's EAI_*
# code (EAI_AGAIN -> EAGAIN, EAI_MEMORY -> ENOMEM, EAI_FAIL -> EIO,
# EAI_NONAME / EAI_NODATA / EAI_ADDRFAMILY -> ENOENT, EAI_SYSTEM -> its
# errno, anything else -> EINVAL) and the resolver's own text (gai_strerror).
#
# A canonical dotted quad (`10.0.0.1`) answers itself (with family 0 or 4;
# family 6 does not map it). Any other host the resolver would read as an
# IPv4 address (inet_aton's forms: octal `010.0.0.1`, which is 8.0.0.1, hex
# `0x7f.1`, short `127.1`, a bare number `2130706433`) fails with EINVAL
# before any lookup, whatever the family, so a host never reaches an address
# its text does not spell (a host with a ':' is an IPv6 literal or a name
# and is let through). A trailing dot makes a name (`127.1.` goes to
# DNS). IPv6 literals (`::1`) answer themselves with family 0 or 6. The
# lookup has no timeout of its own: the resolver's settings bound it.
#
# The C lane runs getaddrinfo on an IO helper thread; the JS lane calls it
# through bun:ffi and blocks the loop until the resolver answers (JS's IO
# loop cannot park on a lookup, bendlang/bend#1148).
#
# Foreign code: nothing a law imports may import this file.
def Os.lookup(host: String, family: U32) -> IO(Result<&1, &1, U32 & String, List<&2, String>>):
  import "./os.c"
  import "./os.js"
