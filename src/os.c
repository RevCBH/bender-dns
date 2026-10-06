// OS resolver
// ===========

#include <netdb.h>
#include <arpa/inet.h>

// getaddrinfo blocks, so it runs on an IO helper thread (io_work): the call
// fills an OsLookup with up to OS_LOOKUP_MAX distinct addresses as text, and
// the pack, back on the loop, turns them into a List<String> in resolver
// order. Starts from bender-http's dns.c (IPv4 only); this one takes a
// family: 0 = AF_UNSPEC, 4 = AF_INET, 6 = AF_INET6.
#define OS_LOOKUP_MAX 32
#define OS_LOOKUP_TEXT 46 /* INET6_ADDRSTRLEN */
#define OS_LOOKUP_NUMERIC_WHY \
  "a numeric host that is not a dotted-quad IPv4 address (the resolver would read it as octal, hex or a short form)"

typedef struct {
  char* host;
  int   family;
  u32   size;
  int   rc;
  int   sys;
  char  addr[OS_LOOKUP_MAX][OS_LOOKUP_TEXT];
} OsLookup;

// The resolver's EAI_* codes differ by platform; the Result carries an errno
// value instead, and the text says what the resolver said.
static u32 os_lookup_code(OsLookup* d) {
  switch (d->rc) {
    case 0:          return ENOENT;
    case EAI_SYSTEM: return d->sys != 0 ? (u32)d->sys : EIO;
    case EAI_AGAIN:  return EAGAIN;
    case EAI_MEMORY: return ENOMEM;
    case EAI_FAIL:   return EIO;
    case EAI_NONAME: return ENOENT;
#if defined(EAI_NODATA) && EAI_NODATA != EAI_NONAME
    case EAI_NODATA: return ENOENT;
#endif
#if defined(EAI_ADDRFAMILY) && EAI_ADDRFAMILY != EAI_NONAME
    case EAI_ADDRFAMILY: return ENOENT;
#endif
    default:         return EINVAL;
  }
}

static const char* os_lookup_none(int family) {
  return family == AF_INET ? "no IPv4 address for this name"
    : family == AF_INET6 ? "no IPv6 address for this name"
    : "no address for this name";
}

static void os_lookup_call(IoWork* w) {
  OsLookup*        d = (OsLookup*)w->data;
  struct addrinfo  hints;
  struct addrinfo* res = NULL;
  memset(&hints, 0, sizeof hints);
  hints.ai_family   = d->family;
  hints.ai_socktype = SOCK_STREAM;
  d->rc  = getaddrinfo(d->host, NULL, &hints, &res);
  d->sys = d->rc == EAI_SYSTEM ? errno : 0;
  for (struct addrinfo* ai = res; ai != NULL && d->size < OS_LOOKUP_MAX; ai = ai->ai_next) {
    char*       at  = d->addr[d->size];
    const void* src = NULL;
    if (ai->ai_addr == NULL) {
      continue;
    }
    if (ai->ai_family == AF_INET) {
      src = &((struct sockaddr_in*)ai->ai_addr)->sin_addr;
    } else if (ai->ai_family == AF_INET6) {
      src = &((struct sockaddr_in6*)ai->ai_addr)->sin6_addr;
    }
    if (src == NULL || inet_ntop(ai->ai_family, src, at, OS_LOOKUP_TEXT) == NULL) {
      continue;
    }
    u32 seen = 0;
    while (seen < d->size && strcmp(d->addr[seen], at) != 0) {
      seen += 1;
    }
    d->size += seen == d->size;
  }
  if (res != NULL) {
    freeaddrinfo(res);
  }
}

static Term os_lookup_pack(Env e, IoWork* w) {
  OsLookup* d = (OsLookup*)w->data;
  Term      r;
  if (d->rc != 0 || d->size == 0) {
    const char* text = d->rc == 0 ? os_lookup_none(d->family)
      : d->rc == EAI_SYSTEM ? NULL : gai_strerror(d->rc);
    r = io_fail(e, os_lookup_code(d), text);
  } else {
    Term xs = term_pak(CID(Nil), 0);
    for (u32 i = d->size; i > 0; i -= 1) {
      xs = io_node(e, CID(Con), io_str(e, d->addr[i - 1], strlen(d->addr[i - 1])), xs);
    }
    r = io_done(e, xs);
  }
  free(d->host);
  free(d);
  return r;
}

// True when the resolver would read host as an IPv4 address (getaddrinfo
// with AI_NUMERICHOST: inet_aton's forms, so octal "010.0.0.1", hex
// "0x7f.1", short "127.1" and a bare 32-bit number "2130706433") but host is
// not the canonical dotted quad io_sys_addr takes. Such a host would reach
// an address its text does not spell, so the lookup refuses it, whatever
// the family. A host with a ':' is an IPv6 literal or a name, never one of
// inet_aton's forms (glibc's AF_INET numeric parse accepts a v4-mapped
// "::ffff:1.2.3.4", which is not ambiguous), so it is let through. A
// numeric parse makes no query, so this runs on the loop.
static int os_lookup_noncanonical(const char* host) {
  struct addrinfo    hints;
  struct addrinfo*   res = NULL;
  struct sockaddr_in at;
  if (strchr(host, ':') != NULL) {
    return 0;
  }
  memset(&hints, 0, sizeof hints);
  hints.ai_family   = AF_INET;
  hints.ai_socktype = SOCK_STREAM;
  hints.ai_flags    = AI_NUMERICHOST;
  if (getaddrinfo(host, NULL, &hints, &res) != 0) {
    return 0;
  }
  freeaddrinfo(res);
  return io_sys_addr(host, 0, &at) != 0;
}

Term os_lookup_run(Env e, Term* f, IoWork* w) {
  u32 fam = (u32)f[1];
  int family = fam == 0 ? AF_UNSPEC : fam == 4 ? AF_INET : fam == 6 ? AF_INET6 : -1;
  if (family < 0) {
    return io_fail(e, EINVAL, "the address family must be 0 (any), 4 (IPv4) or 6 (IPv6)");
  }
  u64   len  = 0;
  char* host = io_cstr(e, f[0], &len);
  if (len == 0 || io_nul(host, len)) {
    free(host);
    return io_fail(e, EINVAL, NULL);
  }
  if (os_lookup_noncanonical(host)) {
    free(host);
    return io_fail(e, EINVAL, OS_LOOKUP_NUMERIC_WHY);
  }
  OsLookup* d = (OsLookup*)io_mem(calloc(1, sizeof(OsLookup)));
  d->host   = host;
  d->family = family;
  w->data   = (char*)d;
  return io_work(w, os_lookup_call, os_lookup_pack);
}

static void __attribute__((constructor)) os_lookup_use(void) {
  io_eff(CID(Os.lookup), os_lookup_run, 0);
}
