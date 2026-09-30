/* Differential-testing support for the 3D Low* and Pulse backends.

   Two modes:

     fuzz <corpus-out>   mutate inputs, keeping any that produce an outcome
                         signature not seen before, and dump the accumulated
                         corpus. The signature is (verdict, error count, error
                         field names), which for a parser is a good stand-in
                         for coverage: as soon as a mutation gets one field
                         further into the grammar, the reported field name
                         changes and the input is retained. That is what drives
                         the corpus towards magic numbers and valid tags.

     replay <corpus-in>  run a fixed corpus and print one trace line per case.

   Everything is deterministic and, critically, address-stable: the region that
   probes read from is mapped at a fixed address, so a pointer value planted in
   an input has the same byte representation in both binaries. Without that the
   two backends would be fed different inputs and the comparison would be
   meaningless. */

#include "harness.h"
#include "seeds.inc"
#include <sys/mman.h>
#include <inttypes.h>

#define HX_SRC_ADDR ((uintptr_t)0x200000)
#define HX_SRC_SIZE ((size_t)0x100000)

static uint8_t *hx_src;

/* ------------------------------------------------------------------ */
/* Output formatting                                                    */
/* ------------------------------------------------------------------ */

#define RING 16
#define SLOTSZ 4096
static char ring[RING][SLOTSZ];
static int ring_i;

static char *slot(void) {
  char *p = ring[ring_i];
  ring_i = (ring_i + 1) % RING;
  return p;
}

const char *hx_u64(uint64_t v) {
  char *p = slot();
  snprintf(p, SLOTSZ, "%" PRIu64, v);
  return p;
}

/* Print a returned pointer as an offset into the input buffer, never as an
   absolute address: the two binaries put their stacks in different places. */
const char *hx_off(const uint8_t *p, const uint8_t *base, uint32_t len) {
  char *s = slot();
  if (p == NULL)
    snprintf(s, SLOTSZ, "null");
  else if (p >= base && p <= base + len)
    snprintf(s, SLOTSZ, "base+%ld", (long)(p - base));
  else
    snprintf(s, SLOTSZ, "other");
  return s;
}

/* ------------------------------------------------------------------ */
/* Error-callback trace                                                 */
/* ------------------------------------------------------------------ */

static char err_acc[1024];
static int err_n;

void hx_reset(void) {
  err_acc[0] = '\0';
  err_n = 0;
}

void hx_error(const char *t, const char *f, const char *r) {
  err_n++;
  if (err_n <= 4) {
    size_t used = strlen(err_acc);
    if (used < sizeof(err_acc) - 160)
      snprintf(err_acc + used, sizeof(err_acc) - used, "%s<%s.%s:%s>",
               used ? "," : "", t ? t : "?", f ? f : "?", r ? r : "?");
  }
}

const char *hx_errors(void) {
  char *p = slot();
  snprintf(p, SLOTSZ, "err=%d[%s]", err_n, err_acc);
  return p;
}

/* ------------------------------------------------------------------ */
/* Copy buffers                                                         */
/* ------------------------------------------------------------------ */

#define CB_SLOTS 8
/* Big enough for the largest probed type in the corpus: specialize_test's
   `B64` is 80 bytes, so the 64 this used to be made
   `ProbeAndCopy(length=sizeof(B))` fail unconditionally and no probe in that
   test could ever succeed. Keep it comfortably above the largest one. */
#define CB_LEN 256
/* driver.c dumps every live copy buffer into a fixed-size description. */
typedef char hx_descsz_covers_copy_buffers
    [(CB_SLOTS * (2 * CB_LEN + 16) < HX_DESCSZ) ? 1 : -1];
static uint8_t cb_store[CB_SLOTS][CB_LEN];

void hx_cb_init(hx_cb_t *cb, int s) {
  cb->slot = s;
  cb->buf = cb_store[s % CB_SLOTS];
  cb->len = CB_LEN;
  cb->pos = 0;
  memset(cb->buf, 0, CB_LEN);
}

const char *hx_cb_show(const hx_cb_t *cb) {
  char *p = slot();
  int o = snprintf(p, SLOTSZ, "cb%d[", cb->slot);
  for (size_t i = 0; i < cb->len && o < SLOTSZ - 8; i++)
    o += snprintf(p + o, SLOTSZ - o, "%02x", cb->buf[i]);
  snprintf(p + o, SLOTSZ - o, "]");
  return p;
}

const char *hx_bytes(const void *p, size_t n) {
  const uint8_t *b = p;
  char *s = slot();
  int o = snprintf(s, SLOTSZ, "[");
  for (size_t i = 0; i < n && o < SLOTSZ - 8; i++)
    o += snprintf(s + o, SLOTSZ - o, "%02x", b[i]);
  snprintf(s + o, SLOTSZ - o, "]");
  return s;
}

uint8_t *EverParseStreamOf(EVERPARSE_COPY_BUFFER_T x) {
  return ((hx_cb_t *)x)->buf;
}

/* The Low* prelude declares this returning uint64_t and the Pulse one size_t;
   both are 64-bit here, so a single definition serves both builds. */
size_t EverParseStreamLen(EVERPARSE_COPY_BUFFER_T x) {
  return ((hx_cb_t *)x)->len;
}

/* Pulse only. Harmless in the Low* build. */
size_t *EverParseStreamPos(EVERPARSE_COPY_BUFFER_T x) {
  return &((hx_cb_t *)x)->pos;
}

/* ------------------------------------------------------------------ */
/* Probe externs                                                        */
/* ------------------------------------------------------------------ */

static int src_ok(uint64_t addr, uint64_t off, uint64_t n) {
  if (addr < HX_SRC_ADDR)
    return 0;
  uint64_t rel = addr - HX_SRC_ADDR;
  if (rel >= HX_SRC_SIZE)
    return 0;
  if (off > HX_SRC_SIZE - rel)
    return 0;
  return n <= HX_SRC_SIZE - rel - off;
}

static BOOLEAN probe_copy(uint64_t n, uint64_t ro, uint64_t wo, uint64_t src,
                          EVERPARSE_COPY_BUFFER_T dst) {
  hx_cb_t *d = dst;
  if (!src_ok(src, ro, n))
    return 0;
  if (wo > d->len || n > d->len - wo)
    return 0;
  memcpy(d->buf + wo, (const uint8_t *)(uintptr_t)(src + ro), (size_t)n);
  return 1;
}

static uint32_t probe_read32(BOOLEAN *failed, uint64_t ro, uint64_t src,
                             EVERPARSE_COPY_BUFFER_T dst) {
  (void)dst;
  uint32_t v = 0;
  if (!src_ok(src, ro, 4)) {
    *failed = 1;                    /* set only on failure, as 3D expects */
    return 0;
  }
  memcpy(&v, (const uint8_t *)(uintptr_t)(src + ro), 4);
  return v;
}

static uint64_t probe_read64(BOOLEAN *failed, uint64_t ro, uint64_t src,
                             EVERPARSE_COPY_BUFFER_T dst) {
  (void)dst;
  uint64_t v = 0;
  if (!src_ok(src, ro, 8)) {
    *failed = 1;
    return 0;
  }
  memcpy(&v, (const uint8_t *)(uintptr_t)(src + ro), 8);
  return v;
}

static BOOLEAN write32(uint32_t v, uint64_t wo, EVERPARSE_COPY_BUFFER_T dst) {
  hx_cb_t *d = dst;
  if (wo > d->len || 4 > d->len - wo)
    return 0;
  memcpy(d->buf + wo, &v, 4);
  return 1;
}

static BOOLEAN write64(uint64_t v, uint64_t wo, EVERPARSE_COPY_BUFFER_T dst) {
  hx_cb_t *d = dst;
  if (wo > d->len || 8 > d->len - wo)
    return 0;
  memcpy(d->buf + wo, &v, 8);
  return 1;
}

static BOOLEAN probe_init(EVERPARSE_STRING name, uint64_t n,
                          EVERPARSE_COPY_BUFFER_T dst) {
  (void)name;
  hx_cb_t *d = dst;
  if (n > d->len)
    return 0;
  d->pos = 0;
  return 1;
}

/* 3D emits one numbered copy of each extern per probe site; all of them get
   the same implementation. */
#define PROBE_SET(SUF)                                                        \
  BOOLEAN ProbeAndCopy##SUF(uint64_t n, uint64_t ro, uint64_t wo,             \
                            uint64_t src, EVERPARSE_COPY_BUFFER_T dst) {      \
    return probe_copy(n, ro, wo, src, dst);                                   \
  }                                                                           \
  uint32_t ProbeAndReadU32##SUF(BOOLEAN *f, uint64_t ro, uint64_t src,        \
                                EVERPARSE_COPY_BUFFER_T dst) {                \
    return probe_read32(f, ro, src, dst);                                     \
  }                                                                           \
  uint64_t ProbeAndReadU64##SUF(BOOLEAN *f, uint64_t ro, uint64_t src,        \
                                EVERPARSE_COPY_BUFFER_T dst) {                \
    return probe_read64(f, ro, src, dst);                                     \
  }                                                                           \
  BOOLEAN ProbeInit##SUF(EVERPARSE_STRING s, uint64_t n,                      \
                         EVERPARSE_COPY_BUFFER_T dst) {                       \
    return probe_init(s, n, dst);                                             \
  }                                                                           \
  /* "In place" means the validator is handed the source region rather than   \
     a copy of it. Modelling it as a copy is behaviourally equivalent from    \
     the validator's point of view, and keeps both backends on exactly the    \
     same implementation, which is what the comparison needs. */              \
  BOOLEAN ProbeInPlace##SUF(uint64_t n, uint64_t ro, uint64_t wo,             \
                            uint64_t src, EVERPARSE_COPY_BUFFER_T dst) {      \
    return probe_copy(n, ro, wo, src, dst);                                   \
  }                                                                           \
  uint64_t UlongToPtr##SUF(uint32_t p) { return (uint64_t)p; }

PROBE_SET()
PROBE_SET(0)
PROBE_SET(1)
PROBE_SET(2)
PROBE_SET(3)
PROBE_SET(4)

BOOLEAN WriteU64(uint64_t v, uint64_t w, EVERPARSE_COPY_BUFFER_T d) { return write64(v, w, d); }
BOOLEAN WriteU640(uint64_t v, uint64_t w, EVERPARSE_COPY_BUFFER_T d) { return write64(v, w, d); }
BOOLEAN WriteU641(uint64_t v, uint64_t w, EVERPARSE_COPY_BUFFER_T d) { return write64(v, w, d); }
BOOLEAN WriteU642(uint64_t v, uint64_t w, EVERPARSE_COPY_BUFFER_T d) { return write64(v, w, d); }
BOOLEAN WriteU643(uint64_t v, uint64_t w, EVERPARSE_COPY_BUFFER_T d) { return write64(v, w, d); }
BOOLEAN WriteU644(uint64_t v, uint64_t w, EVERPARSE_COPY_BUFFER_T d) { return write64(v, w, d); }
BOOLEAN WriteU320(uint32_t v, uint64_t w, EVERPARSE_COPY_BUFFER_T d) { return write32(v, w, d); }

void hx_init(void) {
  void *p = mmap((void *)HX_SRC_ADDR, HX_SRC_SIZE, PROT_READ | PROT_WRITE,
                 MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
  if (p != (void *)HX_SRC_ADDR) {
    fprintf(stderr, "harness: could not map the probe source region\n");
    exit(2);
  }
  hx_src = p;
  uint32_t s = 0x12345678u;
  for (size_t i = 0; i < HX_SRC_SIZE; i++) {
    s ^= s << 13; s ^= s >> 17; s ^= s << 5;
    hx_src[i] = (uint8_t)s;
  }
  /* A pointer chain, so that probes which follow pointers land somewhere
     valid. Replicated at the start of every page rather than only at the
     start of the region: a chain written solely into the first 128 bytes is
     exhausted after one hop, so any grammar that dereferences more than two
     levels deep always lands in the xorshift noise below and can never
     validate. With a copy in every page, following a pointer lands on another
     pointer however deep the chain goes. */
  for (size_t page = 0; page < HX_SRC_SIZE; page += 0x1000) {
    for (int i = 0; i < 16; i++) {
      /* Stay inside the region: wrap rather than run off the end. */
      uint64_t a = HX_SRC_ADDR +
                   ((page + 0x1000 * (uint64_t)(i + 1)) % HX_SRC_SIZE);
      memcpy(hx_src + page + 8 * i, &a, 8);
    }
  }
}

/* ------------------------------------------------------------------ */
/* Fuzzing                                                              */
/* ------------------------------------------------------------------ */

static uint64_t rs = 0x243F6A8885A308D3ull;
static uint64_t rnd(void) {
  rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
  return rs;
}

static const uint64_t INTERESTING[] = {
  0, 1, 2, 3, 4, 7, 8, 15, 16, 20, 31, 32, 63, 64, 127, 128, 255, 256,
  1000, 1024, 4096, 65535, 65536, 0x7FFFFFFFu, 0x80000000u, 0xFFFFFFFFu,
  0xFFFFFFFFFFFFFFFFull,
  HX_SRC_ADDR, HX_SRC_ADDR + 0x1000, HX_SRC_ADDR + 0x2000,
};
#define NINTERESTING (int)(sizeof(INTERESTING) / sizeof(INTERESTING[0]))

/* Writes a dictionary constant into the buffer, in the width and byte order
   the field it is meant for might use. 3D grammars mix endiannesses freely
   (ELF's `e_ident` is bytes, its `e_type` is little-endian, and TCP/IP is
   big-endian), and the width a constant is compared at is not recoverable
   from the literal, so try all of them. */
static void plant(hx_case_t *c, uint64_t v) {
  static const uint32_t widths[] = {1, 2, 4, 8};
  uint32_t n = widths[rnd() % 4];
  if (c->len < n) return;
  uint32_t o = (uint32_t)(rnd() % (c->len - n + 1));
  for (uint32_t i = 0; i < n; i++) {
    /* Little-endian for even draws, big-endian for odd. */
    uint32_t sh = (rnd() & 1) ? (n - 1 - i) : i;
    c->buf[o + i] = (uint8_t)(v >> (8 * sh));
  }
}

static void mutate(hx_case_t *c, const hx_entry_t *e) {
  int nops = 1 + (int)(rnd() % 4);
  for (int i = 0; i < nops; i++) {
    /* Draw from the dictionary about a third of the time when there is one. */
    if (e->ndict && rnd() % 3 == 0) {
      uint64_t v = e->dict[rnd() % (uint32_t)e->ndict];
      if (rnd() % 4 == 0)
        c->args[rnd() % HX_NARGS] = v;
      else
        plant(c, v);
      continue;
    }
    switch (rnd() % 11) {
    case 0:                         /* flip a bit */
      if (c->len) {
        uint32_t o = (uint32_t)(rnd() % c->len);
        c->buf[o] ^= (uint8_t)(1u << (rnd() % 8));
      }
      break;
    case 1:                         /* set a random byte */
      if (c->len) c->buf[rnd() % c->len] = (uint8_t)rnd();
      break;
    case 2:                         /* plant an interesting byte */
      if (c->len) c->buf[rnd() % c->len] =
          (uint8_t)INTERESTING[rnd() % NINTERESTING];
      break;
    case 3: {                       /* plant an interesting 4-byte value */
      if (c->len >= 4) {
        uint32_t o = (uint32_t)(rnd() % (c->len - 3));
        uint32_t v = (uint32_t)INTERESTING[rnd() % NINTERESTING];
        memcpy(c->buf + o, &v, 4);
      }
      break;
    }
    case 4: {                       /* plant an interesting 8-byte value */
      if (c->len >= 8) {
        uint32_t o = (uint32_t)(rnd() % (c->len - 7));
        uint64_t v = INTERESTING[rnd() % NINTERESTING];
        memcpy(c->buf + o, &v, 8);
      }
      break;
    }
    case 5:                         /* change the length */
      c->len = (uint32_t)(rnd() % (HX_MAXLEN + 1));
      break;
    case 6:                         /* mutate a scalar argument */
      c->args[rnd() % HX_NARGS] = INTERESTING[rnd() % NINTERESTING];
      break;
    case 7:                         /* random scalar argument */
      c->args[rnd() % HX_NARGS] = rnd();
      break;
    case 8: {                       /* zero the tail of the buffer */
      /* A [:zeroterm] array has to meet its terminator, and the last one in a
         type has to meet it exactly at the end of the input for the whole
         input to be consumed. Landing that by chance needs two specific zero
         bytes at one specific offset, which is why TAtMost's `T` reached
         `str3` constantly and never once got past it. */
      uint32_t n = 1 + (uint32_t)(rnd() % 8);
      if (n > c->len) n = c->len;
      memset(c->buf + c->len - n, 0, n);
      break;
    }
    case 9: {                       /* copy a chunk within the buffer */
      if (c->len >= 8) {
        uint32_t n = 1 + (uint32_t)(rnd() % 8);
        uint32_t a = (uint32_t)(rnd() % (c->len - n + 1));
        uint32_t b = (uint32_t)(rnd() % (c->len - n + 1));
        memmove(c->buf + b, c->buf + a, n);
      }
      break;
    }
    default: {                      /* a short run of equal bytes */
      if (c->len) {
        uint32_t o = (uint32_t)(rnd() % c->len);
        uint32_t n = 1 + (uint32_t)(rnd() % 8);
        /* Half the time from INTERESTING rather than uniformly at random:
           what terminates a [:zeroterm] array is a run of zeroes, and a
           uniform byte is zero only once in 256, so TAtMost's three
           zero-terminated strings were never all terminated at once. */
        uint8_t v = (rnd() & 1) ? (uint8_t)INTERESTING[rnd() % NINTERESTING]
                                : (uint8_t)rnd();
        if (o + n > c->len) n = c->len - o;
        memset(c->buf + o, v, n);
      }
      break;
    }
    }
  }
}

/* The outcome signature used as the fuzzing progress signal. */
static void signature(char *out, size_t n, BOOLEAN r, const char *desc) {
  snprintf(out, n, "%d|%s|%s", !!r, hx_errors(), desc);
}

#define MAXCORPUS 3000
#define MAXSIGS 3000

/* How much longer to keep trying for an entrypoint no input has been accepted
   for yet. */
#define STARVED 20

/* Corpus slots none of the (far more numerous) rejecting cases may take.
   Without this, a grammar with thousands of distinct ways to fail fills the
   corpus long before the fuzzer stumbles on an input that validates, and that
   one valuable case is then dropped -- so the entrypoint contributes no
   evidence at all about the accepting path, which is the one that exercises
   the most backend code. */
#define ACCEPT_RESERVE 256

static int run_fuzz(const char *path, long iters) {
  FILE *f = fopen(path, "wb");
  if (!f) { perror(path); return 1; }

  for (int e = 0; e < hx_nentries; e++) {
    static hx_case_t corpus[MAXCORPUS];
    static char sigs[MAXSIGS][HX_DESCSZ * 2];
    int ncorpus = 0, nsigs = 0;
    char desc[HX_DESCSZ], sig[HX_DESCSZ * 2];

    /* Seed the corpus: a spread of lengths across several content families.
       All zeroes matters most and used to be missing: a field is very often
       valid when zero, an empty [:zeroterm] array is two zero bytes, and a
       zero length or tag selects the smallest case of a union, so the
       all-zero input is the shortest accepted input of a good many grammars.
       TAtMost's `T`, for one, is accepted by eighteen zero bytes and by
       almost nothing else, and it was never accepted here at all while the
       only family seeded was the byte ramp. */
    for (int fam = 0; fam < 4; fam++) {
      for (uint32_t len = 0; len <= HX_MAXLEN && ncorpus < MAXCORPUS;
           len += 8) {
        hx_case_t *c = &corpus[ncorpus++];
        memset(c, 0, sizeof(*c));
        c->len = len;
        for (uint32_t i = 0; i < len; i++)
          c->buf[i] = (uint8_t)(fam == 0 ? 0
                              : fam == 1 ? 0xFF
                              : fam == 2 ? (i & 0xFF)
                                         : rnd());
        for (int a = 0; a < HX_NARGS; a++) c->args[a] = (uint64_t)(a + 1);
      }
    }

    /* Seed with the dictionary laid down end to end, in each width, so that a
       grammar whose opening field is a magic number has a starting point that
       already matches rather than having to be mutated into one byte at a
       time. */
    /* Then anything a solver found for this entrypoint. */
    for (size_t i = 0; i < sizeof(hx_seeds) / sizeof(hx_seeds[0]); i++) {
      if (strcmp(hx_seeds[i].entry, hx_entries[e].name)) continue;
      if (ncorpus >= MAXCORPUS) break;
      hx_case_t *c = &corpus[ncorpus++];
      memset(c, 0, sizeof(*c));
      c->len = hx_seeds[i].len;
      memcpy(c->buf, hx_seeds[i].buf, hx_seeds[i].len);
    }

    for (uint32_t width = 1; width <= 8 && hx_entries[e].ndict; width *= 2)
    for (int be = 0; be < 2; be++)
    /* The dictionary is in order of first appearance in the .3d, so a run of
       it reproduces a multi-byte magic number verbatim -- but only once the
       run is aligned with the start of that magic number, which the literals
       of preceding fields shift. Seed a few rotations so one of them is. */
    for (uint32_t rot = 0; rot < 4 && ncorpus < MAXCORPUS; rot++) {
      const uint64_t *dict = hx_entries[e].dict;
      uint32_t nd = (uint32_t)hx_entries[e].ndict;
      hx_case_t *c = &corpus[ncorpus++];
      memset(c, 0, sizeof(*c));
      c->len = HX_MAXLEN;
      for (int a = 0; a < HX_NARGS; a++) c->args[a] = dict[(rot + a) % nd];
      for (uint32_t o = 0, k = rot; o + width <= HX_MAXLEN; o += width, k++) {
        uint64_t v = dict[k % nd];
        for (uint32_t i = 0; i < width; i++)
          c->buf[o + i] = (uint8_t)(v >> (8 * (be ? width - 1 - i : i)));
      }
    }

    /* An entrypoint that has never once been accepted has produced no
       evidence about what the two backends do on a *valid* input, which is
       the case that matters most. Those are exactly the entrypoints with the
       most demanding grammars, so give them a larger budget rather than
       letting them time out alongside the easy ones. Costs nothing for an
       entrypoint that is accepting inputs already. */
    long naccept = 0;
    for (long it = 0; it < iters || (!naccept && it < iters * STARVED); it++) {
      hx_case_t c = corpus[rnd() % (uint64_t)ncorpus];
      mutate(&c, &hx_entries[e]);
      if (c.len > HX_MAXLEN) c.len = HX_MAXLEN;

      uint8_t tmp[HX_MAXLEN];
      memcpy(tmp, c.buf, HX_MAXLEN);
      hx_reset();
      desc[0] = 0;
      BOOLEAN r = hx_entries[e].call(c.args, tmp, c.len, desc);
      if (r) naccept++;
      signature(sig, sizeof(sig), r, desc);

      int fresh = 1;
      for (int s = 0; s < nsigs; s++)
        if (!strcmp(sigs[s], sig)) { fresh = 0; break; }
      int room = r ? MAXCORPUS : MAXCORPUS - ACCEPT_RESERVE;
      if (fresh && nsigs < MAXSIGS && ncorpus < room) {
        strncpy(sigs[nsigs], sig, sizeof(sigs[0]) - 1);
        sigs[nsigs][sizeof(sigs[0]) - 1] = 0;
        nsigs++;
        corpus[ncorpus++] = c;
      }
    }

    for (int i = 0; i < ncorpus; i++) {
      uint32_t idx = (uint32_t)e;
      fwrite(&idx, sizeof(idx), 1, f);
      fwrite(&corpus[i], sizeof(hx_case_t), 1, f);
    }
    fprintf(stderr, "%-34s corpus=%d sigs=%d accepted=%ld%s\n",
            hx_entries[e].name, ncorpus, nsigs, naccept,
            naccept ? "" : "   *** never accepted an input ***");
  }
  fclose(f);
  return 0;
}

static int run_replay(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) { perror(path); return 1; }
  uint32_t idx;
  hx_case_t c;
  long n = 0;
  while (fread(&idx, sizeof(idx), 1, f) == 1 &&
         fread(&c, sizeof(c), 1, f) == 1) {
    if (idx >= (uint32_t)hx_nentries) { fprintf(stderr, "bad index\n"); return 1; }
    uint8_t tmp[HX_MAXLEN];
    memcpy(tmp, c.buf, HX_MAXLEN);
    char desc[HX_DESCSZ];
    desc[0] = 0;
    hx_reset();
    BOOLEAN r = hx_entries[idx].call(c.args, tmp, c.len, desc);
    printf("%s|%ld|len=%u|r=%d%s|%s\n", hx_entries[idx].name, n, c.len,
           !!r, desc, hx_errors());
    n++;
  }
  fclose(f);
  return 0;
}

int main(int argc, char **argv) {
  hx_init();
  if (argc >= 3 && !strcmp(argv[1], "fuzz"))
    return run_fuzz(argv[2], argc >= 4 ? atol(argv[3]) : 200000);
  if (argc >= 3 && !strcmp(argv[1], "replay"))
    return run_replay(argv[2]);
  fprintf(stderr, "usage: %s fuzz <out> [iters] | replay <in>\n", argv[0]);
  return 2;
}
