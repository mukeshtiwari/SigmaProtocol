/* Z, positive and N as GMP integers, for extracted code.

   The three inductives of BinNums are remapped to one representation: an
   integer.  Z0, N0 are 0; Zpos p and Npos p are p; Zneg p is -p; xH is 1,
   xO p is 2p and xI p is 2p + 1.  A value in [Min_long, Max_long] is an unboxed
   integer, and only such a value is unboxed, so the representation is
   canonical.

   A larger value is an immutable block of the CertiRocq heap, collected by its
   garbage collector:

       header: No_scan_tag, size n + 1
       word 0: the signed size s of an mpz (|s| = n limbs, sign of the value)
       words 1..n: the limbs, least significant first, the top one nonzero

   No_scan_tag tells the collector that the words are not pointers, so it
   copies the block as it is.  Operations read a block in place through a
   read-only mpz (mpz_roinit_n), compute into a static scratch mpz, and only
   then allocate the result in the heap and copy the limbs; so the arguments
   are dead when an allocation may call the collector, and only the case
   analyses, which still use their closure arguments afterwards, keep roots
   (a stack frame of their own, as the generated code does).

   GC protocol.  A function that allocates takes the thread_info (attribute
   "takes tinfo" = true in splice_gmp_z.py): the generated code then stores its
   alloc and limit pointers in the thread_info before the call, keeps its live
   values in its frame of the shadow stack (tinfo->fp), and reloads alloc, limit
   and its roots after it.  Allocation is tinfo->alloc += n + 2, after a
   garbage_collect with tinfo->nalloc = n + 2 when limit - alloc < n + 2.
   Functions that never allocate keep the plain C signature.

   A result of more than BIG_WORDS words (about 2 million bits) would not fit
   in the nursery; it is malloc'ed outside the heap in the same layout and
   never freed (the collector leaves pointers outside the heap alone).  The
   KZG computations stay far below.

   bool: true is the first constructor (unboxed 0), false the second (1).
   comparison: Eq, Lt, Gt are unboxed 0, 1, 2. */

#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include "z_gmp.h"

#define BOOL(b) Val_long((b) ? 0 : 1)
#define ZSIZE(v) ((mp_size_t) Field(v, 0))      /* signed size of a boxed integer */
#define ZLIMBS(v) ((mp_limb_t *) &Field(v, 1))  /* its limbs */
#define BIG_WORDS (NURSERY_SIZE / 2)

#ifdef ZG_COUNT
#include <stdio.h>
static unsigned long zc_boxes, zc_words, zc_big, zc_gcs;
__attribute__((destructor)) static void zc_report(void) {
  fprintf(stderr, "z_gmp: %lu boxed integers in the heap (%lu words), %lu outside, "
          "%lu collections called by z_gmp\n", zc_boxes, zc_words, zc_big, zc_gcs);
}
#define COUNT(x) (x)
#else
#define COUNT(x) ((void) 0)
#endif

static mpz_t R;   /* scratch result; its limbs are malloc'ed by GMP and reused */
static int R_ready;
static inline mpz_ptr res(void) {
  if (!R_ready) { mpz_init2(R, 1024); R_ready = 1; }
  return R;
}

/* A read-only mpz of a value: a view of the limbs of a block, or of one limb
   of t for an unboxed integer (|x| < 2^62).  Valid until the next allocation. */
typedef struct { __mpz_struct z; mp_limb_t l; } zview;
static mpz_srcptr view(value v, zview *t) {
  if (Is_long(v)) {
    intnat x = Long_val(v);
    t->l = x < 0 ? (mp_limb_t) -x : (mp_limb_t) x;
    return mpz_roinit_n(&t->z, &t->l, x < 0 ? -1 : x > 0);
  }
  mp_size_t s = ZSIZE(v);
  t->z._mp_alloc = (int) (s < 0 ? -s : s);
  t->z._mp_size = (int) s;
  t->z._mp_d = ZLIMBS(v);
  return &t->z;
}

/* m as a value: unboxed if it fits, otherwise a new block in the heap.  May
   call the collector: no value read before the call may be used afterwards
   unless it is rooted.  m must not point into the heap. */
static value box(struct thread_info *tinfo, mpz_srcptr m) {
  if (mpz_fits_slong_p(m)) {
    long l = mpz_get_si(m);
    if (l >= Min_long && l <= Max_long) return Val_long(l);
  }
  mp_size_t s = m->_mp_size, n = s < 0 ? -s : s;
  uintnat words = (uintnat) n + 2;
  value *p;
  if (words > BIG_WORDS) {
    p = malloc(words * sizeof(value));
    if (p == NULL) abort();
    COUNT(zc_big++);
  } else {
    if ((uintnat) (tinfo->limit - tinfo->alloc) < words) {
      tinfo->nalloc = words;
      garbage_collect(tinfo);
      COUNT(zc_gcs++);
    }
    p = tinfo->alloc;
    tinfo->alloc = p + words;
    COUNT((zc_boxes++, zc_words += words));
  }
  p[0] = (value) (((header_t) (n + 1) << 10) | No_scan_tag);
  p[1] = (value) s;
  memcpy(p + 2, m->_mp_d, (size_t) n * sizeof(mp_limb_t));
  return (value) (p + 1);
}

static int sgn(value v) {
  if (Is_long(v)) return (Long_val(v) > 0) - (Long_val(v) < 0);
  return (ZSIZE(v) > 0) - (ZSIZE(v) < 0);
}

static int cmp(value x, value y) {
  if (Is_long(x) && Is_long(y)) return (Long_val(x) > Long_val(y)) - (Long_val(x) < Long_val(y));
  zview a, b;
  int c = mpz_cmp(view(x, &a), view(y, &b));
  return (c > 0) - (c < 0);
}

typedef void (*binop)(mpz_ptr, mpz_srcptr, mpz_srcptr);

static value apply(struct thread_info *tinfo, binop f, value x, value y) {
  zview a, b;
  mpz_ptr r = res();
  f(r, view(x, &a), view(y, &b));
  return box(tinfo, r);
}

static value small(long l) { /* |l| small enough for Val_long */
  return Val_long(l);
}

value zg_add(struct thread_info *tinfo, value x, value y) {
  if (Is_long(x) && Is_long(y)) {
    intnat s = Long_val(x) + Long_val(y); /* |s| < 2^63: no overflow */
    if (s >= Min_long && s <= Max_long) return Val_long(s);
  }
  return apply(tinfo, mpz_add, x, y);
}

value zg_sub(struct thread_info *tinfo, value x, value y) {
  if (Is_long(x) && Is_long(y)) {
    intnat s = Long_val(x) - Long_val(y);
    if (s >= Min_long && s <= Max_long) return Val_long(s);
  }
  return apply(tinfo, mpz_sub, x, y);
}

value zg_mul(struct thread_info *tinfo, value x, value y) {
  if (Is_long(x) && Is_long(y)) {
    intnat p;
    if (!__builtin_mul_overflow(Long_val(x), Long_val(y), &p) && p >= Min_long && p <= Max_long)
      return Val_long(p);
  }
  return apply(tinfo, mpz_mul, x, y);
}

value zg_opp(struct thread_info *tinfo, value x) {
  if (Is_long(x)) return zg_sub(tinfo, small(0), x);
  zview a;
  mpz_ptr r = res();
  mpz_neg(r, view(x, &a));
  return box(tinfo, r);
}
value zg_abs(struct thread_info *tinfo, value x) { return sgn(x) < 0 ? zg_opp(tinfo, x) : x; }

value zg_fdiv(struct thread_info *tinfo, value x, value y) {
  return sgn(y) == 0 ? small(0) : apply(tinfo, mpz_fdiv_q, x, y);
}
value zg_fmod(struct thread_info *tinfo, value x, value y) {
  return sgn(y) == 0 ? x : apply(tinfo, mpz_fdiv_r, x, y);
}
value zg_tdiv(struct thread_info *tinfo, value x, value y) {
  return sgn(y) == 0 ? small(0) : apply(tinfo, mpz_tdiv_q, x, y);
}
value zg_tmod(struct thread_info *tinfo, value x, value y) {
  return sgn(y) == 0 ? x : apply(tinfo, mpz_tdiv_r, x, y);
}

value zg_pow(struct thread_info *tinfo, value x, value y) {
  if (sgn(y) < 0) return small(0);
  if (!Is_long(y)) abort(); /* exponent beyond 2^62 */
  zview a;
  mpz_ptr r = res();
  mpz_pow_ui(r, view(x, &a), (unsigned long) Long_val(y));
  return box(tinfo, r);
}

static value shift(struct thread_info *tinfo, value x, value y, int left) {
  /* y as a shift amount; shifts beyond 2^62 bits are not supported */
  if (!Is_long(y)) abort();
  long n = Long_val(y);
  if (n < 0) { n = -n; left = !left; }
  zview a;
  mpz_ptr r = res();
  if (left) mpz_mul_2exp(r, view(x, &a), (mp_bitcnt_t) n);
  else mpz_fdiv_q_2exp(r, view(x, &a), (mp_bitcnt_t) n);
  return box(tinfo, r);
}

value zg_shiftl(struct thread_info *tinfo, value x, value y) { return shift(tinfo, x, y, 1); }
value zg_shiftr(struct thread_info *tinfo, value x, value y) { return shift(tinfo, x, y, 0); }
value zg_land(struct thread_info *tinfo, value x, value y) { return apply(tinfo, mpz_and, x, y); }
value zg_lor(struct thread_info *tinfo, value x, value y) { return apply(tinfo, mpz_ior, x, y); }
value zg_lxor(struct thread_info *tinfo, value x, value y) { return apply(tinfo, mpz_xor, x, y); }

value zg_testbit(value x, value y) {
  if (sgn(y) < 0) return BOOL(0);
  if (!Is_long(y)) return BOOL(sgn(x) < 0); /* bits beyond 2^62 */
  zview a;
  return BOOL(mpz_tstbit(view(x, &a), (mp_bitcnt_t) Long_val(y))); /* two's complement */
}

value zg_compare(value x, value y) {
  int c = cmp(x, y);
  return Val_long(c == 0 ? 0 : c < 0 ? 1 : 2);
}
value zg_eqb(value x, value y) {
  if (Is_long(x) || Is_long(y)) return BOOL(x == y); /* canonical representation */
  mp_size_t s = ZSIZE(x);
  if (s != ZSIZE(y)) return BOOL(0);
  return BOOL(mpn_cmp(ZLIMBS(x), ZLIMBS(y), s < 0 ? -s : s) == 0);
}
value zg_leb(value x, value y) { return BOOL(cmp(x, y) <= 0); }
value zg_ltb(value x, value y) { return BOOL(cmp(x, y) < 0); }

value zg_pos_sub_trunc(struct thread_info *tinfo, value x, value y) {
  return cmp(x, y) <= 0 ? small(1) : zg_sub(tinfo, x, y);
}
value zg_n_sub_trunc(struct thread_info *tinfo, value x, value y) {
  return cmp(x, y) <= 0 ? small(0) : zg_sub(tinfo, x, y);
}
value zg_pos_pred(struct thread_info *tinfo, value x) {
  return x == small(1) ? x : zg_sub(tinfo, x, small(1));
}
value zg_n_pred(struct thread_info *tinfo, value x) {
  return x == small(0) ? x : zg_sub(tinfo, x, small(1));
}
value zg_to_pos(value x) { return sgn(x) <= 0 ? small(1) : x; }
value zg_to_n(value x) { return sgn(x) < 0 ? small(0) : x; }

value zg_pos_size(value x) {
  zview a;
  return small((long) mpz_sizeinbase(view(x, &a), 2));
}

/* constructors */
value zg_Z0(void) { return small(0); }
value zg_Zpos(value p) { return p; }
value zg_Zneg(struct thread_info *tinfo, value p) { return zg_opp(tinfo, p); }
value zg_xH(void) { return small(1); }
value zg_xO(struct thread_info *tinfo, value p) { return zg_add(tinfo, p, p); }
value zg_xI(struct thread_info *tinfo, value p) {
  if (Is_long(p)) return zg_add(tinfo, zg_add(tinfo, p, p), small(1)); /* first sum unboxed or fresh */
  zview a;
  mpz_ptr r = res();
  mpz_mul_2exp(r, view(p, &a), 1);
  mpz_setbit(r, 0);
  return box(tinfo, r);
}
value zg_N0(void) { return small(0); }
value zg_Npos(value p) { return p; }

/* Allocate the integer r while the closures f[0..n-1] stay live: they are
   roots of a frame of the shadow stack during the allocation, and are
   updated if the collector moved them. */
static value box_keep(struct thread_info *tinfo, mpz_srcptr r, value *f, int n) {
  struct stack_frame frame;
  value root[2];
  for (int i = 0; i < n; i++) root[i] = f[i];
  frame.root = root;
  frame.next = root + n;
  frame.prev = tinfo->fp;
  tinfo->fp = &frame;
  value v = box(tinfo, r);
  tinfo->fp = frame.prev;
  for (int i = 0; i < n; i++) f[i] = root[i];
  return v;
}

/* case analyses; a nullary branch is called with the discriminee, as in
   CertiRocq's z_nat_case */
value zg_z_case(struct thread_info *tinfo, value z, value f0, value fpos, value fneg) {
  int s = sgn(z);
  if (s == 0) return closure_call(tinfo, f0, z);
  if (s > 0) return closure_call(tinfo, fpos, z);
  if (Is_long(z) && Long_val(z) > Min_long) return closure_call(tinfo, fneg, small(-Long_val(z)));
  zview a;
  mpz_ptr r = res();
  mpz_neg(r, view(z, &a));
  value p = box_keep(tinfo, r, &fneg, 1);
  return closure_call(tinfo, fneg, p);
}

value zg_pos_case(struct thread_info *tinfo, value p, value fI, value fO, value fH) {
  if (p == small(1)) return closure_call(tinfo, fH, p);
  if (Is_long(p)) {
    intnat l = Long_val(p);
    return closure_call(tinfo, (l & 1) ? fI : fO, small(l >> 1));
  }
  zview a;
  mpz_srcptr pz = view(p, &a);
  int odd = mpz_odd_p(pz);
  mpz_ptr r = res();
  mpz_fdiv_q_2exp(r, pz, 1); /* floor (p / 2) */
  value f = odd ? fI : fO;
  value h = box_keep(tinfo, r, &f, 1);
  return closure_call(tinfo, f, h);
}

value zg_n_case(struct thread_info *tinfo, value n, value f0, value fpos) {
  if (n == small(0)) return closure_call(tinfo, f0, n);
  return closure_call(tinfo, fpos, n);
}

char *zg_to_string(value x) {
  zview a;
  return mpz_get_str(NULL, 10, view(x, &a));
}
