/* Ed.fast_smul by the verified bedrock2 scalar multiplication.

   remap_const.py remaps the Rocq constant
       Curve.Ed25519.Ed25519.Ed.fast_smul : Z -> point -> point
   (an affine point: a pair of coordinates in Zmod p with a proof that it is
   on the curve) to ed25519_fast_smul below, which

     1. writes the scalar n (an integer in the representation of z_gmp.c)
        and the coordinates x, y of the point (integers in [0, p)) as 32
        little-endian bytes each;
     2. calls ed25519_smul_bytes, which writes the coordinates of n.P as 32
        little-endian bytes each;
     3. builds the resulting point in the CertiRocq heap from these bytes.

   Step 2 is the bedrock2 code of ed25519_bedrock.c.  The theorem
   ed25519_smul_bytes_e2e (bedrock/EmitC.v) states, for the printed list of
   functions, that on the canonical encodings of the coordinates of a group
   element x and the 32 bytes of a scalar s it writes the canonical
   encodings of the coordinates of Ed.gpow_fast x s; the constant 2d is
   computed inside (ed25519_twice_d), and no branch or memory address
   depends on the bits of the scalar (ScalarMultCT.v).  Trusted here: the
   conversions between integers and bytes and the heap layout of steps 1
   and 3, the renaming of the function double, and the precondition
   0 <= n < 2^256, which every call of fast_smul from Ed.gpow_fast meets
   (n = unsigned k < l); any other n aborts.  Outside this file: bedrock2's
   printer ToCString, which produced ed25519_bedrock.c.

   Layout of the values, after erasure (checked at run time; a mismatch
   aborts): Peregrine drops the erased proof fields of constructors, so a
   point is a block of tag 0 [c] (sig), c a block of tag 0 [x, y] (prod),
   and each coordinate a block of tag 0 [z] (the record Zmod) with z an
   integer. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <gmp.h>
#include "gc_stack.h"
#include "ed25519_glue.h"

/* The C keyword [double] is the name of a bedrock2 function. */
#define double ed25519_bedrock_double
#include "ed25519_bedrock.c"
#undef double

#define ZSIZE(v) ((mp_size_t) Field(v, 0))
#define ZLIMBS(v) ((mp_limb_t *) &Field(v, 1))

static void fail(const char *what) {
  fprintf(stderr, "ed25519_fast_smul: %s\n", what);
  abort();
}

static void dump(value v, int depth) {
  if (Is_long(v)) { fprintf(stderr, "%ld", (long) Long_val(v)); return; }
  unsigned tag = Tag_val(v);
  uintnat n = Wosize_val(v);
  if (tag == No_scan_tag) { fprintf(stderr, "<int %lu limbs>", (unsigned long) n - 1); return; }
  fprintf(stderr, "[tag %u:", tag);
  for (uintnat i = 0; i < n; i++) {
    fputc(' ', stderr);
    if (depth > 0) dump(Field(v, i), depth - 1); else fputs("..", stderr);
  }
  fputc(']', stderr);
}

/* A block of tag 0 and the given size, or abort. */
static value block(value v, uintnat size) {
  if (!Is_block(v) || Tag_val(v) != 0 || Wosize_val(v) != size) {
    dump(v, 4); fputc('\n', stderr);
    fail("unexpected representation");
  }
  return v;
}

/* An integer 0 <= z < 2^256 as 32 little-endian bytes. */
static void int_to_bytes(value z, uint8_t out[32]) {
  memset(out, 0, 32);
  if (Is_long(z)) {
    intnat l = Long_val(z);
    if (l < 0) fail("negative integer");
    for (int i = 0; i < 8; i++) out[i] = (uint8_t) ((uintnat) l >> (8 * i));
    return;
  }
  if (Tag_val(z) != No_scan_tag) fail("integer expected");
  mp_size_t s = ZSIZE(z);
  if (s < 0) fail("negative integer");
  if ((size_t) s * sizeof(mp_limb_t) > 32) fail("integer of more than 256 bits");
  for (mp_size_t i = 0; i < s; i++) {
    mp_limb_t limb = ZLIMBS(z)[i];
    for (size_t j = 0; j < sizeof(mp_limb_t); j++)
      out[i * sizeof(mp_limb_t) + j] = (uint8_t) (limb >> (8 * j));
  }
}

/* Words needed in the heap for the integer of 32 little-endian bytes
   (0 if it is unboxed), and the integer written at p. */
static uintnat int_words(const uint8_t b[32], mp_limb_t limbs[4], mp_size_t *size) {
  mp_size_t s = 0;
  for (int i = 0; i < 4; i++) {
    mp_limb_t l = 0;
    for (int j = 0; j < 8; j++) l |= (mp_limb_t) b[8 * i + j] << (8 * j);
    limbs[i] = l;
    if (l) s = i + 1;
  }
  *size = s;
  if (s == 0 || (s == 1 && limbs[0] <= (mp_limb_t) Max_long)) return 0;
  return (uintnat) s + 2;
}

static value *alloc_words(struct thread_info *tinfo, uintnat words) {
  value *p = tinfo->alloc;
  tinfo->alloc = p + words;
  return p;
}

static value make_int(struct thread_info *tinfo, const mp_limb_t limbs[4], mp_size_t s) {
  if (s == 0) return Val_long(0);
  if (s == 1 && limbs[0] <= (mp_limb_t) Max_long) return Val_long((intnat) limbs[0]);
  value *p = alloc_words(tinfo, (uintnat) s + 2);
  p[0] = (value) (((header_t) (s + 1) << 10) | No_scan_tag);
  p[1] = (value) s;
  memcpy(p + 2, limbs, (size_t) s * sizeof(mp_limb_t));
  return (value) (p + 1);
}

static value make_block1(struct thread_info *tinfo, value a) {
  value *p = alloc_words(tinfo, 2);
  p[0] = (value) ((header_t) 1 << 10);  /* size 1, tag 0 */
  p[1] = a;
  return (value) (p + 1);
}

static value make_block2(struct thread_info *tinfo, value a, value b) {
  value *p = alloc_words(tinfo, 3);
  p[0] = (value) ((header_t) 2 << 10);  /* size 2, tag 0 */
  p[1] = a;
  p[2] = b;
  return (value) (p + 1);
}

value ed25519_fast_smul(struct thread_info *tinfo, value n, value P) {
  static int debug = -1;
  if (debug < 0) debug = getenv("ED25519_GLUE_DEBUG") != NULL;
  if (debug) { fputs("n = ", stderr); dump(n, 0); fputs("\nP = ", stderr); dump(P, 4); fputc('\n', stderr); }

  /* step 1: read the inputs; nothing below allocates before step 3 */
  uint8_t kb[32], xb[32], yb[32];
  if (!Is_long(n) && Tag_val(n) != No_scan_tag) fail("integer expected");
  int_to_bytes(n, kb);
  value c = Field(block(P, 1), 0);
  value vx = Field(block(c, 2), 0), vy = Field(c, 1);
  int_to_bytes(Field(block(vx, 1), 0), xb);
  int_to_bytes(Field(block(vy, 1), 0), yb);

  /* step 2: the verified code */
  uint8_t ob[2][32];
  ed25519_smul_bytes((br_word_t) ob[0], (br_word_t) ob[1], (br_word_t) xb, (br_word_t) yb,
                     (br_word_t) kb);

  /* step 3: the result [[[x], [y]]] in the heap.  The inputs are dead, so a
     collection here needs no roots. */
  mp_limb_t limbs[2][4];
  mp_size_t sizes[2];
  uintnat words = 2 + 2 + 3 + 2;  /* two Zmod records, the pair and the sig */
  for (int i = 0; i < 2; i++) words += int_words(ob[i], limbs[i], &sizes[i]);
  if ((uintnat) (tinfo->limit - tinfo->alloc) < words) {
    tinfo->nalloc = words;
    garbage_collect(tinfo);
  }
  value x = make_block1(tinfo, make_int(tinfo, limbs[0], sizes[0]));
  value y = make_block1(tinfo, make_int(tinfo, limbs[1], sizes[1]));
  value res = make_block1(tinfo, make_block2(tinfo, x, y));
  if (debug) { fputs("result = ", stderr); dump(res, 4); fputc('\n', stderr); }
  return res;
}
