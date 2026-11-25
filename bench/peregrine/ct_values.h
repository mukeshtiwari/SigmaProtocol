/* Fixed-size byte values in the CertiRocq heap, for the constant-time build
   (programs *_ct of build.sh; zl_ct_glue.c and ed25519_ct_glue.c).

   A scalar of Zl.F is a block of 4 words (32 bytes, the canonical
   representative below l, little-endian) with tag CT_SCALAR_TAG; a point of
   Ed.G is a block of 8 words (the canonical affine coordinates x and y below
   p = 2^255 - 19, 32 little-endian bytes each) with tag CT_POINT_TAG.  Both
   tags are above No_scan_tag, so the collector copies the blocks without
   reading their contents; the integers of z_gmp.c have the tag No_scan_tag,
   so neither kind can be mistaken for an integer.  The size of a block, its
   header and the address at which it is allocated do not depend on its
   contents. */
#ifndef CT_VALUES_H
#define CT_VALUES_H
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <gmp.h>
#include "gc_stack.h"

#define CT_SCALAR_TAG 253
#define CT_POINT_TAG 254
#define CT_SCALAR_WORDS 4
#define CT_POINT_WORDS 8

static void ct_fail(const char *who, const char *what) {
  fprintf(stderr, "%s: %s\n", who, what);
  abort();
}

/* The bytes of a value of the given kind; aborts on another representation.
   Only the header is read, which is public. */
static inline uint8_t *ct_bytes(value v, unsigned tag, uintnat words, const char *who) {
  if (!Is_block(v) || Tag_val(v) != tag || Wosize_val(v) != words)
    ct_fail(who, "unexpected representation");
  return (uint8_t *) v;
}

/* A new block of the given kind holding a copy of src, in the heap.  The
   caller must not hold other heap values: a collection here has no roots. */
static inline value ct_alloc(struct thread_info *tinfo, unsigned tag, uintnat words,
                             const uint8_t *src) {
  if ((uintnat) (tinfo->limit - tinfo->alloc) < words + 1) {
    tinfo->nalloc = words + 1;
    garbage_collect(tinfo);
  }
  value *p = tinfo->alloc;
  tinfo->alloc = p + words + 1;
  p[0] = (value) (((header_t) words << 10) | tag);
  memcpy(p + 1, src, words * sizeof(value));
  return (value) (p + 1);
}

/* The sumbool (or bool) of an equality: left (true) is ordinal 0, right
   (false) ordinal 1.  diff is the OR of the XORs of the compared bytes; the
   result is computed without a branch. */
static inline value ct_sumbool_of_diff(uint8_t diff) {
  uintnat d = diff;
  uintnat nonzero = (d | (0 - d)) >> (8 * sizeof(uintnat) - 1);
  return Val_long(nonzero);
}

static inline uint8_t ct_diff(const uint8_t *a, const uint8_t *b, size_t n) {
  uint8_t d = 0;
  for (size_t i = 0; i < n; i++) d |= a[i] ^ b[i];
  return d;
}

/* The integer of 32 little-endian bytes in the representation of z_gmp.c
   (unboxed below 2^62, otherwise a block of tag No_scan_tag holding the
   signed size and the limbs).  Not constant time: for public values only.
   The caller must not hold other heap values. */
static inline uintnat ct_int_words(const uint8_t b[32], mp_limb_t limbs[4], mp_size_t *size) {
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

/* Writes the integer at the alloc pointer; the space (ct_int_words) must
   have been reserved. */
static inline value ct_make_int(struct thread_info *tinfo, const mp_limb_t limbs[4], mp_size_t s) {
  if (s == 0) return Val_long(0);
  if (s == 1 && limbs[0] <= (mp_limb_t) Max_long) return Val_long((intnat) limbs[0]);
  value *p = tinfo->alloc;
  tinfo->alloc = p + s + 2;
  p[0] = (value) (((header_t) (s + 1) << 10) | No_scan_tag);
  p[1] = (value) s;
  memcpy(p + 2, limbs, (size_t) s * sizeof(mp_limb_t));
  return (value) (p + 1);
}

static inline void ct_reserve(struct thread_info *tinfo, uintnat words) {
  if ((uintnat) (tinfo->limit - tinfo->alloc) < words) {
    tinfo->nalloc = words;
    garbage_collect(tinfo);
  }
}
#endif
