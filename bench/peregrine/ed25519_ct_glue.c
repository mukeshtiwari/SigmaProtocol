/* Ed.G (the order-l subgroup of Ed25519) as 64-byte values, for the
   constant-time build (programs *_ct of build.sh).

   remap_const.py remaps the constants of Curve/Ed25519.v
       Ed.B, Ed.gid : Ed.G
       Ed.gop : Ed.G -> Ed.G -> Ed.G,  Ed.ginv : Ed.G -> Ed.G
       Ed.gpow_fast : Ed.G -> Zl.F -> Ed.G
       Ed.Gdec : forall x y : Ed.G, {x = y} + {x <> y}
   of Examples/Ed25519Ins.v
       point_to_Z : Ed.G -> Z * Z,  h : Ed.G (the public key gpow_fast B x)
   and of the benchmark Ed25519Ballot_LamBox.v
       Ed25519Ballot.publish_G : Ed.G -> Ed.G
   to the functions below.  A point is a block of CT_POINT_TAG holding its
   canonical affine coordinates x and y (32 little-endian bytes each,
   ct_values.h); a scalar is a block of CT_SCALAR_TAG (zl_ct_glue.c).
   check_abstract.py checks that the remapped program refers to no remaining
   operation on the curve or on Zmod.

   gpow is one call of the bedrock2 function ed25519_smul_bytes of
   ed25519_bedrock.c on the 64 bytes of the point and the 32 bytes of the
   scalar; the theorem ed25519_smul_bytes_e2e (bedrock/EmitC.v) states that
   it writes the canonical encodings of the coordinates of
   [Ed.gpow_fast x s].  gop and ginv are compositions of bedrock2 functions
   of the same file (AUCurves' 64-bit field arithmetic and the Ed25519
   bedrock2 bridge), each verified, none of which branches on or indexes
   memory by its data:
     gop:   from_bytes, from_affine (both), ed25519_twice_d, add, to_affine,
            to_bytes;
     ginv:  from_bytes, carry_sub from 0 (x -> -x), to_bytes.
   The coordinates are canonical below p and to_bytes outputs canonical
   bytes, so byte equality is point equality (edc_eq, compared without a
   branch).  point_to_Z (edc_to_Z) converts to GMP integers and is not
   constant time; the program applies it to published points only.

   Trusted: the composition of the bedrock2 functions in gop and ginv (each
   verified; the compositions are not), the byte layout and heap
   allocation, the constants B and the identity below, and bedrock2's
   printer ToCString, which produced ed25519_bedrock.c.  This file replaces
   ed25519_glue.c in the *_ct programs (both define ed25519_smul_bytes by
   including ed25519_bedrock.c). */
#include "ct_values.h"
#include "ed25519_ct_glue.h"
#include "zl_ct_glue.h"
#if defined(__has_include)
#if __has_include(<valgrind/memcheck.h>)
#include <valgrind/memcheck.h>
#endif
#endif
#ifndef VALGRIND_MAKE_MEM_DEFINED
#define VALGRIND_MAKE_MEM_DEFINED(p, n) ((void) 0)
#endif

/* The C keyword [double] is the name of a bedrock2 function. */
#define double ed25519_bedrock_double
#include "ed25519_bedrock.c"
#undef double

#define P(v) ((uint8_t *) ct_bytes(v, CT_POINT_TAG, CT_POINT_WORDS, "ed25519_ct_glue"))
#define K(v) ((uint8_t *) ct_bytes(v, CT_SCALAR_TAG, CT_SCALAR_WORDS, "ed25519_ct_glue"))
#define HDR ((value) (((header_t) CT_POINT_WORDS << 10) | CT_POINT_TAG))

/* The base point B of RFC 8032 and the identity (0, 1), outside the heap. */
static union { value w[1 + CT_POINT_WORDS]; } base_block = {{HDR}}, gid_block = {{HDR}};
static const uint8_t base_bytes[64] = {
  0x1a, 0xd5, 0x25, 0x8f, 0x60, 0x2d, 0x56, 0xc9, 0xb2, 0xa7, 0x25, 0x95, 0x60, 0xc7, 0x2c, 0x69,
  0x5c, 0xdc, 0xd6, 0xfd, 0x31, 0xe2, 0xa4, 0xc0, 0xfe, 0x53, 0x6e, 0xcd, 0xd3, 0x36, 0x69, 0x21,
  0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
  0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66};

value edc_base(void) {
  memcpy(&base_block.w[1], base_bytes, 64);
  return (value) &base_block.w[1];
}

value edc_gid(void) {
  uint8_t *b = (uint8_t *) &gid_block.w[1];
  memset(b, 0, 64);
  b[32] = 1;
  return (value) b;
}

/* Field elements (5 limbs of 64 bits, 40 bytes) of 32 canonical bytes. */
static void point_in(const uint8_t *pb, uint8_t ext[200]) {
  uint8_t fx[40], fy[40];
  fe25519_from_bytes((br_word_t) fx, (br_word_t) pb);
  fe25519_from_bytes((br_word_t) fy, (br_word_t) (pb + 32));
  from_affine((br_word_t) ext, (br_word_t) fx, (br_word_t) fy);
}

static void point_out(const uint8_t ext[200], uint8_t out[64]) {
  uint8_t aff[80];
  to_affine((br_word_t) aff, (br_word_t) ext);
  fe25519_to_bytes((br_word_t) out, (br_word_t) aff);
  fe25519_to_bytes((br_word_t) (out + 32), (br_word_t) (aff + 40));
}

value edc_gop(struct thread_info *tinfo, value a, value b) {
  uint8_t A[200], B[200], R[200], d2[40], out[64];
  ed25519_twice_d((br_word_t) d2);
  point_in(P(a), A);
  point_in(P(b), B);
  add((br_word_t) R, (br_word_t) A, (br_word_t) B, (br_word_t) d2);
  point_out(R, out);
  return ct_alloc(tinfo, CT_POINT_TAG, CT_POINT_WORDS, out);
}

value edc_ginv(struct thread_info *tinfo, value a) {
  uint8_t zero[40], fx[40], nx[40], out[64];
  const uint8_t *pa = P(a);
  fe25519_from_word((br_word_t) zero, (br_word_t) 0);
  fe25519_from_bytes((br_word_t) fx, (br_word_t) pa);
  fe25519_carry_sub((br_word_t) nx, (br_word_t) zero, (br_word_t) fx);
  fe25519_to_bytes((br_word_t) out, (br_word_t) nx);
  memcpy(out + 32, pa + 32, 32);
  return ct_alloc(tinfo, CT_POINT_TAG, CT_POINT_WORDS, out);
}

value edc_gpow(struct thread_info *tinfo, value Pv, value k) {
  uint8_t out[64];
  const uint8_t *pb = P(Pv);
  ed25519_smul_bytes((br_word_t) out, (br_word_t) (out + 32), (br_word_t) pb,
                     (br_word_t) (pb + 32), (br_word_t) K(k));
  return ct_alloc(tinfo, CT_POINT_TAG, CT_POINT_WORDS, out);
}

/* Ed.Gdec: left (ordinal 0) iff the canonical bytes are equal. */
value edc_eq(value a, value b) {
  return ct_sumbool_of_diff(ct_diff(P(a), P(b), 64));
}

/* point_to_Z: the pair (x, y) of integers.  Public points only. */
value edc_to_Z(struct thread_info *tinfo, value Pv) {
  uint8_t b[64];
  memcpy(b, P(Pv), 64);
  mp_limb_t limbs[2][4];
  mp_size_t sizes[2];
  uintnat words = 3;
  for (int i = 0; i < 2; i++) words += ct_int_words(b + 32 * i, limbs[i], &sizes[i]);
  ct_reserve(tinfo, words);
  value x = ct_make_int(tinfo, limbs[0], sizes[0]);
  value y = ct_make_int(tinfo, limbs[1], sizes[1]);
  value *p = tinfo->alloc;
  tinfo->alloc = p + 3;
  p[0] = (value) ((header_t) 2 << 10);  /* size 2, tag 0: the pair */
  p[1] = x;
  p[2] = y;
  return (value) (p + 1);
}

/* Examples.Ed25519Ins.h = Ed.gpow_fast Ed.B x: the public key, computed
   from the secret key x (zlc_secret_key) in constant time and then
   published, as a key generation publishes it. */
value edc_public_key(struct thread_info *tinfo) {
  value k = zlc_secret_key(tinfo);
  uint8_t kb[32], out[64];
  memcpy(kb, K(k), 32);  /* k may move in the collection of ct_alloc */
  const uint8_t *pb = P(edc_base());
  ed25519_smul_bytes((br_word_t) out, (br_word_t) (out + 32), (br_word_t) pb,
                     (br_word_t) (pb + 32), (br_word_t) kb);
  return edc_publish(ct_alloc(tinfo, CT_POINT_TAG, CT_POINT_WORDS, out));
}

/* publish_G: the point becomes public (for memcheck, its bytes become
   defined); the identity otherwise.  With CT_NO_DECLASSIFY (a control for
   the test) the published values stay secret. */
value edc_publish(value Pv) {
#ifndef CT_NO_DECLASSIFY
  VALGRIND_MAKE_MEM_DEFINED(P(Pv), 64);
#endif
  return Pv;
}
