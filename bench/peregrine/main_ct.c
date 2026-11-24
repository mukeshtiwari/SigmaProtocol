/* Driver for the constant-time build (programs *_ct of build.sh).

   Before the extracted program [body] runs, the buffer of secret scalars
   (zlc_secret_bytes of zl_ct_glue.c: the encryption randomness, the votes,
   the proof randomness and the decryption key) is marked undefined for
   valgrind's memcheck (the technique of Langley's ctgrind).  memcheck then
   tracks every value computed from a secret, and reports
     "Conditional jump or move depends on uninitialised value(s)"
   where a branch or conditional move depends on a secret, and
     "Use of uninitialised value of size N"
   where a memory address does (with --track-origins=yes, both name the
   origin).  The program publishes the values of a ballot through
   publish_F and publish_G (zlc_publish, edc_publish), which mark them
   defined.  Outside valgrind the marking does nothing.

   The program prints its result: a bool, or with CT_RESULT_Z an integer in
   decimal (the *_digest programs). */
#include <stdio.h>
#include <stdint.h>
#include "gc_stack.h"
#ifdef CT_RESULT_Z
#include "z_gmp.h"
#endif
#if defined(__has_include)
#if __has_include(<valgrind/memcheck.h>)
#include <valgrind/memcheck.h>
#endif
#endif
#ifndef VALGRIND_MAKE_MEM_UNDEFINED
#define VALGRIND_MAKE_MEM_UNDEFINED(p, n) ((void) 0)
#endif

extern value body(struct thread_info *);
extern uint8_t zlc_secret_bytes[][32];
extern const size_t zlc_secret_size;

int main(void) {
  struct thread_info *tinfo = make_tinfo();
  VALGRIND_MAKE_MEM_UNDEFINED(zlc_secret_bytes, zlc_secret_size);
  value v = body(tinfo);
#ifdef CT_RESULT_Z
  printf("%s\n", zg_to_string(v));
#else
  if (Is_long(v)) printf("%s\n", (v >> 1) == 0 ? "true" : "false");
  else printf("unexpected block tag %u\n", (unsigned) Tag_val(v));
#endif
  return 0;
}
