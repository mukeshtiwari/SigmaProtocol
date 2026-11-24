/* The Jasmin build of the verified bedrock2 code (programs *_jasmin and
   *_jasminl of build.sh).

   ed25519_bedrock.jazz and fieldl_bedrock.jazz are the bedrock2 functions
   of ed25519_bedrock.c and fieldl_bedrock.c printed as Jasmin
   (bedrock/jasmin/EmitJasmin.v), compiled to assembly by jasminc.  In that
   build, build.sh compiles copies of ed25519_glue.c and zl_glue.c in a
   directory where the files ed25519_bedrock.c and fieldl_bedrock.c that the
   glue includes consist of the line #include "bedrock_jasmin.h".  This
   header declares the export functions of the two Jasmin modules under the
   names the glue calls.  An export function takes the addresses of its
   buffers (System V calling convention) and returns the addresses of the
   buffers it writes, which the glue ignores. */
#ifndef BEDROCK_JASMIN_H
#define BEDROCK_JASMIN_H
#include <stdint.h>

typedef uintptr_t br_word_t;

/* ed25519_bedrock.jazz */
void jasmin_ed25519_smul_bytes(br_word_t p_ox, br_word_t p_oy, br_word_t p_x, br_word_t p_y,
                               br_word_t p_k);
#define ed25519_smul_bytes jasmin_ed25519_smul_bytes

/* fieldl_bedrock.jazz */
void jasmin_zl_add_bytes(br_word_t p_out, br_word_t p_a, br_word_t p_b);
void jasmin_zl_sub_bytes(br_word_t p_out, br_word_t p_a, br_word_t p_b);
void jasmin_zl_mul_bytes(br_word_t p_out, br_word_t p_a, br_word_t p_b);
void jasmin_zl_opp_bytes(br_word_t p_out, br_word_t p_a);
#define zl_add_bytes jasmin_zl_add_bytes
#define zl_sub_bytes jasmin_zl_sub_bytes
#define zl_mul_bytes jasmin_zl_mul_bytes
#define zl_opp_bytes jasmin_zl_opp_bytes
#endif
