/* Ed.fast_smul by the verified bedrock2 scalar multiplication; see
   ed25519_glue.c. */
#ifndef ED25519_GLUE_H
#define ED25519_GLUE_H
#include "values.h"
#include "gc_stack.h"
value ed25519_fast_smul(struct thread_info *tinfo, value n, value P);
#endif
