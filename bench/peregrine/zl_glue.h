/* The operations of Zl (integers modulo the Ed25519 group order l) by the
   verified bedrock2 arithmetic of fieldl_bedrock.c; see zl_glue.c. */
#ifndef ZL_GLUE_H
#define ZL_GLUE_H
#include "values.h"
#include "gc_stack.h"
value zl_add(struct thread_info *tinfo, value a, value b);
value zl_sub(struct thread_info *tinfo, value a, value b);
value zl_mul(struct thread_info *tinfo, value a, value b);
value zl_opp(struct thread_info *tinfo, value a);
#endif
