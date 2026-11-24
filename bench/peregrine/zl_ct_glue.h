/* Zl.F as 32-byte values for the constant-time build; see zl_ct_glue.c. */
#ifndef ZL_CT_GLUE_H
#define ZL_CT_GLUE_H
#include "values.h"
#include "gc_stack.h"
value zlc_zero(void);
value zlc_one(void);
value zlc_add(struct thread_info *tinfo, value a, value b);
value zlc_sub(struct thread_info *tinfo, value a, value b);
value zlc_mul(struct thread_info *tinfo, value a, value b);
value zlc_opp(struct thread_info *tinfo, value a);
value zlc_eq(value a, value b);
value zlc_of_Z(struct thread_info *tinfo, value z);
value zlc_to_Z(struct thread_info *tinfo, value a);
value zlc_secret(struct thread_info *tinfo, value i);
value zlc_secret_key(struct thread_info *tinfo);
value zlc_publish(value a);
#endif
