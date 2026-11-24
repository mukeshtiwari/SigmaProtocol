/* Ed.G as 64-byte values for the constant-time build; see
   ed25519_ct_glue.c. */
#ifndef ED25519_CT_GLUE_H
#define ED25519_CT_GLUE_H
#include "values.h"
#include "gc_stack.h"
value edc_base(void);
value edc_gid(void);
value edc_gop(struct thread_info *tinfo, value a, value b);
value edc_ginv(struct thread_info *tinfo, value a);
value edc_gpow(struct thread_info *tinfo, value P, value k);
value edc_eq(value a, value b);
value edc_to_Z(struct thread_info *tinfo, value P);
value edc_public_key(struct thread_info *tinfo);
value edc_publish(value P);
#endif
