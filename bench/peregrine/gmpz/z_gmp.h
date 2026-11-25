/* Z, positive and N as GMP integers in the CertiRocq heap, for extracted
   code; see z_gmp.c. */
#ifndef Z_GMP_H
#define Z_GMP_H

#include "values.h"
#include "gc_stack.h"

/* constructors and case analyses of the remapped inductives */
value zg_Z0(void);
value zg_Zpos(value p);
value zg_Zneg(struct thread_info *tinfo, value p);
value zg_xH(void);
value zg_xO(struct thread_info *tinfo, value p);
value zg_xI(struct thread_info *tinfo, value p);
value zg_N0(void);
value zg_Npos(value p);
value zg_z_case(struct thread_info *tinfo, value z, value f0, value fpos, value fneg);
value zg_pos_case(struct thread_info *tinfo, value p, value fI, value fO, value fH);
value zg_n_case(struct thread_info *tinfo, value n, value f0, value fpos);

/* operations, with the semantics of Rocq's Z, Pos and N.  The functions that
   take the thread_info may allocate in the heap and call the collector. */
value zg_add(struct thread_info *tinfo, value x, value y);
value zg_sub(struct thread_info *tinfo, value x, value y);
value zg_mul(struct thread_info *tinfo, value x, value y);
value zg_opp(struct thread_info *tinfo, value x);
value zg_abs(struct thread_info *tinfo, value x);
value zg_fdiv(struct thread_info *tinfo, value x, value y);   /* Z.div: floor, x / 0 = 0 */
value zg_fmod(struct thread_info *tinfo, value x, value y);   /* Z.modulo: floor, x mod 0 = x */
value zg_tdiv(struct thread_info *tinfo, value x, value y);   /* Z.quot: truncated, x / 0 = 0 */
value zg_tmod(struct thread_info *tinfo, value x, value y);   /* Z.rem: truncated, x rem 0 = x */
value zg_pow(struct thread_info *tinfo, value x, value y);    /* Z.pow: y < 0 gives 0 */
value zg_shiftl(struct thread_info *tinfo, value x, value y); /* Z.shiftl: y < 0 shifts right */
value zg_shiftr(struct thread_info *tinfo, value x, value y); /* Z.shiftr: floor */
value zg_land(struct thread_info *tinfo, value x, value y);
value zg_lor(struct thread_info *tinfo, value x, value y);
value zg_lxor(struct thread_info *tinfo, value x, value y);
value zg_testbit(value x, value y);
value zg_compare(value x, value y);
value zg_eqb(value x, value y);
value zg_leb(value x, value y);
value zg_ltb(value x, value y);
value zg_pos_sub_trunc(struct thread_info *tinfo, value x, value y); /* Pos.sub: 1 when x <= y */
value zg_n_sub_trunc(struct thread_info *tinfo, value x, value y);   /* N.sub: 0 when x <= y */
value zg_pos_pred(struct thread_info *tinfo, value x);               /* Pos.pred: pred 1 = 1 */
value zg_n_pred(struct thread_info *tinfo, value x);                 /* N.pred: pred 0 = 0 */
value zg_pos_size(value x);               /* Pos.size, as a positive */
value zg_to_pos(value x);                 /* Z.to_pos: 1 when x <= 0 */
value zg_to_n(value x);                   /* Z.to_N: 0 when x < 0 */
char *zg_to_string(value x);

#endif
