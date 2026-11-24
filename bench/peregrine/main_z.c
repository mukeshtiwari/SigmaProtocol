/* Driver for an extracted closed [Z] compiled by Peregrine's C backend with
   the GMP remapping of Z: prints the integer in decimal. */
#include <stdio.h>
#include "gc_stack.h"
#include "z_gmp.h"
extern value body(struct thread_info *);
int main(void) {
  struct thread_info *tinfo = make_tinfo();
  value v = body(tinfo);
  printf("%s\n", zg_to_string(v));
  return 0;
}
