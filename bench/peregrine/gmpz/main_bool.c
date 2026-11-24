/* Driver for an extracted closed [bool] compiled by Peregrine's C backend.
   [body] is the extracted program; bool is unboxed: true is ordinal 0,
   false is ordinal 1. */
#include <stdio.h>
#include "gc_stack.h"
extern value body(struct thread_info *);
int main(void) {
  struct thread_info *tinfo = make_tinfo();
  value v = body(tinfo);
  if (Is_long(v)) printf("%s\n", (v >> 1) == 0 ? "true" : "false");
  else printf("unexpected block tag %u\n", (unsigned) Tag_val(v));
  return 0;
}
