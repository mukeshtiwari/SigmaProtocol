/* peregrine_numeral_of_string: the hook that Peregrine's numeral hoisting
   (the generated peregrine_numerals.h) calls to build each hoisted numeral
   once.  It returns the integer in the representation of z_gmp.c: unboxed
   when it fits, otherwise a block outside the CertiRocq heap (a no-scan
   header, the signed size and the limbs), which the collector does not move,
   so that the caller can cache it. */
#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include "gc_stack.h"

value peregrine_numeral_of_string(const char *s) {
  mpz_t m;
  if (mpz_init_set_str(m, s, 10) != 0) abort();
  if (mpz_fits_slong_p(m)) {
    long l = mpz_get_si(m);
    if (l >= Min_long && l <= Max_long) { mpz_clear(m); return Val_long(l); }
  }
  mp_size_t sz = m->_mp_size, n = sz < 0 ? -sz : sz;
  value *p = malloc(((size_t) n + 2) * sizeof(value));
  if (p == NULL) abort();
  p[0] = (value) (((header_t) (n + 1) << 10) | No_scan_tag);
  p[1] = (value) sz;
  memcpy(p + 2, m->_mp_d, (size_t) n * sizeof(mp_limb_t));
  mpz_clear(m);
  return (value) (p + 1);
}
