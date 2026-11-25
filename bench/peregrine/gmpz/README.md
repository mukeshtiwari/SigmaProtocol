The GMP remapping of `Z`, `positive` and `N` for Peregrine's C backend, from
an existing KZG demonstrator (`demo/extraction/GmpZ.v` and `demo/c-exec`, MIT
licence; the repository is not linked for anonymous review). `GmpZ.v` states the remapping as
Peregrine constant and inductive remappings; `z_gmp.c` and `z_gmp.h`
implement the operations with GMP in the CertiRocq heap; the Python scripts
splice the remapping into a λ□ program (`splice_gmp_z.py`,
`splice_locked.py`), realise the remaining axioms as C stubs
(`stub_axioms.py`), and raise the recursion limit for both (`run_deep.py`).
`main_bool.c` runs an extracted closed `bool`. All of it is trusted.
