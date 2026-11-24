(** Axiom audit of [ExecFieldL.v], kept apart because printing the
    assumptions in that file needs more than 3 GB.  [fl_exec_to_bytes] is
    left out: printing its assumptions alone needs more than 3 GB, and
    [ZlBytes.zl_exec_add_bytes], whose assumptions [ZlBytes.v] prints, uses
    it. *)
Require Import Bridge.ExecFieldL.
Print Assumptions Bridge.ExecFieldL.fl_exec_add.
Print Assumptions Bridge.ExecFieldL.fl_exec_sub.
Print Assumptions Bridge.ExecFieldL.fl_exec_mul.
Print Assumptions Bridge.ExecFieldL.fl_exec_opp.
Print Assumptions Bridge.ExecFieldL.fl_exec_add_raw.
Print Assumptions Bridge.ExecFieldL.fl_exec_sub_raw.
Print Assumptions Bridge.ExecFieldL.fl_exec_opp_raw.
Print Assumptions Bridge.ExecFieldL.fl_exec_mul_raw.
Print Assumptions Bridge.ExecFieldL.fl_exec_to_mont.
Print Assumptions Bridge.ExecFieldL.fl_exec_from_mont.
Print Assumptions Bridge.ExecFieldL.fl_exec_from_bytes.
