From Stdlib Require Import String List ZArith.
From CeresBS Require Import Ceres.
Set Warnings "-masking-absolute-name".
From CakeML.Backend Require Import Pipeline Serialize.
From CakeML.CakeML Require Import ast namespace.
From MetaRocq Require Import ETransform Common.Transform Utils.bytestring.
From MetaRocq.Template Require All Loader TemplateMonad.
From MetaRocq.Utils Require Import monad_utils.
From Examples Require Import WasmBenchDefs.
Open Scope bs.
Import ListNotations.
Import Transform.
Import MRMonadNotation.

Fixpoint Mlet_ l b :=
  match l with
  | nil => b
  | cons (name, e) xs => Let (Some (String.to_string name)) e (Mlet_ xs b)
  end.

Definition eval_cakeml (cf := config.extraction_checker_flags)
  (p : Ast.Env.program) : string :=
  let p' := run (malfunction_pipeline Pipeline.default_malfunction_config)
              (nil, p) (MRUtils.todo "wf_env and welltyped term"%bs) in
  let t := Mlet_ (List.rev (List.flat_map (fun '(x, d) =>
             match d with Some b => cons (x, b) nil | None => nil end)
             (fst p'))) (snd p') in
  @to_string _ Serialize_t t.

Import Loader All.

Definition extract {A : Type} (a : A) :=
  t <- tmQuoteRec a ;;
  s <- tmEval lazy (eval_cakeml t) ;;
  tmMsg s ;; tmReturn tt.

Notation "'Extraction' a" := (extract a) (at level 1, a at level 2).

MetaRocq Run Extraction helios_wasm_ballot_bench.
