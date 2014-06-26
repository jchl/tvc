(******************************************************************************)
(* Basic definitions used in the statement of the equivalence theorems.       *)
(******************************************************************************)

Require Csem.global.
Require Csem.core.
Require Import Csem.core_run.
Require Import Csem.core_run_inductive.
Require Import Csem.core_run_effect.
Require ndopsem.
Require genericvalues.
Require Import MetatheoryAtom.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Tvc.base_tactics.
Require Import Tvc.notation.

Definition core_program := Csem.core.file_ global.zero.
Definition core_value := Csem.core.expr global.zero.
Definition llvm_program := syntax.LLVMsyntax.system.
Definition llvm_value := genericvalues.LLVMgv.GenericValue.

(* C types. *)
Inductive ctype : Type :=
  | Signed_ : nat -> ctype
  | Unsigned_ : nat -> ctype.

Definition width (t : ctype) : nat :=
  match t with
    | Signed_ w => w
    | Unsigned_ w => w
  end.

Definition ctype_to_llvm_type (t : ctype) :=
  syntax.LLVMsyntax.typ_int (width t).

(* Well-typedness for LLVM values. *)
Definition is_well_typed (t : ctype) (v : llvm_value) :=
  exists i,
    eq v [(Values.Vint (width t - 1) i, AST.Mint (width t - 1))].

(* Conversion of LLVM values to Core values. *)
Definition llvm_value_to_core_value
           (td : syntax.LLVMsyntax.targetdata) (t : ctype) (v : llvm_value) : option core_value :=
  match (genericvalues.LLVMgv.GV2val td v) with
    | Some v =>
      match v with
        | Values.Vint sz i =>
          match t with
            | Signed_ _ => Some (Csem.core.Econst (Csem.cmm_aux.Cint (Integers.Int.signed _ i)))
            | Unsigned_ _ => Some (Csem.core.Econst (Csem.cmm_aux.Cint (Integers.Int.unsigned _ i)))
          end
        | _ => None
      end
    | None => None
  end.

(* Convergence and divergence for LLVM IR programs. *)
Definition _args_at_tys (args_tys : list (llvm_value * ctype)) :=
  map (fun gvt => match gvt with (gv, t) => $ gv # ctype_to_llvm_type t $ end) args_tys.

Definition llvm_converges
           (system : llvm_program) (main : atom)
           (args_tys : list (llvm_value * ctype)) (v : llvm_value) : Prop :=
  (exists (gvs : GVs),
    (exists (tr : events.trace),
       @opsem.Opsem.s_converges GVsSig system main (_args_at_tys args_tys) tr gvs) /\
    (GVsSig.(opsem.instantiate_gvs) v gvs)).

Definition llvm_diverges
           (system : llvm_program) (main : atom)
           (args_tys : list (llvm_value * ctype)) : Prop :=
  (exists (tr : events.traceinf),
     @opsem.Opsem.s_diverges GVsSig system main (_args_at_tys args_tys) tr).

(* Convergence, divergence and undefinedness for Core programs. *)
Definition core_converges (f : core_program) (args : list core_value) (v : core_value) : Prop :=
  ((forallb Csem.core.is_value args) = true) /\
  ((Csem.core.is_value v) = true) /\
  (exists (t : cmm_csem.tid0) (s : core_run_effect.state),
     (star_red2_ind (initial_expr_and_state_with_args Exhaustive f args) ((convert_expr v, t, []), s))).

Definition core_diverges (f : core_program) (args : list core_value) : Prop :=
  ((forallb Csem.core.is_value args) = true) /\
  (star_red2_diverges (initial_expr_and_state_with_args Exhaustive f args)).

Definition core_undefined (f : core_program) (args : list core_value) : Prop :=
  ((forallb Csem.core.is_value args) = true) /\
  (star_red2_undef_ind (initial_expr_and_state_with_args Exhaustive f args)).
