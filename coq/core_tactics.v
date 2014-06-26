(******************************************************************************)
(* Tactics for working with Core programs.                                    *)
(******************************************************************************)

Require Import core_run_inductive.
Require Import Tvc.base_tactics.
Require Import Tvc.definitions.
Require Import Tvc.core_props.

(*
This tactic generalizes the trace and tid components of a goal of the form:
  plus_red2_diverges expr
enabling the resulting generalized goal to be proved by coinduction.
*)
Ltac generalize_trace_and_tid :=
  match goal with
    | |- plus_red2_diverges (_, ?tid', _, ?state) =>
      let trace' := (eval hnf in (state.(Csem.core_run_effect.trace))) in
      generalize trace' as trace;
      generalize tid' as tid;
      clear
  end.

Ltac pose_cv v cv :=
  let H := fresh in
  let x := fresh "x" in
  remember v as x eqn:H in |-;
  repeat match goal with
           | [ _ : eq ?v0 _ |- _ ] => replace v0 in H
         end;
  compute -[Integers.Int.signed Integers.Int.modulus] in H;
  match type of H with
    | eq _ ?v =>
      match v with
        | Some ?v' => pose (cv := v')
      end
  end;
  clear x H.

Ltac pose_s_and_t core_file args n :=
  let x := (eval compute -[Integers.Int.signed Integers.Int.modulus] in
               (red2nb n (core_run.initial_expr_and_state_with_args core_run_effect.Exhaustive core_file args))) in
  match head x with
    | (Defined0 (_, ?t', _), ?s') => pose (s := s'); pose (t := t')
  end.

Ltac pose_s_and_t' core_file args n :=
  let x := (eval compute -[Integers.Int.signed Integers.Int.modulus] in
               (red2nb' n (core_run.initial_expr_and_state_with_args core_run_effect.Exhaustive core_file args))) in
  match x with
    | (Defined0 (_, ?t', _), ?s') => pose (s := s'); pose (t := t')
  end.

Ltac pose_s_and_u_helper x :=
  match head x with
    | (Undef ?u', ?s') => pose (s := s'); pose (u := u')
    | _ => let y := tail x in
           pose_s_and_u_helper y
  end.

Ltac pose_s_and_u core_file args n :=
  let x := (eval compute -[Integers.Int.signed Integers.Int.modulus] in
               (red2nb n (core_run.initial_expr_and_state_with_args core_run_effect.Exhaustive core_file args))) in
  pose_s_and_u_helper x.

Ltac pose_s_and_u' core_file args n :=
  let x := (eval compute -[Integers.Int.signed Integers.Int.modulus] in
               (red2nb' n (core_run.initial_expr_and_state_with_args core_run_effect.Exhaustive core_file args))) in
  match x with
    | (Undef ?u', ?s') => pose (s := s'); pose (u := u')
  end.

Ltac pose_s_and_e n :=
  match goal with
    | |- core_run_inductive.plus_red2_diverges (?e', ?s') =>
      let x := (eval compute -[Integers.Int.signed Integers.Int.modulus] in (red2n n e' s')) in
      match head x with
        | (Defined0 ?e'', ?s'') => pose (s := s''); pose (e := e'')
      end
  end.

Ltac pose_s_and_e_converges n :=
  match goal with
    | |- core_run_inductive.star_red2_ind (?e', ?s') _ =>
      let x := (eval compute -[Integers.Int.signed Integers.Int.modulus] in (red2n n e' s')) in
      match head x with
        | (Defined0 ?e'', ?s'') => pose (s2 := s''); pose (e2 := e'')
      end
  end.

Ltac pose_s_and_t_converges n :=
  match goal with
    | |- core_run_inductive.star_red2_ind (?e', ?s') _ =>
      let x := (eval compute -[Integers.Int.signed Integers.Int.modulus] in (red2n n e' s')) in
      match head x with
        | (Defined0 (_, ?t', _), ?s'') => pose (s2 := s''); pose (t2 := t')
      end
  end.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "." "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
