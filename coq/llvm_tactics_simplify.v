(******************************************************************************)
(* Tactics for simplifying the goal state of proofs about LLVM IR programs.   *)
(******************************************************************************)

Require opsem.
Import opsem.Opsem.
Require ndopsem.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.ZArith.ZArith.
Require Import Tvc.base_tactics.
Require Import Tvc.notation.
Require Import Tvc.definitions.

Ltac destruct_all_eq_dec := autorewrite with eq_dec_db in *.

Lemma simplify_const2GV_int :
  forall td g v1 v2 gn gns b c d e,
    eq (opsem.Opsem.const2GV td g (const_int v1 v2)) (Some gns) ->
    gn @ gns ->
    _const2GV td g (const_int v1 v2) = Some ([(Values.Vint c d, e)], b) ->
    eq gn [(Values.Vint c d, e)].
Proof.
  intros.

  unfold opsem.Opsem.const2GV in H.
  destruct (_const2GV td g (const_int v1 v2)).

  injection H1; clear H1; intros; subst.
  injection H; clear H; intro; subst.
  inversion H0.
  trivial.

  discriminate.
Qed.

(*
This tactic eliminates corresponding pairs of const2GV and instantiate_gvs.
*)
Ltac simplify_const2GV :=
  repeat match goal with
           | [ H1 : eq (const2GV _ _ _) (Some ?x),
               H2 : opsem.instantiate_gvs _ _ ?x |- _ ] =>
             eapply simplify_const2GV_int in H1; [ | eassumption | compute; reflexivity ]; clear H2; subst; try clear x
           | [ H1 : eq (const2GV _ _ _) (Some ?x),
               H2 : ndopsem.MNDGVs.instantiate_gvs _ ?x |- _ ] =>
             eapply simplify_const2GV_int in H1; [ | eassumption | compute; reflexivity ]; clear H2; subst; try clear x

         end.

(*
This tactic reduces (instantiate_gvs _ x (Ensembles.Singleton _ y)) to x = y.
*)
Ltac simplify_instantiate_gvs_singleton :=
  repeat match goal with
           | [ H : opsem.instantiate_gvs _ ?x (Ensembles.Singleton _ ?y) |- _ ] =>
             destruct H
           | [ H : ndopsem.MNDGVs.instantiate_gvs ?x (Ensembles.Singleton _ ?y) |- _ ] =>
             destruct H
         end.

(*
This tactic eliminates equations involving getTypeAllocSize.
*)
Ltac simplify_getTypeAllocSize :=
  repeat match goal with
           | [ H : eq (getTypeAllocSize _ _) (Some ?x) |- _ ] =>
             compute in H; injection H; clear H; intro; subst x
         end.

Ltac simplify :=
  unfold BOP, TRUNC, EXT, ICMP, getOperandValue, alist.updateAddAL, alist.lookupAL in *;
  destruct_all_eq_dec;
  simplify_const2GV;
  simplify_instantiate_gvs_singleton;
  simplify_getTypeAllocSize;
  injection_Some_eq_Some;
  subst;
  simplify_instantiate_gvs_singleton;
  simpl in *.

Ltac simplify_memory_op id Hnew :=
  unfold alist.updateAddAL, BOP, getOperandValue, alist.lookupAL in *;
  destruct_all_eq_dec;
  simplify_const2GV;
  simplify_instantiate_gvs_singleton;
  simplify_getTypeAllocSize;

  match goal with
     | [ H : context [id] |- _ ] => cbv delta [id] in H; simpl in H; rename H into Hnew
  end;
  simpl in *;

  injection_Some_eq_Some;
  subst;
  simplify_instantiate_gvs_singleton;
  simpl in *.

Ltac simplify_alloca H := simplify_memory_op genericvalues.LLVMgv.malloc H.
Ltac simplify_load H := simplify_memory_op genericvalues.LLVMgv.mload H; try destruct_match_Some.
Ltac simplify_store H := simplify_memory_op genericvalues.LLVMgv.mstore H; try destruct_match_Some.

Lemma lift_op1_simplified :
  forall op v t x y a b c,
    eq y [(Values.Vint a b, c)] ->
    (ndopsem.MNDGVs.lift_op1 op
                             (Ensembles.Singleton genericvalues.LLVMgv.GenericValue v)
                             t = Some x ->
     op v = Some y ->
     eq (Ensembles.Singleton genericvalues.LLVMgv.GenericValue y) x).
Proof.
  intros op v t x y a b c H H0 H1.
  unfold ndopsem.MNDGVs.lift_op1 in H0.
  unfold ndopsem.MNDGVs.instantiate_gvs in H0.
  unfold ndopsem.MNDGVs.gv2gvs in H0.
  injection H0; clear H0; intro H0.
  subst x.
  extensionality z.
  apply Axioms.prop_ext.
  split.
  intro.
  repeat eexists.
  apply H1.
  rewrite H.
  rewrite <- H.
  unfold Ensembles.In.
  assumption.
  intro.
  decompose [ex and] H0; clear H0.
  destruct H2.
  rewrite H1 in H3.
  injection H3; clear H3; intro H3.
  subst x0.
  subst y.
  assumption.
Qed.

Ltac simplify_lifted_op_1 :=
  simplify;
  match goal with
    | [ H : eq (ndopsem.MNDGVs.lift_op1 _ _ _) _ |- _ ] =>
      eapply lift_op1_simplified in H; [
        | reflexivity
        | compute; reflexivity ]
  end;
  subst.

Lemma lift_op2_simplified :
  forall op v1 v2 t x y a b c,
    eq y [(Values.Vint a b, c)] ->
    (ndopsem.MNDGVs.lift_op2 op
                             (Ensembles.Singleton genericvalues.LLVMgv.GenericValue v1)
                             (Ensembles.Singleton genericvalues.LLVMgv.GenericValue v2)
                             t = Some x ->
     op v1 v2 = Some y ->
     eq (Ensembles.Singleton genericvalues.LLVMgv.GenericValue y) x).
Proof.
  intros op v1 v2 t x y a b c H H0 H1.
  unfold ndopsem.MNDGVs.lift_op2 in H0.
  unfold ndopsem.MNDGVs.instantiate_gvs in H0.
  unfold ndopsem.MNDGVs.gv2gvs in H0.
  injection H0; clear H0; intro H0.
  subst x.
  extensionality z.
  apply Axioms.prop_ext.
  split.
  intro.
  repeat eexists.
  apply H1.
  rewrite H.
  rewrite <- H.
  unfold Ensembles.In.
  assumption.
  intro.
  decompose [ex and] H0; clear H0.
  destruct H2.
  destruct H3.
  rewrite H1 in H4.
  injection H4; clear H4; intro H4.
  subst x1.
  subst y.
  assumption.
Qed.

Ltac simplify_lifted_op_2 :=
  simplify;
  match goal with
    | [ H : eq (ndopsem.MNDGVs.lift_op2 _ _ _ _) _ |- _ ] =>
      eapply lift_op2_simplified in H; [
        | reflexivity
        | compute; reflexivity ]
  end;
  subst.

Ltac simplify_bop := simplify_lifted_op_2.
Ltac simplify_trunc := simplify_lifted_op_1.
Ltac simplify_ext := simplify_lifted_op_1.
Ltac simplify_icmp := simplify_lifted_op_2.

Ltac simplify_select :=
  unfold getOperandValue, alist.lookupAL in *;
  destruct_all_eq_dec;
  injection_Some_eq_Some;
  subst;
  simplify_instantiate_gvs_singleton;
  simpl in *;
  destruct_all_eq_dec;
  repeat match goal with
           | [ H : eq (const2GV _ _ _) (Some _) |- _ ] =>
             compute in H;
             injection H; clear H; intro H; subst
         end.

Ltac simplify_br_uncond :=
  match goal with
    | [ H1 : eq _ (lookupBlockViaLabelFromFdef _ _),
        H2 : eq (switchToNewBasicBlock _ _ _ _ _) _ |- _ ] =>
      unfold lookupBlockViaLabelFromFdef in H1;
      simpl in H1;
      simplify;
      injection H1; clear H1; intros; subst;
      unfold switchToNewBasicBlock in H2;
      simpl in H2;
      injection_Some_eq_Some;
      subst
  end.

Ltac simplify_br :=
  match goal with
    | [ H1 : eq _ (if isGVZero _ _ then _ else _),
        H2 : eq (switchToNewBasicBlock _ _ _ _ _) _ |- _ ] =>
      unfold getOperandValue, alist.lookupAL in *;
      destruct_all_eq_dec;
      injection_Some_eq_Some;
      subst;
      simplify_instantiate_gvs_singleton;
      simpl in *;
      destruct_all_eq_dec;
      injection H1; clear H1; intros; subst;
      unfold switchToNewBasicBlock in H2;
      simpl in H2;
      injection_Some_eq_Some;
      subst
  end.

Ltac simplify_ret :=
  unfold getOperandValue, alist.lookupAL in *;
  destruct_all_eq_dec;
  injection_Some_eq_Some;
  subst;
  simplify_const2GV;
  simplify_instantiate_gvs_singleton.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "." "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
