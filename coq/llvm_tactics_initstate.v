(******************************************************************************)
(* Tactics for proving and using the 'initState_is' lemmas.                   *)
(******************************************************************************)

Require opsem.
Import opsem.Opsem.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Peano_dec.
Require Import Tvc.base_tactics.
Require Import Tvc.llvm_tactics_simplify.

Lemma instantiate_gv2gvs :
  forall TD v t a b c,
    (eq (genericvalues.LLVMgv.fit_gv TD t [(Values.Vint a b, c)]) (Some [(Values.Vint a b, c)])) ->
    eq v [(Values.Vint a b, c)] ->
    (eq (fun gv : genericvalues.LLVMgv.GenericValue =>
           exists gv1 gv2 : genericvalues.LLVMgv.GenericValue,
             ndopsem.MNDGVs.instantiate_gvs gv1 (ndopsem.MNDGVs.gv2gvs v t) /\
             genericvalues.LLVMgv.fit_gv TD t gv1 = Some gv2 /\
             ndopsem.MNDGVs.instantiate_gvs gv (ndopsem.MNDGVs.gv2gvs gv2 t))
        (ndopsem.MNDGVs.gv2gvs v t)).
Proof.
  intros ? ? ? ? ? ? H' H.
  subst.
  extensionality gv.
  apply Axioms.prop_ext.
  split.

  intro.
  decompose_ex H; decompose [and] H; clear H.
  inversion H0; clear H0; subst.
  rewrite H' in H2; clear H'.
  injection H2; intro; clear H2; subst.
  assumption.

  intro.
  exists [(Values.Vint a b, c)].
  exists [(Values.Vint a b, c)].
  repeat split.
  assumption.
  assumption.
Qed.

Transparent productInModuleB_dec.

Ltac prove_initState_is_1 :=
  let H := fresh in
  intro H;
  unfold s_genInitState in H;
  simpl in H;
  destruct_all_eq_dec;
  unfold infrastructure.LLVMinfra.productInModuleB_dec in H;
  unfold productInModuleB in H;
  unfold InProductsB in H;
  simpl in H;
  unfold productEqB in H;
  unfold sumbool2bool in H;
  repeat match goal with
           | [ _ : context [product_dec ?a ?a] |- _ ] =>
             let H := fresh in
             destruct (product_dec a a) as [_ | H]; [ | contradiction H; reflexivity ]
         end;
  simpl in H;
  repeat match goal with
           | [ _ : context [product_dec ?a ?b] |- _ ] =>
             let H := fresh in
             destruct (product_dec a b) as [H | _]; [ discriminate H | ]
             (* XXX this discriminate is very slow; I'm not sure why *)
         end;
  simpl in H;
  (* g, f, mem *)
  let f := fresh "f" in
  let g := fresh "g" in
  let mem := fresh "mem" in
  let H1 := fresh in
  match type of H with
    | eq (match ?e with | Some _ => _ | None => _ end) _ =>
      destruct e as [[[g f] mem] | ?] eqn:H1; try discriminate
  end;
  exists g;
  exists f;
  (* Get an equation for mem *)
  repeat match type of H1 with
           | eq (match (initFunTable ?m ?f) with | Some _ => _ | None => _ end) _ =>
             destruct (initFunTable m f) eqn:H2; clear H2; try discriminate
         end;
  repeat match type of H1 with
           | eq (match (initGlobal ?td ?g ?m ?id ?t ?c ?a) with | Some _ => _ | None => _ end) _ =>
             destruct (initGlobal td g m id t c a) as [[? ?]|] eqn:H2; clear H2; try discriminate
         end;
  injection H1; intros ? _ _; clear H1; subst mem;
  (* Locals *)
  match type of H with
    | eq (match ?e with | Some _ => _ | None => _ end) _ =>
      destruct e eqn:H2; try discriminate
  end.

Ltac prove_initState_is_2 H v i :=
  erewrite (instantiate_gv2gvs _ v _ _ _ _) in H; [ | | eassumption ]; [ |
    unfold fit_gv, gv_chunks_match_typb, gv_chunks_match_typb_aux, Values.Val.has_chunkb;
    let x := fresh "x" in
    destruct (eq_nat_dec _ _) as [? | x]; [ | contradiction x; reflexivity ];
    destruct i as [? [? ?]];
    destruct (Coqlib.zle _ _); [ | contradiction ];
    destruct (Coqlib.zlt _ _); [ | contradiction ];
    subst;
    reflexivity ].

(*
This tactic expects to find a hypothesis of the form:
  H : s_genInitState _ _ _ Memory.Mem.empty = Some (cfg, IS)
for some variables cfg, IS.  It will clear hypothesis H, and substitute all occurrences of cfg and
IS for their actual values.
*)
Ltac destruct_initState initState_is :=
  let H' := fresh in
  match goal with [ H : eq (s_genInitState _ _ _ Memory.Mem.empty) (Some (?cfg, ?IS)) |- _ ] =>
    let H' := fresh in
    pose proof initState_is as H';
    decompose_ex H'; decompose [and] H'; clear H';
    subst cfg IS;
    clear H
  end.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "." "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
