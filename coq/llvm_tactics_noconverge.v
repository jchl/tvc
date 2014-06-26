(******************************************************************************)
(* Tactics for proving non-convergence of LLVM IR programs.                   *)
(******************************************************************************)

Require opsem.
Import opsem.Opsem.
Require Import Tvc.base_tactics.
Require Import Tvc.notation.

(* The following lemmas are to be used instead of inversion on a hypothesis of the form sInsn; there
is a different lemma to be used depending on the next instruction. *)
Ltac solve_sInsn :=
  intros;
  match goal with
      [ H : sInsn _ _ _ _ |- _ ] => inversion H
  end;
  repeat eexists;
  eassumption.

Lemma store_sInsn :
  forall S TD Ps F B lc gl fs sid t align v1 v2 EC cs tmn Mem als FS tr,
    sInsn (mkCfg S TD Ps gl fs)
          (mkState ((mkEC F B ((insn_store sid t v1 v2 align)::cs) tmn lc als)::EC) Mem)
          FS tr ->
    exists mp2 gv1 Mem' gvs1 mps2,
      getOperandValue TD v1 lc gl = Some gvs1 /\
      getOperandValue TD v2 lc gl = Some mps2 /\
      gv1 @ gvs1 /\
      mp2 @ mps2 /\
      mstore TD Mem mp2 t gv1 align = Some Mem' /\
      eq FS (mkState ((mkEC F B cs tmn lc als)::EC) Mem').
Proof.
  solve_sInsn.
Qed.

(* XXX Other instructions TBD. *)

Lemma br_uncond_sInsn :
  forall S TD Ps F B lc gl fs bid l EC Mem als FS tr,
    sInsn (mkCfg S TD Ps gl fs)
          (mkState ((@mkEC GVsSig F B nil (insn_br_uncond bid l) lc als)::EC) Mem)
          FS tr ->
    exists ps' cs' tmn' lc',
      Some (stmts_intro ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) /\
      switchToNewBasicBlock TD (l, stmts_intro ps' cs' tmn') B gl lc = Some lc' /\
      eq FS (mkState ((mkEC F (l, stmts_intro ps' cs' tmn') cs' tmn' lc' als)::EC) Mem).
Proof.
  solve_sInsn.
Qed.

Lemma br_sInsn :
  forall S TD Ps F B lc gl fs bid Cond l1 l2 EC Mem als FS tr,
    sInsn (mkCfg S TD Ps gl fs)
          (mkState ((@mkEC GVsSig F B nil (insn_br bid Cond l1 l2) lc als)::EC) Mem)
          FS tr ->
    exists c conds ps' cs' tmn' lc',
      getOperandValue TD Cond lc gl = Some conds /\
      c @ conds /\
      Some (stmts_intro ps' cs' tmn') = (if isGVZero TD c
                                         then lookupBlockViaLabelFromFdef F l2
                                         else lookupBlockViaLabelFromFdef F l1) /\
      switchToNewBasicBlock TD (if isGVZero TD c then l2 else l1, stmts_intro ps' cs' tmn') B gl lc = Some lc' /\
      eq FS (mkState ((mkEC F (if isGVZero TD c then l2 else l1, stmts_intro ps' cs' tmn') cs' tmn' lc' als)::EC) Mem).
Proof.
  solve_sInsn.
Qed.

Ltac do_insn_simple tac :=
  match goal with
    | [ H : sInsn _ _ _ _ |- _ ] =>
      apply tac in H;
      decompose_ex H; try (progress (decompose [and] H); clear H); (* only clear if the decompose did something *)
      subst
  end.

Ltac do_store_simple := do_insn_simple store_sInsn.
(* XXX Other instructions TBD. *)
Ltac do_br_uncond_simple := do_insn_simple br_uncond_sInsn.
Ltac do_br_simple := do_insn_simple br_sInsn.

Fixpoint tailof {A : Type} (xs ys : list A) : Prop :=
    match ys with
      | [] => xs = ys
      | (y::ys') => xs = ys \/ tailof xs ys'
    end.

Fixpoint cmds_term_match {A B : Type} (xs : list A) (y : B) (zs : list (list A * B)) : Prop :=
  match zs with
    | [] => False
    | ((xs', y')::zs') => ((tailof xs xs') /\ (eq y y')) \/ (cmds_term_match xs y zs')
  end.

Ltac start_induction cmds_term_s :=
  match goal with
    | [ H1 : sop_star _ ?state _ _,
        H2 : eq (s_isFinialState _ _) _ |- _ ] =>
      clear - H1 H2;
      let H := fresh in
      let IS := fresh "IS" in
      remember state as IS eqn:H;
      match (eval hnf in (List.head state.(ECS))) with
        | Some ?ec =>
          let mem := (eval simpl in (state.(Mem))) in
          let bb := (eval simpl in (ec.(CurBB))) in
          let cs := (eval simpl in (ec.(CurCmds))) in
          let thecmds := fresh "thecmds" in
          let H3 := fresh in
          remember cs as thecmds eqn:H3 in H at 2; (* just replace in CurCmds, not in CurBB *)
          let term := (eval simpl in (ec.(Terminator))) in
          let theterm := fresh "theterm" in
          let H4 := fresh in
          remember term as theterm eqn:H4 in H at 2; (* just replace in Terminator, not in CurBB *)
          let H := (eval simpl in (cmds_term_match thecmds theterm cmds_term_s)) in
          assert H by auto;
          clear H3 H4;
          generalize dependent bb;
          generalize dependent thecmds;
          generalize dependent theterm;
          generalize dependent mem;
          induction H1; intros themem theterm thecmds H5 thebb ?; subst;
          [ decompose [and or] H5; try assumption; subst thecmds theterm; inversion H2 | ];
          decompose [and or] H5; try assumption; subst thecmds theterm; clear H5
          (* 'try assumption' takes care of the H5 : ... \/ False case *)
      end
  end.

Ltac apply_induction_hypothesis H :=
  eapply H; [ assumption | | reflexivity ]; auto.
  (* We leave the second subgoal (the equality with thecmds/theterm) to last, as otherwise it may
     cause the existential variables to be instantiated to the wrong values. *)

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "." "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
