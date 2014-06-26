(******************************************************************************)
(* Tactics for proving non-divergence of LLVM IR programs.                    *)
(******************************************************************************)

Require opsem.
Import opsem.Opsem.
Require Import Tvc.base_tactics.
Require Import Tvc.notation.
Require Import Tvc.llvm_tactics_simplify.

(* This lemma is to be used instead of inversion on a hypothesis of the form s_diverges. *)
Lemma invert_diverges :
  forall s main args x0,
    @s_diverges GVsSig s main args x0 ->
    exists cfg IS,
      s_genInitState s main args Memory.Mem.empty = Some (cfg, IS) /\
      sop_diverges cfg IS x0.
Proof.
  intros.
  inversion H.
  repeat eexists; eassumption.
Qed.

(* The following lemmas are to be used instead of inversion on a hypothesis of the form
sop_diverges'; there is a different lemma to be used depending on the next instruction. *)
Ltac solve_diverges :=
  intros;
  match goal with
    | [ H : sop_diverges' _ _ _ |- _ ] => inversion_clear H
  end;
  match goal with
    | [ H : sInsn _ _ _ _ |- _ ] => inversion H; clear H; subst
  end;
  repeat match goal with
    | [ |- ex _ ] => eexists
  end;
  repeat split;
  eassumption.

Lemma alloca_diverges :
  forall cfg F B id t v align cs tmn EC lc als Mem tr,
    sop_diverges' cfg (mkState ((@mkEC GVsSig F B ((insn_alloca id t v align)::cs) tmn lc als)::EC) Mem) tr ->
    exists lc' als' Mem' tr',
      sop_diverges' cfg (mkState ((@mkEC GVsSig F B cs tmn lc' als')::EC) Mem') tr'.
Proof.
  solve_diverges.
Qed.

Lemma load_diverges :
  forall cfg F B id t v align cs tmn EC lc als Mem tr,
    sop_diverges' cfg (mkState ((@mkEC GVsSig F B ((insn_load id t v align)::cs) tmn lc als)::EC) Mem) tr ->
    exists lc' als' Mem' tr',
      sop_diverges' cfg (mkState ((@mkEC GVsSig F B cs tmn lc' als')::EC) Mem') tr'.
Proof.
  solve_diverges.
Qed.

Lemma store_diverges :
  forall cfg F B sid t v1 v2 align cs tmn EC lc als Mem tr,
    sop_diverges' cfg (mkState ((@mkEC GVsSig F B ((insn_store sid t v1 v2 align)::cs) tmn lc als)::EC) Mem) tr ->
    exists lc' als' Mem' tr',
      sop_diverges' cfg (mkState ((@mkEC GVsSig F B cs tmn lc' als')::EC) Mem') tr'.
Proof.
  solve_diverges.
Qed.

Lemma bop_diverges :
  forall cfg F B id bop sz v1 v2 cs tmn EC lc als Mem tr,
    sop_diverges' cfg (mkState ((@mkEC GVsSig F B ((insn_bop id bop sz v1 v2)::cs) tmn lc als)::EC) Mem) tr ->
    exists lc' als' Mem' tr',
      sop_diverges' cfg (mkState ((@mkEC GVsSig F B cs tmn lc' als')::EC) Mem') tr'.
Proof.
  solve_diverges.
Qed.

Lemma trunc_diverges :
  forall cfg F B lc id truncop t1 v1 t2 EC cs tmn Mem als tr,
    sop_diverges' cfg (mkState ((@mkEC GVsSig F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc als)::EC) Mem) tr ->
    exists lc' als' Mem' tr',
      sop_diverges' cfg (mkState ((@mkEC GVsSig F B cs tmn lc' als')::EC) Mem') tr'.
Proof.
  solve_diverges.
Qed.

Lemma ext_diverges :
  forall cfg F B lc id extop t1 v1 t2 EC cs tmn Mem als tr,
    sop_diverges' cfg (mkState ((@mkEC GVsSig F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc als)::EC) Mem) tr ->
    exists lc' als' Mem' tr',
      sop_diverges' cfg (mkState ((@mkEC GVsSig F B cs tmn lc' als')::EC) Mem') tr'.
Proof.
  solve_diverges.
Qed.

Lemma icmp_diverges :
  forall cfg F B lc id cond t v1 v2 EC cs tmn Mem als tr,
    sop_diverges' cfg (mkState ((@mkEC GVsSig F B ((insn_icmp id cond t v1 v2)::cs) tmn lc als)::EC) Mem) tr ->
    exists lc' als' Mem' tr',
      sop_diverges' cfg (mkState ((@mkEC GVsSig F B cs tmn lc' als')::EC) Mem') tr'.
Proof.
  solve_diverges.
Qed.

Lemma select_diverges :
  forall cfg F B lc id v0 t v1 v2 EC cs tmn Mem als tr,
    sop_diverges' cfg (mkState ((@mkEC GVsSig F B ((insn_select id v0 t v1 v2)::cs) tmn lc als)::EC) Mem) tr ->
    exists lc' als' Mem' tr',
      sop_diverges' cfg (mkState ((@mkEC GVsSig F B cs tmn lc' als')::EC) Mem') tr'.
Proof.
  solve_diverges.
Qed.

Lemma br_diverges :
  forall cfg F B lc bid Cond l1 l2 EC Mem als tr,
    sop_diverges' cfg (mkState ((@mkEC GVsSig F B nil (insn_br bid Cond l1 l2) lc als)::EC) Mem) tr ->
    exists (c : bool) gl ps' cs' tmn' lc' als' Mem' tr',
      Some (stmts_intro ps' cs' tmn') = (if c then lookupBlockViaLabelFromFdef F l2 else lookupBlockViaLabelFromFdef F l1) /\
      switchToNewBasicBlock (CurTargetData cfg) (if c then l2 else l1, stmts_intro ps' cs' tmn') B gl lc = Some lc' /\
      sop_diverges' cfg (mkState ((@mkEC GVsSig F (if c then l2 else l1, stmts_intro ps' cs' tmn') cs' tmn' lc' als')::EC) Mem') tr'.
Proof.
  solve_diverges.
Qed.

Lemma br_uncond_diverges :
  forall cfg F B lc bid l EC Mem als tr,
    sop_diverges' cfg (mkState ((@mkEC GVsSig F B nil (insn_br_uncond bid l) lc als)::EC) Mem) tr ->
    exists gl ps' cs' tmn' lc' als' Mem' tr',
      Some (stmts_intro ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) /\
      switchToNewBasicBlock (CurTargetData cfg) (l, stmts_intro ps' cs' tmn') B gl lc = Some lc' /\
      sop_diverges' cfg (mkState ((@mkEC GVsSig F (l, stmts_intro ps' cs' tmn') cs' tmn' lc' als')::EC) Mem') tr'.
Proof.
  solve_diverges.
Qed.

Lemma final_ret_diverges :
  forall cfg F B lc rid RetTy Result Mem als tr,
    sop_diverges' cfg (mkState ((@mkEC GVsSig F B nil (insn_return rid RetTy Result) lc als)::nil) Mem) tr ->
    False.
Proof.
  solve_diverges.
Qed.

(*
This tactic will prove any goal if there is a hypothesis of the form
  H : sop_diverges' _ _ _
where the thing that is claimed to diverge is a single basic block terminated by a return statement.

If the basic block is not terminated by a return statement, then the resulting goal will be that
the program continuing from the terminator diverges.
*)
Ltac single_basic_block_does_not_diverge :=
  repeat match goal with
           | [ H : sop_diverges' _ _ _ |- _ ] =>
             first [ apply alloca_diverges in H |
                     apply load_diverges in H |
                     apply store_diverges in H |
                     apply bop_diverges in H |
                     apply trunc_diverges in H |
                     apply ext_diverges in H |
                     apply icmp_diverges in H |
                     apply select_diverges in H |
                     exfalso; apply final_ret_diverges in H; assumption ];
               clear - H; decompose_ex H
         end.

(*
This tactic expects is a hypothesis of the form
  H : sop_diverges' _ _ _
where the thing that is claimed to diverge is a (br or br_uncond) terminator.  It will replace this
hypothesis with another hypothesis that asserts sop_diverges' from the start of the next basic
block; if the terminator was a br_uncond, then there will be two goals, one for each possible next
basic block.
*)
Ltac terminator_does_not_diverge :=
  match goal with
    | [ H : sop_diverges' _ _ _ |- _ ] =>
      first [ apply br_diverges in H; let c := fresh in destruct H as [c ?]; destruct c |
              apply br_uncond_diverges in H ];
        clear - H; decompose_ex H; decompose [and] H; clear H;
        simplify_br_uncond
  end.

Lemma any_insn_diverges :
  forall cfg F B c cs tmn EC lc als Mem tr,
    ~(exists rid noret ca rt1 va1 fv lp, eq c (insn_call rid noret ca rt1 va1 fv lp)) ->
    sop_diverges' cfg (mkState ((@mkEC GVsSig F B (c::cs) tmn lc als)::EC) Mem) tr ->
    exists lc' als' Mem' tr',
      sop_diverges' cfg (mkState ((@mkEC GVsSig F B cs tmn lc' als')::EC) Mem') tr'.
Proof.
  intros;
  match goal with
    | [ H : sop_diverges' _ _ _ |- _ ] => inversion H; subst; clear H
  end;
  match goal with
    | [ H : sInsn _ _ _ _ |- _ ] => inversion H; subst; clear H
  end;
  try (eexists;
       eexists;
       eexists;
       eexists;
       eassumption);
  contradiction H;
  repeat eexists.
Qed.

(*
This tactic will prove any goal if there is a hypothesis of the form
  H : sop_diverges' _ _ _
where the thing that is claimed to diverge is a single basic block terminated by a return statement.

If the basic block is not terminated by a return statement, then the resulting goal will be that
the program continuing from the terminator diverges.

This is equivalent to but slightly slower than the above, but works for all non-call instructions
without needing individual proofs for each instruction.

This tactic is not currently used.
*)
Ltac single_basic_block_does_not_diverge' :=
  repeat match goal with
           | [ H : sop_diverges' _ _ _ |- _ ] =>
             apply any_insn_diverges in H; [
                 clear - H; decompose_ex H |
                 let H := fresh in intro H; decompose_ex H; discriminate ]
         end;
  match goal with
    | [ H : sop_diverges' _ _ _ |- _ ] => inversion H; clear H; subst
  end;
  match goal with
    | [ H : sInsn _ _ _ _ |- _ ] => inversion H; clear H; subst
  end.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "." "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
