(******************************************************************************)
(* Tactics for avoiding inversion when "executing" an LLVM IR program.        *)
(******************************************************************************)

Require opsem.
Import opsem.Opsem.
Require Import Coq.ZArith.Zdiv.
Require Import Tvc.base_tactics.
Require Import Tvc.notation.

(* This lemma is to be used instead of inversion on a hypothesis of the form s_converges. *)
Lemma invert_converges :
  forall s main args x0 x,
    @s_converges GVsSig s main args x0 x ->
    exists cfg IS FS,
      s_genInitState s main args Memory.Mem.empty = Some (cfg, IS) /\
      sop_star cfg IS FS x0 /\
      s_isFinialState cfg FS = Some x.
Proof.
  intros.
  inversion H.
  repeat eexists; eassumption.
Qed.

(* The following lemmas are to be used instead of inversion on a pair of hypothesis of the form
sop_star and s_isFinialState; there is a different lemma to be used depending on the next
instruction. *)
Ltac solve_converges :=
  intros;
  match goal with
      [ H1 : eq (s_isFinialState _ _) _,
        H2 : sop_star _ _ _ _ |- _ ] => inversion H2; clear H2; subst; inversion H1
  end;
  match goal with
      [ H : sInsn _ _ _ _ |- _ ] => inversion H1
  end;
  subst;
  repeat eexists;
  eauto.

Lemma alloca_converges :
  forall S TD Ps F B lc gl fs id t v align EC cs tmn Mem als FS tr x,
    s_isFinialState (mkCfg S TD Ps gl fs) FS = Some x ->
    sop_star (mkCfg S TD Ps gl fs)
             (mkState ((mkEC F B ((insn_alloca id t v align)::cs) tmn lc als)::EC) Mem)
             FS tr ->
    exists gns gn Mem' tsz mb tr2,
      getTypeAllocSize TD t = Some tsz /\
      getOperandValue TD v lc gl = Some gns /\
      gn @ gns /\
      genericvalues.LLVMgv.malloc TD Mem tsz gn align = Some (Mem', mb) /\
      sop_star (mkCfg S TD Ps gl fs)
               (mkState ((mkEC F B cs tmn
                               (alist.updateAddAL _ lc id ($ (blk2GV TD mb) # (typ_pointer t) $))
                               (mb::als))::EC) Mem')
               FS tr2.
Proof.
  solve_converges.
Qed.

Lemma load_converges :
  forall S TD Ps F B lc gl fs id t align v EC cs tmn Mem als FS tr x,
    s_isFinialState (mkCfg S TD Ps gl fs) FS = Some x ->
    sop_star (mkCfg S TD Ps gl fs)
             (mkState ((mkEC F B ((insn_load id t v align)::cs) tmn lc als)::EC) Mem)
             FS tr ->
    exists mps mp gv tr2,
      getOperandValue TD v lc gl = Some mps /\
      mp @ mps /\
      mload TD Mem mp t align = Some gv /\
      sop_star (mkCfg S TD Ps gl fs) 
               (mkState ((mkEC F B cs tmn (alist.updateAddAL _ lc id ($ gv # t $)) als)::EC) Mem)
               FS tr2.
Proof.
  solve_converges.
Qed.

Lemma store_converges :
  forall S TD Ps F B lc gl fs sid t align v1 v2 EC cs tmn Mem als FS tr x,
    s_isFinialState (mkCfg S TD Ps gl fs) FS = Some x ->
    sop_star (mkCfg S TD Ps gl fs)
             (mkState ((mkEC F B ((insn_store sid t v1 v2 align)::cs) tmn lc als)::EC) Mem)
             FS tr ->
    exists mp2 gv1 Mem' gvs1 mps2 tr2,
      getOperandValue TD v1 lc gl = Some gvs1 /\
      getOperandValue TD v2 lc gl = Some mps2 /\
      gv1 @ gvs1 /\
      mp2 @ mps2 /\
      mstore TD Mem mp2 t gv1 align = Some Mem' /\
      sop_star (mkCfg S TD Ps gl fs)
               (mkState ((mkEC F B cs tmn lc als)::EC) Mem')
               FS tr2.
Proof.
  solve_converges.
Qed.

Lemma bop_converges :
  forall S TD Ps F B lc gl fs id bop sz v1 v2 EC cs tmn Mem als FS tr x,
    @s_isFinialState GVsSig (mkCfg S TD Ps gl fs) FS = Some x ->
    sop_star (mkCfg S TD Ps gl fs)
             (mkState ((mkEC F B ((insn_bop id bop sz v1 v2)::cs) tmn lc als)::EC) Mem)
             FS tr ->
    exists gvs3 tr2,
      BOP TD lc gl bop sz v1 v2 = Some gvs3 /\
      sop_star (mkCfg S TD Ps gl fs)
               (mkState ((mkEC F B cs tmn (alist.updateAddAL _ lc id gvs3) als)::EC) Mem)
               FS tr2.
Proof.
  solve_converges.
Qed.

Lemma trunc_converges :
  forall S TD Ps F B lc gl fs id truncop t1 v1 t2 EC cs tmn Mem als FS tr x,
    @s_isFinialState GVsSig (mkCfg S TD Ps gl fs) FS = Some x ->
    sop_star (mkCfg S TD Ps gl fs)
             (mkState ((mkEC F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc als)::EC) Mem)
             FS tr ->
    exists gvs2 tr2,
      TRUNC TD lc gl truncop t1 v1 t2 = Some gvs2 /\
      sop_star (mkCfg S TD Ps gl fs)
               (mkState ((mkEC F B cs tmn (alist.updateAddAL _ lc id gvs2) als)::EC) Mem)
               FS tr2.
Proof.
  solve_converges.
Qed.

Lemma ext_converges :
  forall S TD Ps F B lc gl fs id extop t1 v1 t2 EC cs tmn Mem als FS tr x,
    @s_isFinialState GVsSig (mkCfg S TD Ps gl fs) FS = Some x ->
    sop_star (mkCfg S TD Ps gl fs)
             (mkState ((mkEC F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc als)::EC) Mem)
             FS tr ->
    exists gvs2 tr2,
      EXT TD lc gl extop t1 v1 t2 = Some gvs2 /\
      sop_star (mkCfg S TD Ps gl fs)
               (mkState ((mkEC F B cs tmn (alist.updateAddAL _ lc id gvs2) als)::EC) Mem)
               FS tr2.
Proof.
  solve_converges.
Qed.

Lemma icmp_converges :
  forall S TD Ps F B lc gl fs id cond t v1 v2 EC cs tmn Mem als FS tr x,
    @s_isFinialState GVsSig (mkCfg S TD Ps gl fs) FS = Some x ->
    sop_star (mkCfg S TD Ps gl fs)
             (mkState ((mkEC F B ((insn_icmp id cond t v1 v2)::cs) tmn lc als)::EC) Mem)
             FS tr ->
    exists gvs3 tr2,
      ICMP TD lc gl cond t v1 v2 = Some gvs3 /\
      sop_star (mkCfg S TD Ps gl fs)
               (mkState ((mkEC F B cs tmn (alist.updateAddAL _ lc id gvs3) als)::EC) Mem)
               FS tr2.
Proof.
  solve_converges.
Qed.

Lemma select_converges :
  forall S TD Ps F B lc gl fs id v0 t v1 v2 EC cs tmn Mem als FS tr x,
    @s_isFinialState GVsSig (mkCfg S TD Ps gl fs) FS = Some x ->
    sop_star (mkCfg S TD Ps gl fs)
             (mkState ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc als)::EC) Mem)
             FS tr ->
    exists cond gvs1 gvs2 c tr2,
      getOperandValue TD v0 lc gl = Some cond /\
      getOperandValue TD v1 lc gl = Some gvs1 /\
      getOperandValue TD v2 lc gl = Some gvs2 /\
      c @ cond /\
      sop_star (mkCfg S TD Ps gl fs)
               (mkState ((mkEC F B cs tmn (if isGVZero TD c
                                           then alist.updateAddAL _ lc id gvs2
                                           else alist.updateAddAL _ lc id gvs1) als)::EC) Mem)
               FS tr2.
Proof.
  solve_converges.
Qed.

Lemma br_uncond_converges :
  forall S TD Ps F B lc gl fs bid l EC Mem als FS tr x,
    @s_isFinialState GVsSig (mkCfg S TD Ps gl fs) FS = Some x ->
    sop_star (mkCfg S TD Ps gl fs)
             (mkState ((mkEC F B nil (insn_br_uncond bid l) lc als)::EC) Mem)
             FS tr ->
    exists ps' cs' tmn' lc' tr2,
      Some (stmts_intro ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) /\
      switchToNewBasicBlock TD (l, stmts_intro ps' cs' tmn') B gl lc = Some lc' /\
      sop_star (mkCfg S TD Ps gl fs)
               (mkState ((mkEC F (l, stmts_intro ps' cs' tmn') cs' tmn' lc' als)::EC) Mem)
               FS tr2.
Proof.
  solve_converges.
Qed.

Lemma br_converges :
  forall S TD Ps F B lc gl fs bid Cond l1 l2 EC Mem als FS tr x,
    @s_isFinialState GVsSig (mkCfg S TD Ps gl fs) FS = Some x ->
    sop_star (mkCfg S TD Ps gl fs)
             (mkState ((mkEC F B nil (insn_br bid Cond l1 l2) lc als)::EC) Mem)
             FS tr ->
    exists c conds ps' cs' tmn' lc' tr2,
      getOperandValue TD Cond lc gl = Some conds /\
      c @ conds /\
      Some (stmts_intro ps' cs' tmn') = (if isGVZero TD c
                                         then lookupBlockViaLabelFromFdef F l2
                                         else lookupBlockViaLabelFromFdef F l1) /\
      switchToNewBasicBlock TD (if isGVZero TD c then l2 else l1, stmts_intro ps' cs' tmn') B gl lc = Some lc' /\
      sop_star (mkCfg S TD Ps gl fs)
               (mkState ((mkEC F (if isGVZero TD c then l2 else l1, stmts_intro ps' cs' tmn') cs' tmn' lc' als)::EC) Mem)
               FS tr2.
Proof.
  solve_converges.
Qed.

Ltac do_insn tac :=
  match goal with
    | [ H1 : sop_star _ _ _ ?tr,
        H2 : eq (s_isFinialState _ _) _ |- _ ] =>
      eapply tac in H1; [ | apply H2 ];
      clear tr;
      decompose_ex H1; try (progress (decompose [and] H1); clear H1) (* only clear if the decompose did something *)
  end.

Ltac do_alloca := do_insn alloca_converges.
Ltac do_load := do_insn load_converges.
Ltac do_store := do_insn store_converges.
Ltac do_bop := do_insn bop_converges.
Ltac do_trunc := do_insn trunc_converges.
Ltac do_ext := do_insn ext_converges.
Ltac do_icmp := do_insn icmp_converges.
Ltac do_select := do_insn select_converges.
Ltac do_br_uncond := do_insn br_uncond_converges.
Ltac do_br := do_insn br_converges.

Lemma return_converges :
  forall S TD Ps F B rid RetTy Result lc gl fs Mem als FS tr x,
  @s_isFinialState GVsSig (mkCfg S TD Ps gl fs) FS = Some x ->
  sop_star (mkCfg S TD Ps gl fs)
           (mkState ((mkEC F B [] (insn_return rid RetTy Result) lc als)::[]) Mem)
           FS tr ->
  @s_isFinialState GVsSig (mkCfg S TD Ps gl fs) (mkState ((mkEC F B [] (insn_return rid RetTy Result) lc als)::[]) Mem) = Some x.
Proof.
  intros.
  inversion H0; clear H0; subst.
  assumption.
  inversion H1.
Qed.

Ltac do_ret :=
  match goal with
    | [ H1 : sop_star _ _ _ _,
        H2 : eq (s_isFinialState _ _) _ |- _ ] =>
      eapply return_converges in H1; [ | apply H2 ];
      inversion H1; clear H1; subst
  end.

(*
This tactic takes a goal equating two terms involving values of type Integers.Int.int, and uses
proof irrelevance to equate the proof terms.
*)
Ltac intrange_proof_irr :=
  let r1 := fresh "intrange" in
  let r2 := fresh "intrange" in
  remember (Z_mod_lt _ _ _) as r1 in |- * at 1;
  remember (Z_mod_lt _ _ _) as r2 in |- * at 1;
  replace r1 with r2 by (apply Axioms.proof_irr);
  subst r2;
  clear dependent r1.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "." "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
