(******************************************************************************)
(* Properties of the Core semantics.                                          *)
(******************************************************************************)

Require Import Csem.core.
Require Csem.core_aux.
Require Csem.core_run.
Require Import Csem.core_run_inductive.
Require Import Tvc.base_tactics.

Definition myexpr : Type := (core.expr (core_run_effect.taction_id1) * cmm_csem.tid0 * list (core_run.cont (core_run_effect.taction_id1)))%type.
Definition mystate : Type := core_run_effect.state.

Fixpoint red2n (n : nat) (e : myexpr) (s : mystate) : list (undefined.t4 myexpr * mystate) :=
  match n with
    | O => [(undefined.Defined0 e, s)]
    | S n => let results := core_run.red2 e s in
             let red2a (es : undefined.t4 myexpr * mystate) : list (undefined.t4 myexpr * mystate) :=
                 let (e, s) := es in
                 match e with
                   | undefined.Defined0 e => red2n n e s
                   | _ => [(e, s)]
                 end in
             flat_map red2a results
  end.

Fixpoint red2n' (n : nat) (e : myexpr) (s : mystate) : undefined.t4 myexpr * mystate :=
  match n with
    | O => (undefined.Defined0 e, s)
    | S n => let results := core_run.red2 e s in
             match results with
               | nil => (undefined.Error, s)
               | es::_ =>
                 let (e, s) := es in
                 match e with
                   | undefined.Defined0 e => red2n' n e s
                   | _ => (e, s)
                 end
             end
  end.

Definition red2nb (n : nat) (es : myexpr * mystate) :=
  let (e, s) := es in red2n n e s.

Definition red2nb' (n : nat) (es : myexpr * mystate) :=
  let (e, s) := es in red2n' n e s.

Lemma red2n_implies_star_red2_ind :
  forall n e s e2 s2,
    In (undefined.Defined0 e2, s2) (red2n n e s) ->
    core_run_inductive.star_red2_ind (e, s) (e2, s2).
Proof.
  induction n; intros; simpl in H.

  destruct H; try contradiction.
  injection H; intros; subst; clear H.
  auto using core_run_inductive.star_red2_zero.

  apply in_flat_map in H.
  destruct H.
  destruct x.
  decompose [and] H; clear H.
  destruct t; try ( destruct H1; [ discriminate | contradiction ] ).
  eauto using core_run_inductive.star_red2_step, core_run_inductive.red2_intro.
Qed.

Lemma red2n'_implies_star_red2_ind :
  forall n e s e2 s2,
    eq (undefined.Defined0 e2, s2) (red2n' n e s) ->
    core_run_inductive.star_red2_ind (e, s) (e2, s2).
Proof.
  induction n; intros; simpl in H.

  injection H; intros; subst; clear H.
  auto using core_run_inductive.star_red2_zero.

  destruct (core_run.red2 e s) eqn:H0; try discriminate.
  destruct p.
  destruct t; try discriminate.
  assert (In (undefined.Defined0 p, s0) (core_run.red2 e s)) by (rewrite H0; eapply in_eq); clear H0.
  eauto using core_run_inductive.star_red2_step, core_run_inductive.red2_intro.
Qed.

Lemma red2n_implies_star_red2_undef :
  forall n e s u s2,
    In (undefined.Undef u, s2) (red2n n e s) ->
    core_run_inductive.star_red2_undef_ind (e, s).
Proof.
  induction n; intros; simpl in H.

  destruct H; [ discriminate | contradiction ].

  apply in_flat_map in H.
  destruct H.
  destruct x.
  decompose [and] H; clear H.
  destruct t; try ( destruct H1; [ discriminate | contradiction ] ).
  eauto using core_run_inductive.star_red2_undef_step, core_run_inductive.red2_intro.
  eauto using core_run_inductive.star_red2_undef_one, core_run_inductive.red2_undef_intro.
Qed.

Lemma red2n'_implies_star_red2_undef :
  forall n e s u s2,
    eq (undefined.Undef u, s2) (red2n' n e s) ->
    core_run_inductive.star_red2_undef_ind (e, s).
Proof.
  induction n ; intros; simpl in H.

  discriminate.

  destruct (core_run.red2 e s) eqn:H0; try discriminate.
  destruct p.
  destruct t; try discriminate.
  assert (In (undefined.Defined0 p, s0) (core_run.red2 e s)) by (rewrite H0; eapply in_eq); clear H0.
  eauto using core_run_inductive.star_red2_undef_step, core_run_inductive.red2_intro.
  assert (In (undefined.Undef l0, s0) (core_run.red2 e s)) by (rewrite H0; eapply in_eq); clear H0.
  eauto using core_run_inductive.star_red2_undef_one, core_run_inductive.red2_undef_intro.
Qed.

Lemma red2n_implies_plus_red2_ind :
  forall n e s e2 s2,
    n > 0 ->
    In (undefined.Defined0 e2, s2) (red2n n e s) ->
    core_run_inductive.plus_red2_ind (e, s) (e2, s2).
Proof.
  induction n; intros; simpl in H0.

  omega.

  apply in_flat_map in H0.
  destruct H0.
  destruct x.
  decompose [and] H0; clear H0.
  destruct t; try ( destruct H2; [ discriminate | contradiction ] ).

  destruct n.

  destruct H2; try contradiction.
  injection H0; intros; subst; clear H0.
  auto using core_run_inductive.plus_red2_one, core_run_inductive.red2_intro.

  assert (S n > 0) by omega.
  eauto using core_run_inductive.plus_red2_step, core_run_inductive.red2_intro.
Qed.

Lemma plus_red2_diverges_implies_star_red2_diverges :
  forall e s,
    core_run_inductive.plus_red2_diverges (e, s) -> core_run_inductive.star_red2_diverges (e, s).
Proof.
  cofix.
  intros e s H.
  destruct H.
  destruct H.

  eauto using core_run_inductive.star_red2_diverges_intro.
  eauto using core_run_inductive.star_red2_diverges_intro, core_run_inductive.plus_red2_diverges_intro.
Qed.

(* The next lemma is true but not useful *)
Lemma red2n_implies_star_red2_diverges :
  forall n e s e2 s2,
    In (undefined.Defined0 e2, s2) (red2n n e s) ->
    core_run_inductive.star_red2_diverges (e2, s2) ->
    core_run_inductive.star_red2_diverges (e, s).
Proof.
  induction n; intros; simpl in H.

  destruct H; try contradiction.
  injection H; intros; subst; clear H.
  auto.

  apply in_flat_map in H.
  destruct H.
  destruct x.
  decompose [and] H; clear H.
  destruct t; try ( destruct H2; [ discriminate | contradiction ] ).
  eauto using core_run_inductive.star_red2_diverges_intro, core_run_inductive.red2_intro.
Qed.

Lemma star_red2_ind_trans :
  forall e1 s1 e2 s2 e3 s3,
    core_run_inductive.star_red2_ind (e1, s1) (e2, s2) ->
    core_run_inductive.star_red2_ind (e2, s2) (e3, s3) ->
    core_run_inductive.star_red2_ind (e1, s1) (e3, s3).
Proof.
  intros.
  generalize dependent s3.
  induction H; intros; eauto using core_run_inductive.star_red2_step.
Qed.

Lemma red2_pure_works :
  forall e (tid : cmm_aux.tid) T (ks : T) s,
    eq (is_pure e) true ->
    exists etks',
      eq (red2_pure (e, tid, ks) s) [etks'].
Proof.
  intros.
  destruct (eval1 (e.file s) e) eqn:?;
  eexists;
  unfold red2_pure;
  rewrite H;
  unfold return3, bind3, get_file, runU, e.u.return3;
  compute [List.map];
  change taction_id1 with nat in Heqt;
  rewrite Heqt;
  reflexivity.
Qed.

Lemma red2_is_red2_pure :
  forall e tid ks s,
    eq (is_pure e) true ->
    eq (is_value0 e) false ->
    eq (red2 (e, tid, ks) s) (red2_pure (e, tid, ks) s).
Proof.
  intros.

  unfold red2, red2_value, dmsum, mzero.
  rewrite H0.

  edestruct (red2_pure_works e) as [? H1]; try assumption.
  rewrite H1.

  destruct ks; [ reflexivity | destruct c; reflexivity ].
Qed.

Definition addTidKs (tid : cmm_aux.tid) (ks : list (cont e.taction_id1)) (r : u.t4 (expr nat)) :=
  match r with
    | Defined0 e => Defined0 (e, tid, ks)
    | Undef u => Undef u
    | Error => Error
  end.

Lemma red2_pure_is_eval :
  forall e tid ks s,
    eq (is_pure e) true ->
    eq (red2_pure (e, tid, ks) s) [(addTidKs tid ks (eval1 (e.file s) e), s)].
Proof.
  intros.

  unfold red2_pure.
  rewrite H.
  unfold bind3, get_file, runU, return5, addTidKs.
  simpl.

  destruct (eval1 (e.file s) e) eqn:?;
  change taction_id1 with nat in Heqt;
  rewrite Heqt;
  reflexivity.
Qed.

(*
Lemma red2_ind_is_eval :
  forall e1 e2 tid ks s,
    eq (is_pure e1) true ->
    eq (is_value0 e1) false ->
    red2_ind ((e1, tid, ks), s) ((e2, tid, ks), s) ->
    (eval1 (e.file s) e1) = Defined0 e2.
Proof.
  intros.
  inversion H1; subst; clear H1.
  rewrite red2_is_red2_pure in H3; try assumption.
  rewrite red2_pure_is_eval in H3; try assumption.
  remember (eval1 (e.file s) e1) as r.
  unfold addTidKs in H3.
  compute in H3.
  destruct H3; try contradiction.
  injection H1; intros; clear H1.
  destruct r; try discriminate.
  injection H2; intros; clear H2.
  subst.
  reflexivity.
Qed.
*)

Lemma eval_value_is_identity :
  forall T (e : expr T) f,
    is_value0 e = true -> eq (eval1 f e) (Defined0 e).
Proof.
  intros.
  destruct e; (unfold eval1; rewrite H; reflexivity) || (simpl in H; discriminate H).
Qed.

Lemma red2_ind_is_eval' :
  forall e1 e2 tid ks s,
    eq (is_pure e1) true ->
    red2_ind ((e1, tid, ks), s) ((e2, tid, ks), s) ->
    (eval1 (e.file s) e1) = Defined0 e2.
Proof.
  intros.
  inversion H0; subst; clear H0.

  destruct (is_value0 e1) eqn:?.

  Focus 2.
  rewrite red2_is_red2_pure in H2; try assumption.
  rewrite red2_pure_is_eval in H2; try assumption.
  remember (eval1 (e.file s) e1) as r.
  unfold addTidKs in H2.
  compute in H2.
  destruct H2; try contradiction.
  injection H0; intros; clear H0.
  destruct r; try discriminate.
  injection H1; intros; clear H1.
  subst.
  reflexivity.

  unfold red2 in H2.
  unfold dmsum, mzero, red2_value in H2.
  change taction_id1 with nat in Heqb.
  rewrite Heqb in H2.

  destruct ks.
  Focus 2.
  destruct c.
  unfold bind3, return3, return5 in H2.
  compute [List.map] in H2.
  unfold return3 in H2.
  compute [apply concat] in H2.
  compute in H2.
  destruct H2; try contradiction.
  injection H0; clear H0; intros.
  subst e2.

  rewrite eval_value_is_identity.
  reflexivity.
  assumption.

  unfold bind3, return3, return5 in H2.
  compute [List.map] in H2.
  unfold return3 in H2.
  compute [apply concat] in H2.
  compute in H2.
  destruct H2; try contradiction.
  discriminate H0.

  unfold mzero in H2.

  rewrite red2_pure_is_eval in H2; try assumption.
  remember (eval1 (e.file s) e1) as r.
  unfold addTidKs in H2.
  compute in H2.
  destruct H2; try contradiction.
  injection H0; intros; clear H0.
  destruct r; try discriminate.
  injection H1; intros; clear H1.
  subst.
  reflexivity.
Qed.

Lemma red2_ind_no_ks_is_eval :
  forall e1 x tid s s2,
    eq (is_pure e1) true ->
    red2_ind ((e1, tid, []), s) (x, s2) ->
    ((eq s s2) /\
     (exists e2, eq x (e2, tid, []) /\
                 (eval1 (e.file s) e1) = Defined0 e2)).
Proof.
  intros.
  inversion H0; subst; clear H0.

  destruct (is_value0 e1) eqn:?.

  Focus 2.
  rewrite red2_is_red2_pure in H2; try assumption.
  rewrite red2_pure_is_eval in H2; try assumption.
  remember (eval1 (e.file s) e1) as r.
  unfold addTidKs in H2.
  compute in H2.
  destruct H2; try contradiction.
  injection H0; intros; clear H0.
  destruct r; try discriminate.
  subst.
  injection H2; intros; clear H2.
  subst.
  split; try reflexivity.
  exists e.
  split; reflexivity.

  unfold red2 in H2.
  unfold dmsum, mzero, red2_value in H2.
  rewrite red2_pure_is_eval in H2; try assumption.

  remember (eval1 (e.file s) e1) as r.
  unfold addTidKs in H2.
  compute in H2.
  destruct H2; try contradiction.
  injection H0; intros; clear H0.
  destruct r; try discriminate.
  subst.
  injection H2; intros; clear H2.
  subst.
  split; try reflexivity.
  exists e.
  split; reflexivity.
Qed.

Lemma red_under_Eret :
  forall e1 e2 tid k ks s,
    eq (is_pure e1) true ->
    eq (is_value0 e1) false ->
    red2_ind ((e1, tid, []), s) ((e2, tid, []), s) ->
    red2_ind ((Eret e1, tid, k::ks), s) ((Eret e2, tid, k::ks), s).
Proof.
  intros.
  apply red2_ind_is_eval' in H1; try assumption.

  apply red2_intro.
  unfold red2, red2_ret, red2_pure, red2_value, dmsum, mzero, bind3, get_file.
  destruct (is_pure (Eret _)) eqn:?; try discriminate.
  simpl.
  unfold mplus, mzero.
  change taction_id1 with nat in H0.
  rewrite H0.
  change taction_id1 with nat in H1.
  rewrite H1.

  destruct k; left; reflexivity.
Qed.

Definition add_eret (ks : list (cont e.taction_id1)) (x : ((((expr (core_run_effect.taction_id1)*cmm_csem.tid0*list (cont (core_run_effect.taction_id1))) % type)*core_run_effect.state) % type)) :=
  match x with
    | ((e, tid, _), s) => ((Eret e, tid, ks), s)
  end.

Lemma value_is_pure :
  forall T (e : expr T),
    eq (is_value0 e) true -> eq (is_pure e) true.
Proof.
  intros.
  destruct e; (reflexivity || discriminate).
Qed.

Lemma star_red2_value_is_identity :
  forall x y,
    star_red2_ind x y ->
    (forall e1 e2 tid s,
       (eq x ((e1, tid, []), s)) ->
       (eq y ((e2, tid, []), s)) ->
       eq (is_value0 e1) true ->
       eq e1 e2).
Proof.
  intros x y H.
  induction H.

  intros.
  congruence.

  intros.
  injection H1; clear H1; intros; subst.
  apply red2_ind_no_ks_is_eval in H.
  Focus 2.
  apply value_is_pure.
  assumption.

  decompose [and] H; clear H; subst.
  decompose_ex H4.
  decompose [and] H4; clear H4; subst.
  injection H2; clear H2; intros; subst.

  rewrite eval_value_is_identity in H1; try assumption.
  injection H1; clear H1; intro; subst.
  eauto.
Qed.

Axiom daemon_is_error :
  forall (x : string) (y : string) T,
    eq ((DAEMON x y) : t4 T) Error.

Axiom daemon_is_Eerror :
  forall (x : string) (y : string) T,
    eq ((DAEMON x y) : expr T) Eerror.

Axiom t4_default_is_error :
  forall T,
    eq (@t4_default T) Error.

(*
Goal forall T f (x y : expr T),
       eq (eval1 f x) (Defined0 (Econst (Cint 1))) ->
       eq (eval1 f y) (Defined0 (Econst (Cint 2))) ->
       eq (eval1 f (Eop OpAdd x y)) (Defined0 (Econst (Cint 3))).
Proof.
  intros.
  unfold eval1.
  unfold bind2.
  unfold eval1 in H.
  rewrite H.
Qed.    
*)

Lemma red2_pure_is_pure :
  forall e1 e2 tid ks s,
    red2_ind ((e1, tid, ks), s) ((e2, tid, ks), s) ->
    eq (is_pure e1) true ->
    eq (is_pure e2) true.
Proof.
(*
  intros.

  apply red2_ind_is_eval' in H; try assumption.
  generalize dependent e2.

  induction e1; intros; try discriminate H0; try (simpl in H; injection H; clear H; intro; subst; reflexivity).

  compute [eval1 apply] in H.
  rewrite daemon_is_error in H.
  discriminate H.

  compute [eval1 apply] in H.
  rewrite daemon_is_error in H.
  rewrite t4_default_is_error in H.
  destruct (fmap_lookup_by implementation_constant_compare i (impl (e.file s))) eqn:?; try discriminate.
  destruct i0 eqn:?; try discriminate.
  injection H; clear H; intro; subst.
  admit. (* XXX need to assume that anything found in impl is pure! *)

  compute [eval1 apply] in H.
  rewrite daemon_is_error in H.
  destruct (is_value0 (Etuple l)); try discriminate.
  injection H; clear H; intro; subst.
  assumption.

  unfold eval1 in H.
  fold (eval1 (e.file s) e1) in H.
  remember (eval1 (e.file s) e1) as r.
  compute [apply] in H.
  rewrite daemon_is_error in H.
  unfold bind2 in H.
  destruct r; try discriminate.
  destruct (is_value0 e).
  destruct e; try discriminate; injection H; clear H; intro; subst; reflexivity.
  injection H; clear H; intro; subst; reflexivity.

  Print eval1.

  unfold eval1 in H.
  fold (@eval1 e.taction_id1 (e.file s) e1_1) in H.
  fold (@eval1 e.taction_id1 (e.file s) e1_2) in H.
  remember (eval1 (e.file s) e1_1) as r.
  remember (eval1 (e.file s) e1_2) as r2.
  clear Heqr.
  clear Heqr2.
  compute [bind2] in H.
  destruct r; try discriminate.
  destruct r2; try discriminate.
  compute [apply return3] in H.
  injection H; clear H; intro.
  subst.
  rewrite daemon_is_Eerror.
  destruct (is_value0 e && is_value0 e0)%bool.
  Focus 2.
  reflexivity.
  destruct b; try (destruct e; try reflexivity; try (destruct c; try reflexivity; try (destruct e0; try reflexivity))); try (destruct c; try reflexivity); try (destruct (_ =? _)%Z; try reflexivity); try (destruct (ctype_eq _ _); try reflexivity).
  destruct (int_ltb _ _); try reflexivity.
  destruct e0; try reflexivity.
  destruct e0; try reflexivity.

  admit. (* Ecall *)

  discriminate H. (* Eundef *)
  discriminate H. (* Eerror *)

  admit. (* Elet *)
  admit. (* Eif *)
  admit. (* Eunseq *)

  unfold eval1 in H.
  fold (@eval1 e.taction_id1 (e.file s) e1) in H.
  remember (eval1 (e.file s) e1) as r.
  clear Heqr.
  compute [bind2 apply append] in H.
  rewrite daemon_is_error in H.
  destruct r; try discriminate.
  destruct e; try (destruct (is_value0 _); [ try discriminate | injection H; clear H; intro; subst; reflexivity ]).
  try destruct (scalar _); injection H; clear H; intro; subst; reflexivity.

  unfold eval1 in H.
  fold (@eval1 e.taction_id1 (e.file s) e1) in H.
  remember (eval1 (e.file s) e1) as r.
  clear Heqr.
  compute [bind2 apply append] in H.
  rewrite daemon_is_error in H.
  destruct r; try discriminate.
  destruct e; try (destruct (is_value0 _); [ try discriminate | injection H; clear H; intro; subst; reflexivity ]).
  try destruct (integer _); injection H; clear H; intro; subst; reflexivity.

  unfold eval1 in H.
  fold (@eval1 e.taction_id1 (e.file s) e1) in H.
  remember (eval1 (e.file s) e1) as r.
  clear Heqr.
  compute [bind2 apply append] in H.
  rewrite daemon_is_error in H.
  destruct r; try discriminate.
  destruct e; try (destruct (is_value0 _); [ try discriminate | injection H; clear H; intro; subst; reflexivity ]).
  try destruct (is_signed_integer_type _); injection H; clear H; intro; subst; reflexivity.

  unfold eval1 in H.
  fold (@eval1 e.taction_id1 (e.file s) e1) in H.
  remember (eval1 (e.file s) e1) as r.
  clear Heqr.
  compute [bind2 apply append] in H.
  rewrite daemon_is_error in H.
  destruct r; try discriminate.
  destruct e; try (destruct (is_value0 _); [ try discriminate | injection H; clear H; intro; subst; reflexivity ]).
  try destruct (is_unsigned_integer_type _); injection H; clear H; intro; subst; reflexivity.
Qed.
*)
Admitted.

Lemma star_red_under_Eret'' :
  forall x y,
    star_red2_ind x y ->
    (exists e1 e2 tid s,
       eq x ((e1, tid, []), s) /\
       eq y ((e2, tid, []), s) /\
       eq (core_aux.is_pure e1) true) ->
    (forall k ks,
       star_red2_ind (add_eret (k::ks) x) (add_eret (k::ks) y)).
Proof.
  intros.
  induction H.
  unfold add_eret.
  decompose_ex H0.
  decompose [and] H0; clear H0; intros.
  injection H; clear H; intros; subst.
  apply star_red2_zero.

  unfold add_eret.
  decompose_ex H0.
  decompose [and] H0; clear H0; intros.
  injection H2; clear H2; intros; subst.
  injection H4; clear H4; intros; subst.

  destruct (is_value0 e0) eqn:?.
  Focus 2.

  assert ((exists z, eq e2 (z, tid, [])) /\ eq s s2).

  (* Proof of assertion *)
  inversion H; subst.
  rewrite red2_is_red2_pure in H2; try assumption.
  rewrite red2_pure_is_eval in H2; try assumption.
  unfold addTidKs in H2.
  unfold In in H2.
  destruct H2; try contradiction.
  injection H0; clear H0; intros; subst.
  split; try reflexivity.
  destruct (eval1 (e.file s2) e0) eqn:?; try discriminate.
  injection H2; clear H2; intros; subst.
  exists e.
  reflexivity.

  destruct H0; destruct H0; subst.

  eapply star_red2_step.

  clear H1.
  apply red_under_Eret; try assumption.
  eassumption.

  apply IHstar_red2_ind.
  exists x.
  exists e4.
  exists tid.
  exists s2.
  repeat split.

  eapply red2_pure_is_pure; eassumption.

  apply red2_ind_no_ks_is_eval in H; try assumption.
  decompose [and] H; clear H; subst.
  decompose_ex H2.
  decompose [and] H2; clear H2; subst.
  rewrite eval_value_is_identity in H0; try assumption.
  injection H0; clear H0; intro; subst.

  eapply star_red2_value_is_identity in H1; try reflexivity; try assumption.
  subst.
  apply star_red2_zero.
Qed.

(* Now phrase it in a more natural way *)
Lemma star_red_under_Eret :
  forall e1 e2 tid k ks s,
    eq (core_aux.is_pure e1) true ->
    eq (core_aux.is_value0 e1) false ->
    star_red2_ind ((e1, tid, []), s) ((e2, tid, []), s) ->
    star_red2_ind ((Eret e1, tid, k::ks), s) ((Eret e2, tid, k::ks), s).
Proof.
  intros.
  fold (add_eret (k :: ks) ((e1, tid, []), s)).
  fold (add_eret (k :: ks) ((e2, tid, []), s)).
  apply star_red_under_Eret''.
  assumption.
  repeat eexists; repeat split; eassumption.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "." "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
