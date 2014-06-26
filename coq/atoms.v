(******************************************************************************)
(* The definition of an infinite stream of atoms, all distinct from one       *)
(* another, and some of its properties.                                       *)
(******************************************************************************)

Require Import Coq.Lists.Streams.
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.Numbers.BinNums.
Require Import MetatheoryAtom.
Require CoqEqDec.

(* An infinite stream of atoms, all distinct from one another. *)
CoFixpoint mkatoms (xs : list atom) : Stream {x : (atom * list atom) | ~ List.In (fst x) (snd x)} :=
  let f := atom_fresh_for_list xs in
  let x := projT1 f in
  let p := projT2 f in
  let xs' := x :: xs in
  Cons (exist _ (x, xs) p) (mkatoms xs').

Definition atoms : Stream {x : (atom * list atom) | ~ List.In (fst x) (snd x)} := mkatoms [].
Definition ax' i : atom := fst (projT1 (Str_nth i atoms)).
Definition ax i : atom := ax' (nat_of_N i).

Lemma all_are_mkatoms :
  forall i,
    exists x,
      Str_nth_tl i atoms = mkatoms x.
Proof.
  intros.
  induction i.

  eexists.
  reflexivity.

  destruct IHi.
  eexists.
  change (S i) with (1 + i).
  rewrite <- Str_nth_tl_plus.
  rewrite H.
  reflexivity.
Qed.

Lemma head_to_tail :
  forall i x,
    Str_nth i atoms = x ->
    Str_nth_tl (S i) atoms = mkatoms (fst (projT1 x) :: snd (projT1 x)).
Proof.
  intros.

  unfold Str_nth in H.
  change (S i) with (1 + i).
  rewrite <- Str_nth_tl_plus.
  simpl.

  destruct (all_are_mkatoms i).
  rewrite H0 in H.
  rewrite H0.
  clear H0.

  simpl in H.
  subst.
  reflexivity.
Qed.

Lemma xxx' :
  forall i j,
    In (ax' i) (snd (projT1 (Str_nth (1 + i + j) atoms))).
Proof.
  induction j;
  simpl in *; rewrite Plus.plus_comm in *; simpl in *.

  (* Case j = 0 *)
  unfold ax'.
  remember (Str_nth i atoms) as x.
  destruct x as [[x xs] ?].
  symmetry in Heqx.
  apply head_to_tail in Heqx.
  unfold Str_nth.
  rewrite Heqx.
  left.
  reflexivity.

  (* Case j > 0 *)
  remember (Str_nth (S (j + i)) atoms) as x.
  destruct x as [[x xs] ?].
  symmetry in Heqx.
  apply head_to_tail in Heqx.
  unfold Str_nth.
  rewrite Heqx.
  right.
  assumption.
Qed.

Lemma i_lt_j :
  forall i j,
    i < j -> exists k, j = 1 + i + k.
Proof.
  intros.
  exists (j - (1 + i)).
  apply Minus.le_plus_minus.
  apply Lt.lt_le_S in H.
  assumption.
Qed.

Lemma xxx :
  forall i j,
    i < j -> In (ax' i) (snd (projT1 (Str_nth j atoms))).
Proof.
  intros i j H.
  apply i_lt_j in H.
  destruct H.
  rewrite H.
  apply xxx'.
Qed.

Lemma xxx2 :
  forall i j,
    i < j -> ax' i <> ax' j.
Proof.
  intros i j H Heq.
  apply xxx in H.
  remember (projT2 (Str_nth j atoms)) as H0 eqn:e; clear e; simpl in H0.
  rewrite Heq in H.
  contradiction.
Qed.

Lemma ax_i_eq_ax_j_iff_i_eq_j :
  forall i j,
    (ax' i = ax' j) <-> i = j.
Proof.
  intros.
  split.

  (* <- case *)
  Focus 2.
  intro.
  subst.
  reflexivity.

  (* -> case *)
  intro.
  destruct (Compare_dec.lt_eq_lt_dec i j) as [[? | ?] | ?].

  (* i < j *)
  exfalso.
  eapply xxx2; eassumption.
  
  (* i = j *)
  assumption.

  (* i > j *)
  exfalso.
  eapply xxx2; (try symmetry; eassumption).
Qed.

Lemma rewrite_eq_dec_equal :
  forall (A : Type) (a : atom) (x y : A),
    (if CoqEqDec.eq_dec a a then x else y) = x.
Proof.
  intros.
  destruct CoqEqDec.eq_dec.

  reflexivity.

  contradict n.
  reflexivity.
Qed.

Lemma rewrite_eq_dec_not_equal :
  forall (A : Type) i j (x y : A),
    N.eqb i j = false ->
    (if CoqEqDec.eq_dec (ax i) (ax j) then x else y) = y.
Proof.
  intros.
  destruct CoqEqDec.eq_dec.

  apply ax_i_eq_ax_j_iff_i_eq_j in e.
  apply Nnat.N2Nat.inj in e.
  subst j.
  rewrite N.eqb_refl in H.
  discriminate.

  reflexivity.
Qed.

Hint Rewrite rewrite_eq_dec_equal : eq_dec_db.
Hint Rewrite rewrite_eq_dec_not_equal using reflexivity : eq_dec_db.

Global Opaque ax.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "../coq" "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
