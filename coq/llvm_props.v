(******************************************************************************)
(* Properties of the LLVM IR semantics.                                       *)
(******************************************************************************)

Require ndopsem.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zdiv.
Require Import Tvc.base_tactics.

Lemma repr_unsigned_inverse :
  forall (w : nat) (n : Integers.Int.int w), eq n (Integers.Int.repr w (Integers.Int.unsigned w n)).
Proof.
  intros.
  unfold Integers.Int.repr, Integers.Int.unsigned.
  destruct n.
  simpl.

  pose proof intrange as H2.
  pose proof (Zmod_small intval (Integers.Int.modulus w)) as H4.
  apply H4 in H2.
  clear H4.

  remember (Z_mod_lt intval (Integers.Int.modulus w) (Integers.Int.modulus_pos w)) as intrange2.
  clear Heqintrange2.

  remember ((intval mod (Integers.Int.modulus w))%Z) as intval2.
  clear Heqintval2.

  destruct H2.
  replace intrange with intrange2 by (apply Axioms.proof_irr).
  reflexivity.
Qed.

Lemma unsigned_repr_inverse :
  forall (w : nat) (z : Z), eq (z mod Integers.Int.modulus w)%Z (Integers.Int.unsigned w (Integers.Int.repr w z)).
Proof.
  reflexivity.
Qed.

Lemma repr_signed_inverse :
  forall (w : nat) (n : Integers.Int.int w), eq n (Integers.Int.repr w (Integers.Int.signed w n)).
Proof.
  intros.
  unfold Integers.Int.repr, Integers.Int.signed.
  destruct n.
  simpl.

  destruct (Coqlib.zlt intval (Integers.Int.half_modulus w)).

  (* case 1: intval < half_modulus *)
  pose proof intrange as H2.
  pose proof (Zmod_small intval (Integers.Int.modulus w)) as H4.
  apply H4 in H2.
  clear H4.

  remember (Z_mod_lt intval (Integers.Int.modulus w) (Integers.Int.modulus_pos w)) as intrange2.
  clear Heqintrange2.

  remember ((intval mod (Integers.Int.modulus w))%Z) as intval2.
  clear Heqintval2.

  destruct H2.
  replace intrange with intrange2 by (apply Axioms.proof_irr).
  reflexivity.

  (* case 2: intval >= half_modulus *)
  assert (eq ((intval - Integers.Int.modulus w) mod (Integers.Int.modulus w))%Z intval) as H2.
  rewrite Zminus_mod.
  rewrite Z_mod_same; [ | omega ].
  rewrite Zminus_0_r.
  rewrite Zmod_mod.
  pose proof intrange as H2.
  pose proof (Zmod_small intval (Integers.Int.modulus w)) as H4.
  apply H4 in H2.
  assumption.

  remember (Z_mod_lt (intval - Integers.Int.modulus w) (Integers.Int.modulus w) (Integers.Int.modulus_pos w)) as intrange2.
  clear Heqintrange2.

  remember (((intval - Integers.Int.modulus w) mod (Integers.Int.modulus w))%Z) as intval2.
  clear Heqintval2.

  destruct H2.
  replace intrange with intrange2 by (apply Axioms.proof_irr).
  reflexivity.
Qed.

Lemma ltb_false_geb_true n m : (n <? m)%Z = false <-> (n >=? m)%Z = true.
Proof.
  unfold Z.ltb, Z.geb.
  split; intro; destruct (n ?= m)%Z eqn:?; auto.
Qed.

Lemma leb_false_gtb_true n m : (n <=? m)%Z = false <-> (n >? m)%Z = true.
Proof.
  unfold Z.leb, Z.gtb.
  split; intro; destruct (n ?= m)%Z eqn:?; auto.
Qed.

Lemma technical_1 :
  forall z m : Z,
    (m > 0)%Z ->
    (- (m / 2) <= z)%Z ->
    (z < 0)%Z ->
    eq (z mod m)%Z (z + m)%Z.
Proof.
  intros.

  rewrite Zmod_eq; [ | omega ].
  apply Zplus_eq_compat; [ reflexivity | ].

  assert (eq (z / m) (-1))%Z as H'.

  assert (eq ((z + m) / m) 0)%Z.
  apply Z.div_small.
  split.

  rewrite Z.add_comm.
  apply (Zplus_le_compat_l (-(m/2)) z m) in H0.
  rewrite Z.add_opp_r in H0.
  assert (m - m/2 >= 0)%Z.

  apply Z.le_ge.
  apply (Zplus_le_reg_l _ _ (m/2)).
  rewrite Z.add_0_r.
  rewrite Zplus_minus.

  assert (0 <= m)%Z as H2 by omega.
  assert (0 < 1 < 2)%Z as H3 by omega.
  pose proof (Zdiv_le_compat_l _ _ _ H2 H3) as H4.
  rewrite Z.div_1_r in H4.
  assumption.

  omega.

  omega.

  rewrite <- (Z.mul_1_l m) in H2 at 1.
  rewrite (Z.div_add z 1%Z m) in H2.
  omega.
  omega.

  rewrite H'.
  rewrite Z.mul_comm.
  rewrite <- Z.opp_eq_mul_m1.
  rewrite Z.opp_involutive.
  reflexivity.
Qed.

Lemma technical_2 :
  forall z m : Z,
  (- (m / 2) <= z)%Z ->
  (z + m >= m / 2)%Z.
Proof.
  intros.

  apply Z.le_ge.

  pose proof (Z.add_le_mono_r (-(m/2))%Z z m) as H0.
  apply H0 in H.
  clear H0.

  pose proof (Z.add_opp_l m (m/2)%Z) as H0.
  rewrite H0 in H.
  clear H0.

  assert ((m - (m / 2)) >= (m / 2))%Z.
  apply Z.le_ge.
  pose proof (Z.add_le_mono_r (m/2) (m - (m/2)) (m/2)) as H0.
  apply <- H0.
  clear H0.

  rewrite Z.sub_add.

  Lemma x_plus_x :
    forall x : Z, eq (x + x)%Z (2 * x)%Z.
  Proof.
    intro.
    omega.
  Qed.

  rewrite x_plus_x.
  rewrite (Z.mul_div_le m 2) by omega.
  omega.

  apply Z.ge_le in H0.
  apply (Z.le_trans _ _ _ H0 H).
Qed.

Lemma signed_repr_inverse :
  forall (w : nat) (z : Z), ((- Integers.Int.half_modulus w) <= z < (Integers.Int.half_modulus w))%Z -> eq z (Integers.Int.signed w (Integers.Int.repr w z)).
Proof.
  intros.
  unfold Integers.Int.repr, Integers.Int.signed, Integers.Int.half_modulus in *.
  simpl.
  pose proof (Integers.Int.modulus_pos w) as H99.
  remember (Integers.Int.modulus w) as m in *.
  decompose [and] H. clear H.
  destruct (Z.ltb z 0) eqn:Heqb.

  (* case 1: z < 0 *)
  clear H1.
  apply Z.ltb_lt in Heqb.
  assert (eq (z mod m)%Z (z + m)%Z) by (apply technical_1; assumption).
  rewrite H.
  assert ((z + m) >= (m / 2))%Z by (apply technical_2; assumption).
  destruct Coqlib.zlt.
  contradiction.
  omega.

  (* case 2: z >= 0 *)
  clear H0.
  apply ltb_false_geb_true in Heqb.
  apply Z.geb_le in Heqb.

  assert (Z.lt z m).
  assert (m / 2 < m)%Z by (apply Z_div_lt; omega).
  eauto using Z.lt_trans.

  pose proof (Zmod_small z m) as H4.
  pose proof (conj Heqb H) as H2.
  apply H4 in H2.
  rewrite H2.

  destruct Coqlib.zlt.
  trivial.
  contradiction.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "." "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
