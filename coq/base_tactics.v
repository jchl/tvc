(******************************************************************************)
(* Tactics that are independent of Core and LLVM IR.                          *)
(******************************************************************************)

(*
This tactic is just like 'decompose [ex] H; clear H', except the names that are introduced are
chosen based on the names of the bound variables (like 'intros' does), rather than just being x1,
x2, ....
*)
Ltac decompose_ex H :=
  repeat match type of H with
           | ex (fun x => _) =>
             let x := fresh x in
             destruct H as [x H]
         end.

Ltac head xs :=
  match xs with
    | ?h :: _ => h
  end.

Ltac tail xs :=
  match xs with
    | _ :: ?t => t
  end.

Inductive hidden (P : Prop) : Prop :=
  hidden_intro : P -> hidden P.

Lemma hidden_iff_visible :
  forall (P : Prop), hidden P <-> P.
Proof.
  intro P.
  split.

  intro H.
  destruct H.
  assumption.

  apply hidden_intro.
Qed.

Ltac hide H := apply <- hidden_iff_visible in H.
Ltac unhide H := apply -> hidden_iff_visible in H.

Lemma Some_injection : forall A (x y : A), Some x = Some y -> x = y.
  intros.
  injection H.
  trivial.
Qed.

(*
This tactic replaces all hypotheses of the form H : Some x = Some y with a hypothesis of the form H : x = y.
*)
Ltac injection_Some_eq_Some :=
  repeat match goal with
           | [ H : eq (Some _) (Some _) |- _ ] =>
             apply Some_injection in H (* 'injection' would split Some (x,y) = Some z into two hypotheses *)
         end.

Section Tests.
(* Some tests for injection_Some_eq_Some. *)

Goal forall A (x : A) (y : A), Some x = Some y -> x = y.
Proof.
  intros ? ? ? H.
  injection_Some_eq_Some.
  exact H.
Qed.

End Tests.

Lemma destruct_match_Some_simple :
  forall (A : Type) x (y : A),
    match x with
      | Some z => Some z
      | None => None
    end = Some y ->
    x = Some y.
Proof.
  intros A x y H.
  destruct x; auto.
Qed.

Lemma destruct_match_Some_general :
  forall (A B : Type) (x : option A) (y : B) f,
    match x with
      | Some z => Some (f z)
      | None => None
    end = Some y ->
    exists z, eq x (Some z) /\ eq y (f z).
Proof.
  intros A B x y f H.
  destruct x eqn:?; [ | discriminate ].
  eexists.
  split.
  reflexivity.
  injection H.
  intro.
  congruence.
Qed.

Ltac destruct_match_Some :=
  let x := fresh "x" in
  let H0 := fresh in
  let H1 := fresh in
  match goal with
      [ H : eq _ (Some ?y) |- _ ] =>
      apply destruct_match_Some_general in H;
      destruct H as [x [H0 H1]];
      rename H0 into H;
      subst y
  end.

(*
This tactic proves a goal of the form:
   a <= b < c
or similar, where a b and c are integers.
*)
Ltac prove_a_lt_b_lt_c := compute; split; [ intro; discriminate | reflexivity ].

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "." "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
