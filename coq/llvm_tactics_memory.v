(******************************************************************************)
(* Tactics for working for LLVM memory operations.                            *)
(******************************************************************************)

Require Import Coq.ZArith.ZArith.
Require opsem.

Inductive contiguous_allocs : Values.block -> Values.block -> Memory.Mem.mem -> Prop :=
| blockConsecutive : forall lo1 hi1 lo2 hi2 Mem1 Mem2 Mem3 b1 b2,
                       Memory.Mem.alloc Mem1 lo1 hi1 = (Mem2, b1) ->
                       Memory.Mem.alloc Mem2 lo2 hi2 = (Mem3, b2) ->
                       contiguous_allocs b1 b2 Mem3
| blockStar : forall lo hi Mem2 Mem3 b1 b2 b3,
                contiguous_allocs b1 b2 Mem2 ->
                Memory.Mem.alloc Mem2 lo hi = (Mem3, b3) ->
                contiguous_allocs b1 b3 Mem3.

Hint Resolve blockConsecutive.
Hint Resolve blockStar.

Lemma contiguous_allocs_gt :
  forall Mem b1 b2,
    contiguous_allocs b1 b2 Mem -> Z.lt b1 b2.
Proof.
  intros Mem0 b1 b2 H.
  induction H.
  erewrite Memory.Mem.alloc_result with (b := b1); [ | apply H ].
  erewrite Memory.Mem.alloc_result with (b := b2); [ | apply H0 ].
  erewrite Memory.Mem.nextblock_alloc with (m2 := Mem2); [ | apply H ].
  omega.
  assert (Z.lt b2 b3); [ | omega ].
  inversion H.
  erewrite Memory.Mem.alloc_result with (b := b3); [ | apply H0 ].
  erewrite Memory.Mem.alloc_result with (b := b2); [ | apply H2 ].
  erewrite Memory.Mem.nextblock_alloc with (m2 := Mem2); [ | apply H2 ].
  omega.
  erewrite Memory.Mem.alloc_result with (b := b3); [ | apply H0 ].
  erewrite Memory.Mem.alloc_result with (b := b2); [ | apply H2 ].
  erewrite Memory.Mem.nextblock_alloc with (m2 := Mem2); [ | apply H2 ].
  omega.
Qed.

Corollary contiguous_allocs_not_equal :
  forall Mem b1 b2,
    contiguous_allocs b1 b2 Mem -> ~(eq b1 b2).
Proof.
  eauto using Z.lt_neq, contiguous_allocs_gt.
Qed.

(*
This tactic takes two hypotheses, about allocs of different locations, and adds a hypothesis stating
that the corresponding memory blocks are not equal.
*)
Ltac assert_allocs_not_equal H1 H2 :=
  match type of H1 with
    | eq (Memory.Mem.alloc _ _ _) (_, ?m1) =>
      match type of H2 with
        | eq (Memory.Mem.alloc _ _ _) (_, ?m2) =>
          assert (not (eq m1 m2)) by
              (eauto using contiguous_allocs_not_equal ||
               assert (not (eq m2 m1)) by
                  (eauto using contiguous_allocs_not_equal); auto)
      end
  end.

(*
This tactic takes two hypotheses, about a store and a load to the same location, deletes the
hypothesis about the load, and replaces it with a hypothesis equating the value loaded with the
value stored.
*)
Ltac equate_store_and_load Hstore Hload :=
  erewrite Memory.Mem.load_store_same in Hload; [ | apply Hstore | simpl; (trivial || assumption) ];
  injection Hload;
  clear Hload;
  intro Hload.

(*
This tactic takes two hypotheses, about an alloc and a load of the same location, deletes the
hypothesis about the load, and replaces it with a hypothesis equating the value loaded with Vundef.
*)
Ltac equate_alloc_and_load Halloc Hload :=
  eapply Memory.Mem.load_alloc_same in Hload; [ | apply Halloc ].

(*
This tactic takes two hypotheses, about a store and a load to different locations, and modifies the
hypotheses about the load so that it results to the memory contents before the store.
*)
Ltac commute_store_and_load Hstore Hload :=
  erewrite Memory.Mem.load_store_other in Hload; [ | apply Hstore | left; assumption ].

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "." "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
