(******************************************************************************)
(* Some notations defined in Vellvm that we wish to re-use.                   *)
(******************************************************************************)

Require opsem.
Require ndopsem.

Definition GVsSig : opsem.GenericValues := ndopsem.NDGVs.

Notation GVs := GVsSig.(opsem.GVsT).

Notation "gv @ gvs" :=
  (GVsSig.(opsem.instantiate_gvs) gv gvs) (at level 43, right associativity).

Notation "$ gv # t $" := (GVsSig.(opsem.gv2gvs) gv t) (at level 41).

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "." "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
