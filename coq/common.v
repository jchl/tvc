(******************************************************************************)
(* This file is imported at the top of every tvc-generated proof, and imports *)
(* everything that those proofs need.                                         *)
(******************************************************************************)

(* from Coq *)
Require Coq.Lists.List.
Export Coq.Lists.List.ListNotations.
Require Coq.Strings.String.
Open Scope string_scope.
Require Export Coq.ZArith.ZArith.

(* from Vellvm *)
Require syntax.
Export syntax.LLVMsyntax.
Require genericvalues.
Require opsem.
Export opsem.Opsem.
Export opsem.OpsemAux.
Require ndopsem.
Require events.

(* from Vellvm/compcert *)
(* Require Memory. *)
(* XXX Coq gets confused between Memory.v (in Vellvm/compcert) and memory.v (in Csem) *)
Require Integers.
Require Values.

(* from csem *)
Require Export Csem.core.

(* from Tvc *)
Require Export base_tactics.
Require Export notation.
Require Export definitions.
Require Export atoms.
Require Export llvm_props.
Require Export llvm_tactics_converge.
Require Export llvm_tactics_noconverge.
Require Export llvm_tactics_nodiverge.
Require Export llvm_tactics_initstate.
Require Export llvm_tactics_memory.
Require Export llvm_tactics_simplify.
Require Export core_props.
Require Export core_tactics.
Require Export stdlib.

Global Opaque initLocals.
Global Transparent productInModuleB_dec.
Global Transparent opsem.instantiate_gvs opsem.cgv2gvs opsem.gv2gvs opsem.lift_op1 opsem.lift_op2.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "../coq" "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
