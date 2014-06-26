Require List.
Import List.ListNotations.
Require String.
Open Scope string_scope.
Require Import ZArith.

Require syntax.
Import syntax.LLVMsyntax.
Require genericvalues.
Require opsem.
Import opsem.OpsemAux.
Import opsem.Opsem.
Require ndopsem.
Require events.

Require Memory.
Require Integers.
Require Values.

Require Import Csem.core.
Require Csem.core_run.
Require Csem.core_run_inductive.

Require Import Tvc.base_tactics.
Require Import Tvc.notation.
Require Import Tvc.definitions.
Require Import Tvc.invert_insn.
Require Import Tvc.tactics.
Require Import Tvc.llvm_diverge.
Require Import Tvc.core_props.
Require Import Tvc.stdlib.

Require Import MetatheoryAtom.
Definition atoms := natoms 11.
Definition num_atoms := 11.
Opaque atoms.

Definition default_atom := projT1 (atom_fresh_for_list []).
Definition ax i := nth i (projT1 atoms) default_atom.

Notation l0 := (ax 0). (* 0 *)
Notation r0 := (ax 1). (* %3 *)
Notation r1 := (ax 2). (* %-1 *)
Notation r2 := (ax 3). (* %1 *)
Notation r3 := (ax 4). (* %2 *)
Notation r4 := (ax 5). (* %x *)
Notation r5 := (ax 6). (* %-3 *)
Notation r6 := (ax 7). (* %y *)
Notation r7 := (ax 8). (* %-2 *)
Notation r8 := (ax 9). (* @f *)
Notation r9 := (ax 10). (* @main *)

Lemma rewrite_eq_dec_not_equal :
  forall (A : Type) i j (x y : A),
    nat_ltb i num_atoms = true ->
    nat_ltb j num_atoms = true ->
    beq_nat i j = false ->
   (if CoqEqDec.eq_dec (ax i) (ax j) then x else y) = y.
Proof.
  intros.

  destruct CoqEqDec.eq_dec.

  apply nat_ltb_true in H.
  apply nat_ltb_true in H0.
  pose proof (projT2 atoms) as H2.
  apply (unique_eq _ (projT1 atoms) default_atom) in e; try assumption.
  subst j.
  rewrite <- beq_nat_refl in H1.
  discriminate.

  trivial.
Qed.

Opaque ax.

Hint Rewrite rewrite_eq_dec_equal : eq_dec_db.
Hint Rewrite rewrite_eq_dec_not_equal using reflexivity : eq_dec_db.

Definition _f_cmds_0_4 : list cmd :=
    [insn_load r0 (typ_int 32) (value_id r2) 4].
Definition _f_cmds_0_3 : list cmd :=
    (insn_store r7 (typ_int 32) (value_id r6) (value_id r3) 4) :: _f_cmds_0_4.
Definition _f_cmds_0_2 : list cmd :=
    (insn_store r5 (typ_int 32) (value_id r4) (value_id r2) 4) :: _f_cmds_0_3.
Definition _f_cmds_0_1 : list cmd :=
    (insn_alloca r3 (typ_int 32) (value_const (const_int 32 (1)%Z)) 4) :: _f_cmds_0_2.
Definition _f_cmds_0_0 : list cmd :=
    (insn_alloca r2 (typ_int 32) (value_const (const_int 32 (1)%Z)) 4) :: _f_cmds_0_1.

Definition _f_cmds_0 : list cmd :=
    _f_cmds_0_0.

Definition _f_term_0 : terminator :=
    insn_return r1 (typ_int 32) (value_id r0).

Definition _f_block_0 : block :=
    (l0, stmts_intro [] _f_cmds_0 _f_term_0).

Definition _f_fdef : fdef :=
    fdef_intro
     (fheader_intro
       (fnattrs_intro linkage_external visibility_default callconv_ccc [] [attribute_stackprotect; attribute_nounwind])
       (typ_int 32) r8 [((typ_int 32, []), r4); ((typ_int 32, []), r6)] None) 
     [_f_block_0].

Definition _main_cmds_0_1 : list cmd :=
    [insn_store r7 (typ_int 32) (value_const (const_int 32 (0)%Z)) (value_id r2) 0].
Definition _main_cmds_0_0 : list cmd :=
    (insn_alloca r2 (typ_int 32) (value_const (const_int 32 (1)%Z)) 4) :: _main_cmds_0_1.

Definition _main_cmds_0 : list cmd :=
    _main_cmds_0_0.

Definition _main_term_0 : terminator :=
    insn_return r1 (typ_int 32) (value_const (const_int 32 (0)%Z)).

Definition _main_block_0 : block :=
    (l0, stmts_intro [] _main_cmds_0 _main_term_0).

Definition _main_fdef : fdef :=
    fdef_intro
     (fheader_intro
       (fnattrs_intro linkage_external visibility_default callconv_ccc [] [attribute_stackprotect; attribute_nounwind])
       (typ_int 32) r9 [] None) [_main_block_0].

Definition mylayouts : list layout :=
    [layout_le; layout_ptr 64 64 64; layout_int 1 8 8; layout_int 8 8 8; 
     layout_int 16 16 16; layout_int 32 32 32; layout_int 64 64 64; layout_float 32 32 32; 
     layout_float 64 64 64; layout_vector 64 64 64; layout_vector 128 128 128; 
     layout_aggr 0 0 64; layout_stack 0 64 64; layout_float 80 128 128].

Definition mynamedts : list namedt :=
    [].

Definition myproducts : list product :=
    [product_fdef _f_fdef; product_fdef _main_fdef].

Definition llvm_prog : module :=
    module_intro mylayouts mynamedts myproducts.

Definition llvm_system : system := [llvm_prog].
(* Print llvm_prog. *)

Definition func_f : expr global.zero :=
    Esseq [] Eskip
     (Esseq []
       (Esseq [Some (Symbol 118 (Some "a_104"))]
         (Eaction
           (Paction Pos (Action [] (Load0 (Ectype (Basic0 (Integer (Signed Int_)))) (Esym (Symbol 1 (Some "x"))) NA))))
         (Esseq []
           (Eunseq
             [Eaction (Paction Pos (Action [] (Kill0 (Esym (Symbol 1 (Some "x"))))));
              Eaction (Paction Pos (Action [] (Kill0 (Esym (Symbol 0 (Some "y"))))))])
           (Eret
             (Ecall (Sym (Symbol 3 (Some "conv_int")))
               [Ectype (Basic0 (Integer (Signed Int_))); Esym (Symbol 118 (Some "a_104"))])))) Eskip).

Definition func_main : expr global.zero :=
    Esseq [] Eskip
     (Esseq []
       (Esseq [Some (Symbol 119 (Some "a_105"))] (Econst (Cint ((0)%Z)))
         (Esseq [] Eskip
           (Eret
             (Ecall (Sym (Symbol 3 (Some "conv_int")))
               [Ectype (Basic0 (Integer (Signed Int_))); Esym (Symbol 119 (Some "a_105"))])))) Eskip).

Definition core_stdlib : fun_map global.zero :=
    [(Symbol 19 (Some "ones_prefix"),
      (TyBase Integer0,
       [(Symbol 2 (Some "i"), Integer0); (Symbol 1 (Some "k"), Integer0); (Symbol 0 (Some "width"), Integer0)],
       Eif
        (Eop OpAnd
          (Eop OpOr (Eop OpLt (Econst (Cint ((0)%Z))) (Esym (Symbol 2 (Some "i"))))
            (Eop OpEq (Econst (Cint ((0)%Z))) (Esym (Symbol 2 (Some "i")))))
          (Eop OpLt (Esym (Symbol 2 (Some "i"))) (Esym (Symbol 1 (Some "k")))))
        (Eop OpAdd
          (Ecall (Sym (Symbol 1 (Some "exp")))
            [Econst (Cint ((2)%Z));
             Eop OpSub (Eop OpSub (Esym (Symbol 0 (Some "width"))) (Econst (Cint ((1)%Z))))
              (Esym (Symbol 2 (Some "i")))])
          (Ecall (Sym (Symbol 19 (Some "ones_prefix")))
            [Eop OpAdd (Esym (Symbol 2 (Some "i"))) (Econst (Cint ((1)%Z))); 
             Esym (Symbol 1 (Some "k")); Esym (Symbol 0 (Some "width"))])) 
        (Econst (Cint ((0)%Z)))));
     (Symbol 18 (Some "bitwise_OR"),
      (TyBase Integer0,
       [(Symbol 2 (Some "ty"), Ctype); (Symbol 1 (Some "n1"), Integer0); (Symbol 0 (Some "n2"), Integer0)],
       Elet (Symbol 114 (Some "n1_"))
        (Ecall (Impl Integer__encode) [Esym (Symbol 2 (Some "ty")); Esym (Symbol 1 (Some "n1"))])
        (Elet (Symbol 115 (Some "n2_"))
          (Ecall (Impl Integer__encode) [Esym (Symbol 2 (Some "ty")); Esym (Symbol 0 (Some "n2"))])
          (Ecall (Impl Integer__decode)
            [Esym (Symbol 2 (Some "ty"));
             Ecall (Sym (Symbol 17 (Some "bitwise_OR_aux")))
              [Esym (Symbol 114 (Some "n1_")); Esym (Symbol 115 (Some "n2_"));
               Ecall (Sym (Symbol 7 (Some "ctype_width"))) [Esym (Symbol 2 (Some "ty"))]]]))));
     (Symbol 17 (Some "bitwise_OR_aux"),
      (TyBase Integer0,
       [(Symbol 2 (Some "n1"), Integer0); (Symbol 1 (Some "n2"), Integer0); (Symbol 0 (Some "w"), Integer0)],
       Eif (Eop OpEq (Esym (Symbol 0 (Some "w"))) (Econst (Cint ((0)%Z)))) 
        (Econst (Cint ((0)%Z)))
        (Elet (Symbol 112 (Some "n1_")) (Eop OpDiv (Esym (Symbol 2 (Some "n1"))) (Econst (Cint ((2)%Z))))
          (Elet (Symbol 113 (Some "n2_")) (Eop OpDiv (Esym (Symbol 1 (Some "n2"))) (Econst (Cint ((2)%Z))))
            (Eop OpAdd
              (Eif
                (Eop OpOr
                  (Eop OpEq (Eop OpMod (Esym (Symbol 2 (Some "n1"))) (Econst (Cint ((2)%Z)))) (Econst (Cint ((1)%Z))))
                  (Eop OpEq (Eop OpMod (Esym (Symbol 1 (Some "n2"))) (Econst (Cint ((2)%Z)))) (Econst (Cint ((1)%Z)))))
                (Econst (Cint ((1)%Z))) (Econst (Cint ((0)%Z))))
              (Eop OpMul (Econst (Cint ((2)%Z)))
                (Ecall (Sym (Symbol 17 (Some "bitwise_OR_aux")))
                  [Esym (Symbol 112 (Some "n1_")); Esym (Symbol 113 (Some "n2_"));
                   Eop OpSub (Esym (Symbol 0 (Some "w"))) (Econst (Cint ((1)%Z)))])))))));
     (Symbol 16 (Some "bitwise_XOR"),
      (TyBase Integer0,
       [(Symbol 2 (Some "ty"), Ctype); (Symbol 1 (Some "n1"), Integer0); (Symbol 0 (Some "n2"), Integer0)],
       Elet (Symbol 110 (Some "n1_"))
        (Ecall (Impl Integer__encode) [Esym (Symbol 2 (Some "ty")); Esym (Symbol 1 (Some "n1"))])
        (Elet (Symbol 111 (Some "n2_"))
          (Ecall (Impl Integer__encode) [Esym (Symbol 2 (Some "ty")); Esym (Symbol 0 (Some "n2"))])
          (Ecall (Impl Integer__decode)
            [Esym (Symbol 2 (Some "ty"));
             Ecall (Sym (Symbol 15 (Some "bitwise_XOR_aux")))
              [Esym (Symbol 110 (Some "n1_")); Esym (Symbol 111 (Some "n2_"));
               Ecall (Sym (Symbol 7 (Some "ctype_width"))) [Esym (Symbol 2 (Some "ty"))]]]))));
     (Symbol 15 (Some "bitwise_XOR_aux"),
      (TyBase Integer0,
       [(Symbol 2 (Some "n1"), Integer0); (Symbol 1 (Some "n2"), Integer0); (Symbol 0 (Some "w"), Integer0)],
       Eif (Eop OpEq (Esym (Symbol 0 (Some "w"))) (Econst (Cint ((0)%Z)))) 
        (Econst (Cint ((0)%Z)))
        (Elet (Symbol 108 (Some "n1_")) (Eop OpDiv (Esym (Symbol 2 (Some "n1"))) (Econst (Cint ((2)%Z))))
          (Elet (Symbol 109 (Some "n2_")) (Eop OpDiv (Esym (Symbol 1 (Some "n2"))) (Econst (Cint ((2)%Z))))
            (Eop OpAdd
              (Eif
                (Eop OpAnd
                  (Eop OpEq
                    (Eop OpMul (Eop OpMod (Esym (Symbol 2 (Some "n1"))) (Econst (Cint ((2)%Z))))
                      (Eop OpMod (Esym (Symbol 1 (Some "n2"))) (Econst (Cint ((2)%Z))))) 
                    (Econst (Cint ((0)%Z))))
                  (Enot
                    (Eop OpEq
                      (Eop OpAdd (Eop OpMod (Esym (Symbol 2 (Some "n1"))) (Econst (Cint ((2)%Z))))
                        (Eop OpMod (Esym (Symbol 1 (Some "n2"))) (Econst (Cint ((2)%Z))))) 
                      (Econst (Cint ((0)%Z)))))) (Econst (Cint ((1)%Z))) 
                (Econst (Cint ((0)%Z))))
              (Eop OpMul (Econst (Cint ((2)%Z)))
                (Ecall (Sym (Symbol 15 (Some "bitwise_XOR_aux")))
                  [Esym (Symbol 108 (Some "n1_")); Esym (Symbol 109 (Some "n2_"));
                   Eop OpSub (Esym (Symbol 0 (Some "w"))) (Econst (Cint ((1)%Z)))])))))));
     (Symbol 14 (Some "bitwise_AND"),
      (TyBase Integer0,
       [(Symbol 2 (Some "ty"), Ctype); (Symbol 1 (Some "n1"), Integer0); (Symbol 0 (Some "n2"), Integer0)],
       Elet (Symbol 106 (Some "n1_"))
        (Ecall (Impl Integer__encode) [Esym (Symbol 2 (Some "ty")); Esym (Symbol 1 (Some "n1"))])
        (Elet (Symbol 107 (Some "n2_"))
          (Ecall (Impl Integer__encode) [Esym (Symbol 2 (Some "ty")); Esym (Symbol 0 (Some "n2"))])
          (Ecall (Impl Integer__decode)
            [Esym (Symbol 2 (Some "ty"));
             Ecall (Sym (Symbol 13 (Some "bitwise_AND_aux")))
              [Esym (Symbol 106 (Some "n1_")); Esym (Symbol 107 (Some "n2_"));
               Ecall (Sym (Symbol 7 (Some "ctype_width"))) [Esym (Symbol 2 (Some "ty"))]]]))));
     (Symbol 13 (Some "bitwise_AND_aux"),
      (TyBase Integer0,
       [(Symbol 2 (Some "n1"), Integer0); (Symbol 1 (Some "n2"), Integer0); (Symbol 0 (Some "w"), Integer0)],
       Eif (Eop OpEq (Esym (Symbol 0 (Some "w"))) (Econst (Cint ((0)%Z)))) 
        (Econst (Cint ((0)%Z)))
        (Elet (Symbol 104 (Some "n1_")) (Eop OpDiv (Esym (Symbol 2 (Some "n1"))) (Econst (Cint ((2)%Z))))
          (Elet (Symbol 105 (Some "n2_")) (Eop OpDiv (Esym (Symbol 1 (Some "n2"))) (Econst (Cint ((2)%Z))))
            (Eop OpAdd
              (Eif
                (Eop OpAnd
                  (Eop OpEq (Eop OpMod (Esym (Symbol 2 (Some "n1"))) (Econst (Cint ((2)%Z)))) (Econst (Cint ((1)%Z))))
                  (Eop OpEq (Eop OpMod (Esym (Symbol 1 (Some "n2"))) (Econst (Cint ((2)%Z)))) (Econst (Cint ((1)%Z)))))
                (Econst (Cint ((1)%Z))) (Econst (Cint ((0)%Z))))
              (Eop OpMul (Econst (Cint ((2)%Z)))
                (Ecall (Sym (Symbol 13 (Some "bitwise_AND_aux")))
                  [Esym (Symbol 104 (Some "n1_")); Esym (Symbol 105 (Some "n2_"));
                   Eop OpSub (Esym (Symbol 0 (Some "w"))) (Econst (Cint ((1)%Z)))])))))));
     (Symbol 12 (Some "complementTwos"),
      (TyBase Integer0, [(Symbol 1 (Some "ty"), Ctype); (Symbol 0 (Some "n"), Integer0)],
       Ecall (Sym (Symbol 11 (Some "complementTwos_aux")))
        [Esym (Symbol 0 (Some "n")); Ecall (Sym (Symbol 7 (Some "ctype_width"))) [Esym (Symbol 1 (Some "ty"))]]));
     (Symbol 11 (Some "complementTwos_aux"),
      (TyBase Integer0, [(Symbol 1 (Some "n"), Integer0); (Symbol 0 (Some "w"), Integer0)],
       Eif (Eop OpEq (Esym (Symbol 0 (Some "w"))) (Econst (Cint ((0)%Z)))) 
        (Esym (Symbol 1 (Some "n")))
        (Elet (Symbol 103 (Some "n_")) (Eop OpDiv (Esym (Symbol 1 (Some "n"))) (Econst (Cint ((2)%Z))))
          (Eop OpAdd
            (Eop OpSub (Econst (Cint ((1)%Z))) (Eop OpMod (Esym (Symbol 1 (Some "n"))) (Econst (Cint ((2)%Z)))))
            (Eop OpMul (Econst (Cint ((2)%Z)))
              (Ecall (Sym (Symbol 11 (Some "complementTwos_aux")))
                [Esym (Symbol 103 (Some "n_")); Eop OpSub (Esym (Symbol 0 (Some "w"))) (Econst (Cint ((1)%Z)))]))))));
     (Symbol 10 (Some "decodeTwos"),
      (TyBase Integer0, [(Symbol 1 (Some "ty"), Ctype); (Symbol 0 (Some "n"), Integer0)],
       Elet (Symbol 102 (Some "width")) (Ecall (Sym (Symbol 7 (Some "ctype_width"))) [Esym (Symbol 1 (Some "ty"))])
        (Eif
          (Eop OpOr (Eop OpLt (Esym (Symbol 0 (Some "n"))) (Econst (Cint ((0)%Z))))
            (Eop OpOr
              (Eop OpLt (Ecall (Sym (Symbol 1 (Some "exp"))) [Econst (Cint ((2)%Z)); Esym (Symbol 102 (Some "width"))])
                (Esym (Symbol 0 (Some "n"))))
              (Eop OpEq (Ecall (Sym (Symbol 1 (Some "exp"))) [Econst (Cint ((2)%Z)); Esym (Symbol 102 (Some "width"))])
                (Esym (Symbol 0 (Some "n")))))) Eerror
          (Eif
            (Eop OpOr
              (Eop OpLt (Esym (Symbol 0 (Some "n")))
                (Eop OpSub
                  (Ecall (Sym (Symbol 1 (Some "exp")))
                    [Econst (Cint ((2)%Z)); Eop OpSub (Esym (Symbol 102 (Some "width"))) (Econst (Cint ((1)%Z)))])
                  (Econst (Cint ((1)%Z)))))
              (Eop OpEq (Esym (Symbol 0 (Some "n")))
                (Eop OpSub
                  (Ecall (Sym (Symbol 1 (Some "exp")))
                    [Econst (Cint ((2)%Z)); Eop OpSub (Esym (Symbol 102 (Some "width"))) (Econst (Cint ((1)%Z)))])
                  (Econst (Cint ((1)%Z)))))) (Esym (Symbol 0 (Some "n")))
            (Eop OpSub (Esym (Symbol 0 (Some "n")))
              (Ecall (Sym (Symbol 1 (Some "exp"))) [Econst (Cint ((2)%Z)); Esym (Symbol 102 (Some "width"))]))))));
     (Symbol 9 (Some "encodeTwos"),
      (TyBase Integer0, [(Symbol 1 (Some "ty"), Ctype); (Symbol 0 (Some "n"), Integer0)],
       Elet (Symbol 101 (Some "width")) (Ecall (Sym (Symbol 7 (Some "ctype_width"))) [Esym (Symbol 1 (Some "ty"))])
        (Eif
          (Eop OpOr
            (Eop OpLt (Esym (Symbol 0 (Some "n")))
              (Eop OpSub (Econst (Cint ((0)%Z)))
                (Ecall (Sym (Symbol 1 (Some "exp")))
                  [Econst (Cint ((2)%Z)); Eop OpSub (Esym (Symbol 101 (Some "width"))) (Econst (Cint ((1)%Z)))])))
            (Eop OpLt
              (Eop OpSub
                (Ecall (Sym (Symbol 1 (Some "exp")))
                  [Econst (Cint ((2)%Z)); Eop OpSub (Esym (Symbol 101 (Some "width"))) (Econst (Cint ((1)%Z)))])
                (Econst (Cint ((1)%Z)))) (Esym (Symbol 0 (Some "n"))))) Eerror
          (Eif
            (Eop OpOr (Eop OpLt (Econst (Cint ((0)%Z))) (Esym (Symbol 0 (Some "n"))))
              (Eop OpEq (Econst (Cint ((0)%Z))) (Esym (Symbol 0 (Some "n"))))) 
            (Esym (Symbol 0 (Some "n")))
            (Eop OpAdd (Ecall (Sym (Symbol 1 (Some "exp"))) [Econst (Cint ((2)%Z)); Esym (Symbol 101 (Some "width"))])
              (Esym (Symbol 0 (Some "n"))))))));
     (Symbol 8 (Some "is_representable"),
      (TyBase Boolean, [(Symbol 1 (Some "n"), Integer0); (Symbol 0 (Some "ty"), Ctype)],
       Eop OpAnd
        (Eop OpOr (Eop OpLt (Ecall (Impl Ctype_min) [Esym (Symbol 0 (Some "ty"))]) (Esym (Symbol 1 (Some "n"))))
          (Eop OpEq (Ecall (Impl Ctype_min) [Esym (Symbol 0 (Some "ty"))]) (Esym (Symbol 1 (Some "n")))))
        (Eop OpOr (Eop OpLt (Esym (Symbol 1 (Some "n"))) (Ecall (Impl Ctype_max) [Esym (Symbol 0 (Some "ty"))]))
          (Eop OpEq (Esym (Symbol 1 (Some "n"))) (Ecall (Impl Ctype_max) [Esym (Symbol 0 (Some "ty"))])))));
     (Symbol 7 (Some "ctype_width"),
      (TyBase Integer0, [(Symbol 0 (Some "ty"), Ctype)],
       Eop OpMul (Ecall (Impl Sizeof) [Esym (Symbol 0 (Some "ty"))]) (Eimpl Characters__bits_in_byte)));
     (Symbol 6 (Some "usual_arithmetic"),
      (TyBase Ctype, [(Symbol 1 (Some "ty1"), Ctype); (Symbol 0 (Some "ty2"), Ctype)], Esym (Symbol 1 (Some "ty1"))));
     (Symbol 5 (Some "conv"),
      (TyBase Integer0,
       [(Symbol 2 (Some "ty1"), Ctype); (Symbol 1 (Some "ty2"), Ctype); (Symbol 0 (Some "n"), Integer0)],
       Eif
        (Eop OpAnd (Eis_scalar (Esym (Symbol 2 (Some "ty1"))))
          (Eop OpEq (Esym (Symbol 1 (Some "ty2"))) (Ectype (Basic0 (Integer Bool)))))
        (Eif (Eop OpEq (Esym (Symbol 0 (Some "n"))) (Econst (Cint ((0)%Z)))) 
          (Econst (Cint ((0)%Z))) (Econst (Cint ((1)%Z))))
        (Eif (Eop OpAnd (Eis_integer (Esym (Symbol 2 (Some "ty1")))) (Eis_integer (Esym (Symbol 1 (Some "ty2")))))
          (Eif
            (Ecall (Sym (Symbol 8 (Some "is_representable")))
              [Esym (Symbol 0 (Some "n")); Esym (Symbol 1 (Some "ty2"))]) 
            (Esym (Symbol 0 (Some "n")))
            (Eif (Eis_unsigned (Esym (Symbol 1 (Some "ty2"))))
              (Ecall (Sym (Symbol 4 (Some "conv_aux"))) [Esym (Symbol 1 (Some "ty2")); Esym (Symbol 0 (Some "n"))])
              (Econst (Cint ((42)%Z))))) (Econst (Cint ((42)%Z))))));
     (Symbol 4 (Some "conv_aux"),
      (TyBase Integer0, [(Symbol 1 (Some "ty"), Ctype); (Symbol 0 (Some "n"), Integer0)],
       Elet (Symbol 100 (Some "n2"))
        (Eif (Eop OpLt (Ecall (Impl Ctype_max) [Esym (Symbol 1 (Some "ty"))]) (Esym (Symbol 0 (Some "n"))))
          (Eop OpAdd (Eop OpSub (Esym (Symbol 0 (Some "n"))) (Ecall (Impl Ctype_max) [Esym (Symbol 1 (Some "ty"))]))
            (Econst (Cint ((1)%Z))))
          (Eop OpAdd (Eop OpAdd (Esym (Symbol 0 (Some "n"))) (Ecall (Impl Ctype_max) [Esym (Symbol 1 (Some "ty"))]))
            (Econst (Cint ((1)%Z)))))
        (Eif
          (Ecall (Sym (Symbol 8 (Some "is_representable")))
            [Esym (Symbol 100 (Some "n2")); Esym (Symbol 1 (Some "ty"))]) 
          (Esym (Symbol 100 (Some "n2")))
          (Ecall (Sym (Symbol 4 (Some "conv_aux"))) [Esym (Symbol 1 (Some "ty")); Esym (Symbol 100 (Some "n2"))]))));
     (Symbol 3 (Some "conv_int"),
      (TyBase Integer0, [(Symbol 1 (Some "ty"), Ctype); (Symbol 0 (Some "n"), Integer0)],
       Eif (Eop OpEq (Esym (Symbol 1 (Some "ty"))) (Ectype (Basic0 (Integer Bool))))
        (Eif (Eop OpEq (Esym (Symbol 0 (Some "n"))) (Econst (Cint ((0)%Z)))) 
          (Econst (Cint ((0)%Z))) (Econst (Cint ((1)%Z))))
        (Eif
          (Ecall (Sym (Symbol 8 (Some "is_representable"))) [Esym (Symbol 0 (Some "n")); Esym (Symbol 1 (Some "ty"))])
          (Esym (Symbol 0 (Some "n")))
          (Eif (Eis_unsigned (Esym (Symbol 1 (Some "ty"))))
            (Ecall (Sym (Symbol 4 (Some "conv_aux"))) [Esym (Symbol 1 (Some "ty")); Esym (Symbol 0 (Some "n"))])
            (Econst (Cint ((42)%Z)))))));
     (Symbol 2 (Some "overflow"),
      (TyBase Integer0, [(Symbol 1 (Some "ty"), Ctype); (Symbol 0 (Some "n"), Integer0)], Esym (Symbol 0 (Some "n"))));
     (Symbol 1 (Some "exp"),
      (TyBase Integer0, [(Symbol 1 (Some "n"), Integer0); (Symbol 0 (Some "m"), Integer0)],
       Ecall (Sym (Symbol 0 (Some "exp_aux")))
        [Esym (Symbol 1 (Some "n")); Esym (Symbol 0 (Some "m")); Econst (Cint ((1)%Z))]));
     (Symbol 0 (Some "exp_aux"),
      (TyBase Integer0,
       [(Symbol 2 (Some "n"), Integer0); (Symbol 1 (Some "m"), Integer0); (Symbol 0 (Some "acc"), Integer0)],
       Eif (Eop OpEq (Esym (Symbol 1 (Some "m"))) (Econst (Cint ((0)%Z)))) 
        (Esym (Symbol 0 (Some "acc")))
        (Ecall (Sym (Symbol 0 (Some "exp_aux")))
          [Esym (Symbol 2 (Some "n")); Eop OpSub (Esym (Symbol 1 (Some "m"))) (Econst (Cint ((1)%Z)));
           Eop OpMul (Esym (Symbol 2 (Some "n"))) (Esym (Symbol 0 (Some "acc")))])))].

Definition core_impl : impl_ global.zero :=
    [(Ctype_max,
      IFun Integer0 [(Symbol 0 (Some "ty"), Ctype)]
       (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer Char)))) 
         (Econst (Cint ((127)%Z)))
         (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer Bool)))) 
           (Econst (Cint ((1)%Z)))
           (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Ichar)))))
             (Econst (Cint ((127)%Z)))
             (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Ichar)))))
               (Econst (Cint ((255)%Z)))
               (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Short)))))
                 (Econst (Cint ((32767)%Z)))
                 (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Short)))))
                   (Econst (Cint ((65535)%Z)))
                   (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Int_)))))
                     (Econst (Cint ((2147483647)%Z)))
                     (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Int_)))))
                       (Econst (Cint ((4294967295)%Z)))
                       (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Long)))))
                         (Econst (Cint ((9223372036854775807)%Z)))
                         (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Long)))))
                           (Econst (Cint ((18446744073709551615)%Z)))
                           (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed LongLong)))))
                             (Econst (Cint ((9223372036854775807)%Z)))
                             (Eif
                               (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned LongLong)))))
                               (Econst (Cint ((18446744073709551615)%Z))) Eerror)))))))))))));
     (Ctype_min,
      IFun Integer0 [(Symbol 0 (Some "ty"), Ctype)]
       (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer Char)))) 
         (Econst (Cint ((-128)%Z)))
         (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer Bool)))) 
           (Econst (Cint ((0)%Z)))
           (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Ichar)))))
             (Econst (Cint ((-128)%Z)))
             (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Ichar)))))
               (Econst (Cint ((0)%Z)))
               (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Short)))))
                 (Econst (Cint ((-32768)%Z)))
                 (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Short)))))
                   (Econst (Cint ((0)%Z)))
                   (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Int_)))))
                     (Econst (Cint ((-2147483648)%Z)))
                     (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Int_)))))
                       (Econst (Cint ((0)%Z)))
                       (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Long)))))
                         (Econst (Cint ((-9223372036854775808)%Z)))
                         (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Long)))))
                           (Econst (Cint ((0)%Z)))
                           (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed LongLong)))))
                             (Econst (Cint ((-9223372036854775808)%Z)))
                             (Eif
                               (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned LongLong)))))
                               (Econst (Cint ((0)%Z))) Eerror)))))))))))));
     (Bitwise_complement,
      IFun Integer0 [(Symbol 1 (Some "ty"), Ctype); (Symbol 0 (Some "n"), Integer0)]
       (Elet (Symbol 117 (Some "n"))
         (Ecall (Sym (Symbol 9 (Some "encodeTwos"))) [Esym (Symbol 1 (Some "ty")); Esym (Symbol 0 (Some "n"))])
         (Ecall (Sym (Symbol 10 (Some "decodeTwos")))
           [Esym (Symbol 1 (Some "ty"));
            Ecall (Sym (Symbol 12 (Some "complementTwos"))) [Esym (Symbol 1 (Some "ty")); Esym (Symbol 117 (Some "n"))]])));
     (SHR_signed_negative,
      IFun Integer0 [(Symbol 2 (Some "ty"), Ctype); (Symbol 1 (Some "n"), Integer0); (Symbol 0 (Some "m"), Integer0)]
       (Elet (Symbol 116 (Some "n"))
         (Ecall (Sym (Symbol 9 (Some "encodeTwos"))) [Esym (Symbol 2 (Some "ty")); Esym (Symbol 1 (Some "n"))])
         (Ecall (Sym (Symbol 10 (Some "decodeTwos")))
           [Esym (Symbol 2 (Some "ty"));
            Eop OpAdd
             (Eop OpDiv (Esym (Symbol 116 (Some "n")))
               (Ecall (Sym (Symbol 1 (Some "exp"))) [Econst (Cint ((2)%Z)); Esym (Symbol 0 (Some "m"))]))
             (Ecall (Sym (Symbol 19 (Some "ones_prefix")))
               [Econst (Cint ((0)%Z)); Esym (Symbol 0 (Some "m"));
                Ecall (Sym (Symbol 7 (Some "ctype_width"))) [Esym (Symbol 2 (Some "ty"))]])])));
     (Alignof,
      IFun Integer0 [(Symbol 0 (Some "ty"), Ctype)]
       (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer Char)))) 
         (Econst (Cint ((1)%Z)))
         (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer Bool)))) 
           (Econst (Cint ((1)%Z)))
           (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Ichar)))))
             (Econst (Cint ((1)%Z)))
             (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Ichar)))))
               (Econst (Cint ((1)%Z)))
               (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Short)))))
                 (Econst (Cint ((2)%Z)))
                 (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Short)))))
                   (Econst (Cint ((2)%Z)))
                   (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Int_)))))
                     (Econst (Cint ((4)%Z)))
                     (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Int_)))))
                       (Econst (Cint ((4)%Z)))
                       (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Long)))))
                         (Econst (Cint ((8)%Z)))
                         (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Long)))))
                           (Econst (Cint ((8)%Z)))
                           (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed LongLong)))))
                             (Econst (Cint ((8)%Z)))
                             (Eif
                               (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned LongLong)))))
                               (Econst (Cint ((8)%Z))) Eerror)))))))))))));
     (Sizeof,
      IFun Integer0 [(Symbol 0 (Some "ty"), Ctype)]
       (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer Char)))) 
         (Econst (Cint ((1)%Z)))
         (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer Bool)))) 
           (Econst (Cint ((1)%Z)))
           (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Ichar)))))
             (Econst (Cint ((1)%Z)))
             (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Ichar)))))
               (Econst (Cint ((1)%Z)))
               (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Short)))))
                 (Econst (Cint ((2)%Z)))
                 (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Short)))))
                   (Econst (Cint ((2)%Z)))
                   (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Int_)))))
                     (Econst (Cint ((4)%Z)))
                     (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Int_)))))
                       (Econst (Cint ((4)%Z)))
                       (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed Long)))))
                         (Econst (Cint ((8)%Z)))
                         (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned Long)))))
                           (Econst (Cint ((8)%Z)))
                           (Eif (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Signed LongLong)))))
                             (Econst (Cint ((8)%Z)))
                             (Eif
                               (Eop OpEq (Esym (Symbol 0 (Some "ty"))) (Ectype (Basic0 (Integer (Unsigned LongLong)))))
                               (Econst (Cint ((8)%Z))) Eerror)))))))))))));
     (Integer__decode,
      IFun Integer0 [(Symbol 1 (Some "ty"), Ctype); (Symbol 0 (Some "n"), Integer0)]
       (Ecall (Sym (Symbol 10 (Some "decodeTwos"))) [Esym (Symbol 1 (Some "ty")); Esym (Symbol 0 (Some "n"))]));
     (Integer__encode,
      IFun Integer0 [(Symbol 1 (Some "ty"), Ctype); (Symbol 0 (Some "n"), Integer0)]
       (Ecall (Sym (Symbol 9 (Some "encodeTwos"))) [Esym (Symbol 1 (Some "ty")); Esym (Symbol 0 (Some "n"))]));
     (Characters__bits_in_byte, Def Integer0 (Econst (Cint ((8)%Z))))].

Definition core_file : file_ global.zero := {|
  main :=
    Symbol 0 (Some "f");
  stdlib :=
    core_stdlib;
  impl :=
    core_impl;
  funs :=
    [(Symbol 1 (Some "main"), (TyEffect Integer0, [], func_main));
     (Symbol 0 (Some "f"),
      (TyEffect Integer0, [(Symbol 1 (Some "x"), Address); (Symbol 0 (Some "y"), Address)], func_f))]
|}.

(* Print core_file. *)

Transparent productInModuleB_dec.
Transparent opsem.instantiate_gvs opsem.cgv2gvs opsem.gv2gvs opsem.lift_op1 opsem.lift_op2.
Opaque initLocals.

Definition mytd : targetdata := (mylayouts, mynamedts).

Definition llvm_value_to_core_value (gv : genericvalues.LLVMgv.GenericValue) : option (expr global.zero) :=
  match (genericvalues.LLVMgv.GV2val mytd gv) with
    | Some v =>
      match v with
        | Values.Vint sz i => Some (Econst (Cint (Integers.Int.signed _ i))) (* XXX or .signed ... *)
        | _ => None
      end
    | None => None
  end.

Definition main_fn : id := r8. (* @f *)

Lemma initState_good : 
  forall cfg IS v0 i0 v1 i1,
    eq v0 [(Values.Vint 31 i0, AST.Mint 31)] ->
    eq v1 [(Values.Vint 31 i1, AST.Mint 31)] ->
    (@s_genInitState GVsSig llvm_system main_fn [$ v0 # typ_int 32 $; $ v1 # typ_int 32 $] Memory.Mem.empty = Some (cfg, IS)) ->
    exists g f,
      eq (@s_genInitState GVsSig llvm_system main_fn [$ v0 # typ_int 32 $; $ v1 # typ_int 32 $] Memory.Mem.empty)
         (Some ((mkCfg llvm_system mytd myproducts g f),
                (mkState [mkEC _f_fdef _f_block_0 _f_cmds_0 _f_term_0 [(r6, $ v1 # typ_int 32 $); (r4, $ v0 # typ_int 32 $)] []] Memory.Mem.empty))).
Proof.
  intros ? ? ? ? ? ? H0' H1' H.
  rewrite H.
  unfold s_genInitState in H.
  simpl in H.
  fold main_fn in H.
  unfold CoqEqDec.eq_dec in H.
  unfold CoqEqDec.EqDec_eq_of_EqDec in H.
  destruct_general_eq_dec_equal EqDec_atom main_fn.
  unfold productInModuleB_dec in H.
  unfold productInModuleB in H.
  unfold InProductsB in H.
  simpl in H.
  unfold productEqB in H.
  unfold sumbool2bool in H.
  destruct_general_eq_dec_equal_wc product_dec.
  simpl in H.
  match type of H with
    | eq (match ?e with | Some _ => _ | None => _ end) _ =>
      destruct e as [[[g f] mem] | ?] eqn:H1; try discriminate
  end.
  exists g.
  exists f.
  repeat match type of H1 with
           | eq (match ?e with | Some _ => _ | None => _ end) _ =>
             destruct e eqn:H2; clear H2; try discriminate
         end.
  injection H1; intros ? _ _; clear H1; subst mem.
  match type of H with
    | eq (match ?e with | Some _ => _ | None => _ end) _ =>
      destruct e eqn:H2; try discriminate
  end.
  Transparent initLocals.
  unfold initLocals in H2.
  Opaque initLocals.
  Opaque ndopsem.MNDGVs.gv2gvs.
  simpl in H2.
  Transparent ndopsem.MNDGVs.gv2gvs.
  destruct_all_eq_dec.
  erewrite (instantiate_gv2gvs mytd v0 _ _ _ _) in H2; [ | | eassumption ].
  Focus 2.
  unfold fit_gv, gv_chunks_match_typb, gv_chunks_match_typb_aux, Values.Val.has_chunkb.
  destruct (eq_nat_dec _ _) as [? | x]; [ | contradiction x; reflexivity ].
  destruct i0 as [? [? ?]].
  destruct (Coqlib.zle _ _); [ | contradiction ].
  destruct (Coqlib.zlt _ _); [ | contradiction ].
  subst.
  reflexivity.
  erewrite (instantiate_gv2gvs mytd v1 _ _ _ _) in H2; [ | | eassumption ].
  Focus 2.
  unfold fit_gv, gv_chunks_match_typb, gv_chunks_match_typb_aux, Values.Val.has_chunkb.
  destruct (eq_nat_dec _ _) as [? | x]; [ | contradiction x; reflexivity ].
  destruct i1 as [? [? ?]].
  destruct (Coqlib.zle _ _); [ | contradiction ].
  destruct (Coqlib.zlt _ _); [ | contradiction ].
  subst.
  reflexivity.
  injection H2; intro; clear H2; subst.
  rewrite <- H.
  reflexivity.
Qed.

Definition thevalue (v0 : genericvalues.LLVMgv.GenericValue) (v1 : genericvalues.LLVMgv.GenericValue) : genericvalues.LLVMgv.GenericValue :=
  v0.

Lemma llvm_converges_only_to_thevalue :
  forall v v0 i0 v1 i1,
    eq v0 [(Values.Vint 31 i0, AST.Mint 31)] ->
    eq v1 [(Values.Vint 31 i1, AST.Mint 31)] ->
    (exists gv,
       (exists tr,
          s_converges llvm_system main_fn [$ v0 # typ_int 32 $; $ v1 # typ_int 32 $] tr gv) /\
       (GVsSig.(opsem.instantiate_gvs) v gv)) ->
    eq v (thevalue v0 v1).
Proof.
  intros ? ? ? ? ? H0' H1' [? [[? H] ?]].
  inversion H as [? ? ? ? ? ? ? ? H']; clear H.  destruct_initState (initState_good _ _ _ _ _ _ H0' H1' H').

  subst.
  Check "    insn_alloca r2 (typ_int 32) (value_const (const_int 32 (1)%Z)) 4".
  do_alloca. simplify_alloca Halloc1.

  Check "    insn_alloca r3 (typ_int 32) (value_const (const_int 32 (1)%Z)) 4".
  do_alloca. simplify_alloca Halloc2.

  Check "    insn_store r5 (typ_int 32) (value_id r4) (value_id r2) 4".
  do_store. simplify_store Hstore1.
  try rewrite <- signed_repr_inverse in Hstore1 by prove_a_lt_b_lt_c.

  Check "    insn_store r7 (typ_int 32) (value_id r6) (value_id r3) 4".
  do_store. simplify_store Hstore2.
  try rewrite <- signed_repr_inverse in Hstore2 by prove_a_lt_b_lt_c.

  Check "    insn_load r0 (typ_int 32) (value_id r2) 4".
  do_load. simplify_load Hload1.
  assert_allocs_not_equal Halloc1 Halloc2.
  commute_store_and_load Hstore2 Hload1.
  equate_store_and_load Hstore1 Hload1.
  try rewrite <- repr_unsigned_inverse in Hload1.
  subst.

  Check "    insn_return r1 (typ_int 32) (value_id r0)".
  do_ret. simplify.

  try (compute; intrange_proof_irr).
  reflexivity.
Qed.

Lemma core_converges_to_thevalue :
  forall v0 i0 v1 i1,
    eq v0 [(Values.Vint 31 i0, AST.Mint 31)] ->
    eq v1 [(Values.Vint 31 i1, AST.Mint 31)] ->
    (exists (cv cv0 cv1 : expr global.zero),
       (llvm_value_to_core_value (thevalue v0 v1) = Some cv) /\
       (llvm_value_to_core_value v0 = Some cv0) /\
       (llvm_value_to_core_value v1 = Some cv1) /\
       (core_converges core_file [cv0; cv1] cv)).
Proof.
  intros v0 i0 v1 i1 H0 H1.
  pose_cv (llvm_value_to_core_value (thevalue v0 v1)) cv.
  pose_cv (llvm_value_to_core_value v0) cv0.
  pose_cv (llvm_value_to_core_value v1) cv1.
  remember (Integers.Int.signed 31 i0) as i0'; hide Heqi0'.
  remember (Integers.Int.signed 31 i1) as i1'; hide Heqi1'.
  set (args := [cv0; cv1]).
(*  pose_s_and_t core_file args 1. *)
  subst.
  exists cv.
  exists cv0.
  exists cv1.
  repeat split; [
  unhide Heqi0'; subst cv; replace i0'; reflexivity |
  unhide Heqi0'; subst cv0; replace i0'; reflexivity |
  unhide Heqi1'; subst cv1; replace i1'; reflexivity |].

(*  exists t.
  exists s. *)
  eexists.
  eexists.

  (* vm_ *)compute.
  pose_s_and_e_converges 38.
  apply star_red2_ind_trans with (s2 := s2) (e2 := e2).

  apply (red2n_implies_star_red2_ind 38).
  vm_compute.
  repeat first [left; reflexivity | right].

  subst e2 s2.

  eapply star_red2_ind_trans (*with (s2 := s2) (e2 := e2) *).
  apply star_red_under_Eret; try reflexivity.
  apply conv_int_identity_signed_int; try reflexivity.

  unhide Heqi0'.
  replace i0'.
  apply (Integers.Int.signed_range 31).

(*
  (* This fails inexplicably.  Copying and pasting the definitions of s2 and t2 below works just fine. *)
  pose_s_and_t_converges 12.
  instantiate (1 := s2).
  instantiate (1 := t2).
 *)
  apply (red2n_implies_star_red2_ind 12).
  (* vm_ *) compute.
  repeat first [left; reflexivity | right].
Qed.

Theorem core_converges_if_llvm_converges :
  forall (gv : genericvalues.LLVMgv.GenericValue) v0 i0 v1 i1,
    eq v0 [(Values.Vint 31 i0, AST.Mint 31)] ->
    eq v1 [(Values.Vint 31 i1, AST.Mint 31)] ->
    (exists (gvs : GVs),
       (exists (tr : events.trace), opsem.Opsem.s_converges llvm_system main_fn [$ v0 # typ_int 32 $; $ v1 # typ_int 32 $] tr gvs) /\
       (GVsSig.(opsem.instantiate_gvs) gv gvs)) ->
    (exists (cv0 cv1  : expr global.zero),
       (llvm_value_to_core_value v0 = Some cv0) /\
       (llvm_value_to_core_value v1 = Some cv1) /\
       ((exists (cv : expr global.zero),
           (llvm_value_to_core_value gv = Some cv) /\
           (core_converges core_file [cv0; cv1] cv)) \/
        (core_undefined core_file [cv0; cv1]))).
Proof.
  intros ? ? ? ? ? H0 H1 H.
  pose proof (core_converges_to_thevalue _ _ _ _ H0 H1) as H'.
  decompose_ex H'.
  decompose [and] H'; clear H'.
  exists cv0.
  exists cv1.
  repeat split; try assumption.
  left.
  exists cv.
  eapply llvm_converges_only_to_thevalue in H; try eassumption.
  subst gv.
  split; assumption.
Qed.

Lemma llvm_does_not_diverge :
  forall v0 i0 v1 i1,
    eq v0 [(Values.Vint 31 i0, AST.Mint 31)] ->
    eq v1 [(Values.Vint 31 i1, AST.Mint 31)] ->
    ~(exists (tr : events.traceinf), @opsem.Opsem.s_diverges GVsSig llvm_system main_fn [$ v0 # typ_int 32 $; $ v1 # typ_int 32 $] tr).
Proof.
  intros ? ? ? ? H0' H1' [? H].
  inversion H as [? ? ? ? ? ? H'' H']; clear H.
  destruct_initState (initState_good _ _ _ _ _ _ H0' H1' H'').

  subst.
  apply opsem_props.OpsemProps.sop_diverges__sop_diverges' in H'. (* we want to work with sInsn, not sop_plus *)
  repeat (single_basic_block_does_not_diverge; try (simplify_br_uncond; single_basic_block_does_not_diverge)).
Qed.

Theorem core_diverges_if_llvm_diverges :
  forall v0 i0 v1 i1,
    eq v0 [(Values.Vint 31 i0, AST.Mint 31)] ->
    eq v1 [(Values.Vint 31 i1, AST.Mint 31)] ->
    (exists (tr : events.traceinf), @opsem.Opsem.s_diverges GVsSig llvm_system main_fn [$ v0 # typ_int 32 $; $ v1 # typ_int 32 $] tr) ->
    (exists (cv0 cv1 : expr global.zero),
       (llvm_value_to_core_value v0 = Some cv0) /\
       (llvm_value_to_core_value v1 = Some cv1) /\
       ((core_diverges core_file [cv0; cv1]) \/
        (core_undefined core_file [cv0; cv1]))).
Proof.
  intros ? ? ? ? H0 H1 H.
  contradiction (llvm_does_not_diverge _ _ _ _ H0 H1).
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "../coq" "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
