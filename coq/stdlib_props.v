(******************************************************************************)
(* Properties of the Core standard library.                                   *)
(******************************************************************************)

Require Import Csem.core.
Require Csem.core_aux.
Require Csem.core_run.
Require Import Csem.core_run_inductive.
Require Import Tvc.base_tactics.
Require Import Tvc.core_props.

(* Unfortunately, this axiom is completely false: call_function doesn't actually call the function!
It just substitutes the arguments into the function body. *)

(*
Axiom conv_int_identity_signed_int :
  forall (T : Type) core_file i,
    (-2147483648 <= i <= 2147483647)%Z ->
    eq (core_run.call_function core_file (Sym (Symbol 3 (Some "conv_int")))
                               [Ectype (Basic0 (Integer (Signed Int_)));
                                 Econst (Cint i)])
       (@Econst T (Cint i)).
*)

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

Definition convert_stdlib (stdlib : fun_map global.zero) : fun_map taction_id :=
  fmap_map (fun x =>
              match x with
                | (ty_ret, args, fbody) => (ty_ret, args, core_run.convert_expr fbody)
              end) stdlib.

Definition converted_stdlib := convert_stdlib core_stdlib.

Definition convert_impl (impl : impl_ global.zero) : impl_ taction_id :=
  fmap_map (fun x =>
              match x with
                | Def bty e => Def bty (convert_expr e)
                | IFun bty args e => IFun bty args (convert_expr e)
              end) impl.

Definition converted_impl := convert_impl core_impl.

Lemma conv_int_identity_signed_int :
  forall i tid ks s,
    eq (stdlib (e.file s)) converted_stdlib ->
    eq (impl (e.file s)) converted_impl ->
    (-2147483648 <= i <= 2147483647)%Z ->
    star_red2_ind (((Ecall (Sym (Symbol 3 (Some "conv_int"))) [Ectype (Basic0 (Integer (Signed Int_))); Econst (Cint i)]), tid, ks), s)
                  (((Econst (Cint i)), tid, ks), s).
Proof.
  intros.

  unfold stdlib, impl, file in H, H0.
  destruct s.
  destruct file.
  subst.

  eapply star_red2_step.
  apply red2_intro.
  rewrite red2_is_red2_pure by reflexivity.
  rewrite red2_pure_is_eval by reflexivity.
  compute.
  left; reflexivity.

  eapply star_red2_step.
  apply red2_intro.
  rewrite red2_is_red2_pure by reflexivity.
  rewrite red2_pure_is_eval by reflexivity.
  compute.
  left; reflexivity.

  eapply star_red2_step.
  apply red2_intro.
  rewrite red2_is_red2_pure by reflexivity.
  rewrite red2_pure_is_eval by reflexivity.
  compute.
  left; reflexivity.

  eapply star_red2_step.
  apply red2_intro.
  rewrite red2_is_red2_pure by reflexivity.
  rewrite red2_pure_is_eval by reflexivity.
  unfold file.

  cbv delta [eval1].
  cbv beta.

(*  
  match goal with
    | |- In _ ?xs => match xs with
                       | [?x] => remember x as blah
                     end
  end.


  simpl.
  compute.
  left; reflexivity.
Qed.
*)
Admitted.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-impredicative-set" "-R" "." "Tvc" "-R" "../../csem/_coq" "Csem" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/ott" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/monads" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics" "-I" "../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4" "-I" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src" "-R" "../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories" "Equations" "-I" "~/lem/coq-lib") ***
*** End: ***
*)
