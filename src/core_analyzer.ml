open Behaviour
open Printf
open Utils

let string_of_expr e =
  let buf = Buffer.create 16 in
  let isatty = !Pp_core.isatty in
  Pp_core.isatty := false;
  PPrint.ToBuffer.pretty 80.0 40 buf (Pp_core.pp_expr e);
  Pp_core.isatty := isatty;
  Buffer.contents buf

let eq_constant c1 c2 =
  Cmm_aux.instance_Basic_classes_SetType_Cmm_aux_constant_dict.Lem_pervasives.setElemCompare_method c1 c2 = 0

let eq_location (syms1, l1) (syms2, l2) =
 syms1 = syms2 && Cmm_aux.location_Equal l1 l2

open Core
let rec eq_expr e1 e2 =
  match (e1, e2) with
    | (Enull, Enull) -> true
    | (Etrue, Etrue) -> true
    | (Efalse, Efalse) -> true
    | (Econst c1, Econst c2) -> eq_constant c1 c2
    | (Ectype ct1, Ectype ct2) -> ct1 = ct2
    | (Eaddr addr1, Eaddr addr2) -> eq_location addr1 addr2
    | (Esym sym1, Esym sym2) -> sym1 = sym2
    | (Eimpl const1, Eimpl const2) -> const1 = const2
    | (Etuple exprs1, Etuple exprs2) -> eq_exprs exprs1 exprs2
    | (Enot expr1, Enot expr2) -> eq_expr expr1 expr2
    | (Eop (binop1, expr1a, expr1b), Eop (binop2, expr2a, expr2b)) -> binop1 = binop2 && eq_expr expr1a expr2a && eq_expr expr1b expr2b
    | (Ecall (name1, exprs1), Ecall (name2, exprs2)) -> name1 = name2 && eq_exprs exprs1 exprs2
    | (Eundef undef1, Eundef undef2) -> undef1 = undef2
    | (Eerror, Eerror) -> true
    | (Eskip, Eskip) -> true
    | (Elet (sym1, expr1a, expr1b), Elet (sym2, expr2a, expr2b)) -> sym1 = sym2 && eq_expr expr1a expr2a && eq_expr expr1b expr2b
    | (Eif (expr1a, expr1b, expr1c), Eif (expr2a, expr2b, expr2c)) -> eq_expr expr1a expr2a && eq_expr expr1b expr2b && eq_expr expr1c expr2c
    | (Eproc (xs1, name1, exprs1), Eproc (xs2, name2, exprs2)) -> (* Pset.equal xs1 xs2 && *) name1 = name2 && eq_exprs exprs1 exprs2
    | (Esame (expr1a, expr1b), Esame (expr2a, expr2b)) -> eq_expr expr1a expr2a && eq_expr expr1b expr2b
    | (Eaction pa1, Eaction pa2) -> eq_paction pa1 pa2
    | (Eunseq exprs1, Eunseq exprs2) -> eq_exprs exprs1 exprs2
    | (Ewseq (syms1, expr1a, expr1b), Ewseq (syms2, expr2a, expr2b)) -> syms1 = syms2 && eq_expr expr1a expr2a && eq_expr expr1b expr2b
    | (Esseq (syms1, expr1a, expr1b), Esseq (syms2, expr2a, expr2b)) -> syms1 = syms2 && eq_expr expr1a expr2a && eq_expr expr1b expr2b
    | (Easeq (sym1, a1, pa1), Easeq (sym2, a2, pa2)) -> sym1 = sym2 && eq_action a1 a2 && eq_paction pa1 pa2
    | (Eindet expr1, Eindet expr2) -> eq_expr expr1 expr2
    | (Ebound (bint1, expr1), Ebound (bint2, expr2)) -> bint1 = bint2 && eq_expr expr1 expr2
    | (Esave (ksym1, sym_ctypes1, expr1), Esave (ksym2, sym_ctypes2, expr2)) -> ksym1 = ksym2 && sym_ctypes1 = sym_ctypes2 && eq_expr expr1 expr2
    | (Erun (xs1, ksym1, sym_exprs1), Erun (xs2, ksym2, sym_exprs2)) -> (* Pset.equal xs1 xs2 && *) ksym1 = ksym2 && eq_sym_exprs sym_exprs1 sym_exprs2
    | (Eret expr1, Eret expr2) -> eq_expr expr1 expr2
    | (End exprs1, End exprs2) -> eq_exprs exprs1 exprs2
    | (Epar exprs1, Epar exprs2) -> eq_exprs exprs1 exprs2
    | (Eshift (expr1a, expr1b), Eshift (expr2a, expr2b)) -> eq_expr expr1a expr2a && eq_expr expr1b expr2b
    | (Eis_scalar expr1, Eis_scalar expr2) -> eq_expr expr1 expr2
    | (Eis_integer expr1, Eis_integer expr2) -> eq_expr expr1 expr2
    | (Eis_signed expr1, Eis_signed expr2) -> eq_expr expr1 expr2
    | (Eis_unsigned expr1, Eis_unsigned expr2) -> eq_expr expr1 expr2
    | _ -> false

and eq_exprs exprs1 exprs2 = List.length exprs1 = List.length exprs2 && List.for_all2 eq_expr exprs1 exprs2

and eq_sym_expr (sym1, expr1) (sym2, expr2) = sym1 = sym2 && eq_expr expr1 expr2

and eq_sym_exprs sym_exprs1 sym_exprs2 = List.length sym_exprs1 = List.length sym_exprs2 && List.for_all2 eq_sym_expr sym_exprs1 sym_exprs2

and eq_action_ a1 a2 =
  match (a1, a2) with
    | (Create0 (expr1, syms1), Create0 (expr2, syms2)) -> eq_expr expr1 expr2 && syms1 = syms2
    | (Alloc (expr1, syms1), Alloc (expr2, syms2)) -> eq_expr expr1 expr2 && syms1 = syms2
    | (Kill0 expr1, Kill0 expr2) -> eq_expr expr1 expr2
    | (Store0 (expr1a, expr1b, expr1c, mo1), Store0 (expr2a, expr2b, expr2c, mo2)) -> eq_expr expr1a expr2a && eq_expr expr1b expr2b && eq_expr expr1c expr2c && mo1 = mo2
    | (Load0 (expr1a, expr1b, mo1), Load0 (expr2a, expr2b, mo2)) -> eq_expr expr1a expr2a && eq_expr expr1b expr2b && mo1 = mo2
    | (CompareExchangeStrong (expr1a, expr1b, expr1c, expr1d, mo1a, mo1b), CompareExchangeStrong (expr2a, expr2b, expr2c, expr2d, mo2a, mo2b)) -> eq_expr expr1a expr2a && eq_expr expr1b expr2b && eq_expr expr1c expr2c && eq_expr expr1d expr2d && mo1a = mo2a && mo1b = mo2b
    | (CompareExchangeWeak (expr1a, expr1b, expr1c, expr1d, mo1a, mo1b), CompareExchangeWeak (expr2a, expr2b, expr2c, expr2d, mo2a, mo2b)) -> eq_expr expr1a expr2a && eq_expr expr1b expr2b && eq_expr expr1c expr2c && eq_expr expr1d expr2d && mo1a = mo2a && mo1b = mo2b
    | _ -> false

and eq_action (Action (_, act1)) (Action (_, act2)) = eq_action_ act1 act2
and eq_paction (Paction (p1, act1)) (Paction (p2, act2)) = eq_action act1 act2 && p1 = p2

open Core_run
let eq_cont k1 k2 =
  match (k1, k2) with
  | (Kunseq (exprs1a, exprs1b), Kunseq (exprs2a, exprs2b)) -> eq_exprs exprs1a exprs2a && eq_exprs exprs1b exprs2b
  | (Kpar (exprs1a, exprs1b), Kpar (exprs2a, exprs2b)) -> eq_exprs exprs1a exprs2a && eq_exprs exprs1b exprs2b
  | (Kwseq (syms1, expr1), Kwseq (syms2, expr2)) -> syms1 = syms2 && eq_expr expr1 expr2
  | (Ksseq (syms1, expr1), Ksseq (syms2, expr2)) -> syms1 = syms2 && eq_expr expr1 expr2
  | _ -> false

let eq_conts ks1 ks2 = List.length ks1 = List.length ks2 && List.for_all2 eq_cont ks1 ks2
let eq_contss ks1 ks2 = List.length ks1 = List.length ks2 && List.for_all2 eq_conts ks1 ks2

let eq_expr_conts (e1, ks1) (e2, ks2) = eq_expr e1 e2 && eq_contss ks1 ks2

let eq_by_using eqf f x y = eqf (f x) (f y)

let bind reducer i ms f = (fun st ->
  List.concat (List.map (function
    | (U.Defined0 x, st') -> f x st'
    | (U.Undef u,    st') -> [((i, U.Undef u), st')]
    | (U.Error,      st') -> [((i, U.Error),   st')]
  ) (reducer (ms st))))
let return i x = (fun st -> [((i, U.return2 x), st)])

let rec star_red2 reducer i visited_exprs ((e, _, ks) as x) =
  if ks == [] && Core_aux.is_value0 e
  then return i (Either.Left e)
  else
    let here = ((e, ks), i) in
    try
      (* XXX We do not compare the state at all, and therefore we will identify _any_ loop as divergent! *)
      let (_, start) = List.find (eq_by_using eq_expr_conts fst here) visited_exprs in
      return i (Either.Right start)
    with
      | Not_found ->
        bind reducer i (Core_run.red2 x) (star_red2 reducer (i + 1) (here :: visited_exprs))

let determine_behaviour core_file assume_deterministic =
  (* XXX We need to pass (symbolic) parameters to the main function, and do symbolic execution. *)

  let (_, main_params, _) = fromSome (Pmap.lookup core_file.main core_file.funs) in
  let args = List.map (fun _ -> Core.Econst (Cmm_aux.Cint Big_int.unit_big_int)) main_params in
  let (e, state) = Core_run.initial_expr_and_state_with_args Core_run_effect.Exhaustive core_file args in
  let reducer = if assume_deterministic then (fun xs -> [List.hd xs]) else (fun xs -> xs) in
  let results = star_red2 reducer 0 [] e state in

  let result_to_behaviour (n, result) =
    match result with
      | Undefined.Defined0 (Either.Left v) ->
        (match v with
          | Core.Econst (Cmm_aux.Cint i) -> (n, Converges (Ret_int i))
          | expr ->
            failwith ("Executing core program resulted in a non-integer value: " ^ string_of_expr expr))
      | Undefined.Defined0 (Either.Right start) -> (n, Diverges start)
      | Undefined.Undef _ -> (n, Undefined)
      | Undefined.Error ->
        failwith "Executing core program resulted in a runtime type error" in

  let behaviours = unique eq_behaviour compare_behaviour (List.map result_to_behaviour (List.map fst results)) in
(*  fprintf stderr "%d results; %d behaviours\n" (List.length results) (List.length behaviours); *)

  match behaviours with
    | [] -> failwith "Core program has no behaviour!"
    | [b] -> (b, true)
    | _ ->
      match List.filter isundefined behaviours with
        | [] -> failwith "Core program is non-deterministic"
          (* XXX We need to be able to handle non-determinism *)
        | b::_ -> (b, false)
