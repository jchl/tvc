open Core
open Cmm_aux
open Symbol
open Core_abbrvs
open Utils

let visit_pair (f, g) (x, y) = f x; g y
let visit_triple (f, g, h) (x, y, z) = f x; g y; h z
let visit_list f xs = List.iter f xs
let visit_fmap f g m = Pmap.iter (fun k v -> f k; g v) m
let visit_option f x =
  match x with
    | None -> ()
    | Some y -> f y

let visit_sym ref_abbrvs (Symbol (n, s) as sym) =
  match find_abbrv !ref_abbrvs (Loc_sym sym) with
    | Some a -> ()
    | None -> let suffix =
                match s with
                  | None -> ""
                  | Some name -> "'" ^ name in
              ref_abbrvs := (Loc_sym sym, "sym_" ^ string_of_int n ^ suffix) :: !ref_abbrvs

let visit_ksym = visit_sym

let visit_constant ref_abbrvs c =
  match c with
    | Cfunction sym -> visit_sym ref_abbrvs sym
    | _ -> ()

let visit_mem_addr ref_abbrvs (syms, _) =
  visit_list (visit_sym ref_abbrvs) syms

let visit_name ref_abbrvs n =
  match n with
    | Sym sym -> visit_sym ref_abbrvs sym
    | _ -> ()

let rec visit_expr ref_abbrvs e =
  match e with
    | Econst c -> visit_constant ref_abbrvs c
    | Eaddr addr -> visit_mem_addr ref_abbrvs addr
    | Esym s -> visit_sym ref_abbrvs s
    | Etuple exprs -> visit_list (visit_expr ref_abbrvs) exprs
    | Enot expr -> visit_expr ref_abbrvs expr
    | Eop (binop, expr1, expr2) -> visit_expr ref_abbrvs expr1; visit_expr ref_abbrvs expr2
    | Ecall (name, exprs) -> visit_name ref_abbrvs name; visit_list (visit_expr ref_abbrvs) exprs
    | Elet (sym, expr1, expr2) -> visit_sym ref_abbrvs sym; visit_expr ref_abbrvs expr1; visit_expr ref_abbrvs expr2
    | Eif (expr1, expr2, expr3) -> visit_expr ref_abbrvs expr1; visit_expr ref_abbrvs expr2; visit_expr ref_abbrvs expr3
    | Eproc (set, name, exprs) -> visit_name ref_abbrvs name; visit_list (visit_expr ref_abbrvs) exprs
    | Esame (expr1, expr2) -> visit_expr ref_abbrvs expr1; visit_expr ref_abbrvs expr2
    | Eaction pa -> visit_paction ref_abbrvs pa
    | Eunseq exprs -> visit_list (visit_expr ref_abbrvs) exprs
    | Ewseq (syms, expr1, expr2) -> visit_list (visit_option (visit_sym ref_abbrvs)) syms; visit_expr ref_abbrvs expr1; visit_expr ref_abbrvs expr2
    | Esseq (syms, expr1, expr2) -> visit_list (visit_option (visit_sym ref_abbrvs)) syms; visit_expr ref_abbrvs expr1; visit_expr ref_abbrvs expr2
    | Easeq (sym, a, pa) -> visit_option (visit_sym ref_abbrvs) sym; visit_action ref_abbrvs a; visit_paction ref_abbrvs pa
    | Eindet expr -> visit_expr ref_abbrvs expr
    | Ebound (bint, expr) -> visit_expr ref_abbrvs expr
    | Esave (ksym, sym_ctypes, expr) -> visit_ksym ref_abbrvs ksym; visit_expr ref_abbrvs expr
    | Erun (set, ksym, sym_exprs) -> visit_ksym ref_abbrvs ksym; visit_list (visit_pair (visit_sym ref_abbrvs, visit_expr ref_abbrvs)) sym_exprs
    | Eret expr -> visit_expr ref_abbrvs expr
    | End exprs -> visit_list (visit_expr ref_abbrvs) exprs
    | Epar exprs -> visit_list (visit_expr ref_abbrvs) exprs
    | Eshift (expr1, expr2) -> visit_expr ref_abbrvs expr1; visit_expr ref_abbrvs expr2
    | Eis_scalar expr -> visit_expr ref_abbrvs expr
    | Eis_integer expr -> visit_expr ref_abbrvs expr
    | Eis_signed expr -> visit_expr ref_abbrvs expr
    | Eis_unsigned expr -> visit_expr ref_abbrvs expr
    | _ -> ()

and visit_action_ ref_abbrvs a =
  match a with
    | Create0 (expr, syms) -> visit_expr ref_abbrvs expr; visit_list (visit_sym ref_abbrvs) syms
    | Alloc (expr, syms) -> visit_expr ref_abbrvs expr; visit_list (visit_sym ref_abbrvs) syms
    | Kill0 expr -> visit_expr ref_abbrvs expr
    | Store0 (expr1, expr2, expr3, mo) -> visit_expr ref_abbrvs expr1; visit_expr ref_abbrvs expr2; visit_expr ref_abbrvs expr3
    | Load0 (expr1, expr2, mo) -> visit_expr ref_abbrvs expr1; visit_expr ref_abbrvs expr2
    | CompareExchangeStrong (expr1, expr2, expr3, expr4, mo1, mo2) -> visit_expr ref_abbrvs expr1; visit_expr ref_abbrvs expr2; visit_expr ref_abbrvs expr3; visit_expr ref_abbrvs expr4
    | CompareExchangeWeak (expr1, expr2, expr3, expr4, mo1, mo2) -> visit_expr ref_abbrvs expr1; visit_expr ref_abbrvs expr2; visit_expr ref_abbrvs expr3; visit_expr ref_abbrvs expr4

and visit_action ref_abbrvs (Action (aset, act)) = visit_action_ ref_abbrvs act
and visit_paction ref_abbrvs (Paction (p, act)) = visit_action ref_abbrvs act

let visit_fun_map ref_abbrvs fs =
  Pmap.iter (fun (Symbol (_, name) as sym) ((_, sym_cbt_s, e) as func) -> visit_sym ref_abbrvs sym; visit_list (visit_pair (visit_sym ref_abbrvs, ignore)) sym_cbt_s; visit_expr ref_abbrvs e; ref_abbrvs := (Loc_fun func, "func_" ^ fromSome name)::(!ref_abbrvs)) fs

let visit_impl_decl ref_abbrvs id =
  match id with
    | Def (cbt, expr) -> visit_expr ref_abbrvs expr
    | IFun (cbt, sym_cbts, expr) -> visit_list (visit_pair (visit_sym ref_abbrvs, ignore)) sym_cbts; visit_expr ref_abbrvs expr

let visit_impl ref_abbrvs impl =
  Pmap.iter (fun ic impl_decl -> visit_impl_decl ref_abbrvs impl_decl; ref_abbrvs := (Loc_impl_decl impl_decl, "impl_" ^ tr '.' '_' (Implementation_.string_of_implementation_constant ic))::(!ref_abbrvs)) impl
