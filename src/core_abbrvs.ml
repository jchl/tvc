open Core

type location =
  | Loc_sym of sym
  | Loc_expr of Global.zero expr
  | Loc_fun of (core_type * ((sym * core_base_type) list) * Global.zero expr)
  | Loc_impl_decl of Global.zero impl_decl
  | Loc_fun_map of Global.zero fun_map
  | Loc_impl of Global.zero impl

let loc_sym x = Loc_sym x
let loc_expr x = Loc_expr x
let loc_fun x = Loc_fun x
let loc_impl_decl x = Loc_impl_decl x
let loc_fun_map x = Loc_fun_map x
let loc_impl x = Loc_impl x

type abbrvs = (location * string) list

let empty_abbrvs = []

let add_abbrv loc name abbrvs = (loc, name)::abbrvs

let location_eq a b =
  match (a, b) with
    | (Loc_sym x, Loc_sym y) -> x = y
    | (Loc_expr x, Loc_expr y) -> x == y (* note: physical equality! *)
    | (Loc_fun x, Loc_fun y) -> x == y (* note: physical equality! *)
    | (Loc_impl_decl x, Loc_impl_decl y) -> x == y (* note: physical equality! *)
    | (Loc_fun_map x, Loc_fun_map y) -> x == y (* note: physical equality! *)
    | (Loc_impl x, Loc_impl y) -> x == y (* note: physical equality! *)
    | _ -> false

let rec find_abbrv abbrvs loc =
  match abbrvs with
    | [] -> None
    | ((x, y)::xs) -> if location_eq x loc then Some y else find_abbrv xs loc
