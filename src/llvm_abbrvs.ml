open Syntax

type location =
  | Loc_layouts of LLVMsyntax.layouts
  | Loc_products of LLVMsyntax.products
  | Loc_namedts of LLVMsyntax.namedts
  | Loc_block of LLVMsyntax.block
  | Loc_cmds of LLVMsyntax.cmds
  | Loc_terminator of LLVMsyntax.terminator
  | Loc_fdef of LLVMsyntax.fdef

let loc_layouts x = Loc_layouts x
let loc_products x = Loc_products x
let loc_namedts x = Loc_namedts x
let loc_block x = Loc_block x
let loc_cmds x = Loc_cmds x
let loc_terminator x = Loc_terminator x
let loc_fdef x = Loc_fdef x

type abbrvs = (location * string) list

let empty_abbrvs = []

let add_abbrv loc name abbrvs = (loc, name)::abbrvs

let location_eq a b =
  match (a, b) with
    | (Loc_layouts x, Loc_layouts y) -> x == y
    | (Loc_products x, Loc_products y) -> x == y
    | (Loc_namedts x, Loc_namedts y) -> x == y
    | (Loc_block x, Loc_block y) -> x == y
    | (Loc_cmds x, Loc_cmds y) -> x == y
    | (Loc_terminator x, Loc_terminator y) -> x == y
    | (Loc_fdef x, Loc_fdef y) -> x == y
    | _ -> false

let rec find_abbrv abbrvs loc =
  match abbrvs with
    | [] -> None
    | ((x, y)::xs) -> if location_eq x loc then Some y else find_abbrv xs loc
