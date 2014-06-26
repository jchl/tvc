open Core
open Core_ctype
open Symbol
open AilTypes
open Implementation_
open Undefined
open Cmm_csem
open Cmm_aux
open Coqgen
open Core_abbrvs

let maybe_visit ctr f abbrvs v =
  match find_abbrv abbrvs (ctr v) with
    | Some a -> ExAtom a
    | None -> f abbrvs v

let visit_list f abbrvs = Coqgen.visit_list (f abbrvs)
let visit_pair (f, g) abbrvs = Coqgen.visit_pair (f abbrvs, g abbrvs)
let visit_triple (f, g, h) abbrvs = Coqgen.visit_triple (f abbrvs, g abbrvs, h abbrvs)
let visit_option f abbrvs = Coqgen.visit_option (f abbrvs)
let visit_int abbrvs = Coqgen.visit_int
let visit_int abbrvs = Coqgen.visit_int
let visit_big_int abbrvs = Coqgen.visit_big_int
let visit_string abbrvs = Coqgen.visit_string

let visit_set f abbrvs set = ExList (Pset.fold (fun v acc -> (f abbrvs v)::acc) set [])
let visit_fmap f g abbrvs m = ExList (Pmap.fold (fun k v acc -> (ExTuple [f abbrvs k; g abbrvs v])::acc) m [])

let visit_zero abbrvs v = failwith "Unreachable"
let visit_aset abbrvs set = visit_set visit_zero abbrvs set

let rec visit_location abbrvs l =
  match l with
    | Lbase bint -> ExApp [ExAtom "Lbase"; visit_big_int abbrvs bint]
    | Lshift (l', bint) -> ExApp [ExAtom "Lshift"; visit_location abbrvs l'; visit_big_int abbrvs bint]

let rec visit_core_base_type abbrvs cbt =
  match cbt with
    | Integer0 -> ExAtom "Integer0"
    | Boolean -> ExAtom "Boolean"
    | Address -> ExAtom "Address"
    | Ctype -> ExAtom "Ctype"
    | CFunction -> ExAtom "CFunction"
    | Unit -> ExAtom "Unit"
    | Tuple cbts -> ExApp [ExAtom "Tuple"; visit_list visit_core_base_type abbrvs cbts]
    | Wildcard -> ExAtom "Wildcard"

let visit_core_type abbrvs ct =
  match ct with
    | TyBase cbt -> ExApp [ExAtom "TyBase"; visit_core_base_type abbrvs cbt]
    | TyEffect cbt -> ExApp [ExAtom "TyEffect"; visit_core_base_type abbrvs cbt]

let visit_sym =
  let visit_sym' abbrvs s =
    match s with
      | Symbol (int, s) -> ExApp [ExAtom "Symbol"; visit_int abbrvs int; visit_option visit_string abbrvs s] in
  maybe_visit loc_sym visit_sym'

let visit_ksym = visit_sym

let visit_constant abbrvs c =
  match c with
    | Cint bint -> ExApp [ExAtom "Cint"; visit_big_int abbrvs bint]
    | Cfunction sym -> ExApp [ExAtom "Cfunction"; visit_sym abbrvs sym]

let visit_integer_base_type abbrvs ibt =
  match ibt with
    | Ichar -> ExAtom "Ichar"
    | Short -> ExAtom "Short"
    | Int_ -> ExAtom "Int_"
    | Long -> ExAtom "Long"
    | LongLong -> ExAtom "LongLong"
    | Int8_t -> ExAtom "Int8_t"
    | Int16_t -> ExAtom "Int16_t"
    | Int32_t -> ExAtom "Int32_t"
    | Int64_t -> ExAtom "Int64_t"

let visit_integer_type abbrvs it =
  match it with
    | Char -> ExAtom "Char"
    | Bool -> ExAtom "Bool"
    | Signed ibt -> ExApp [ExAtom "Signed"; visit_integer_base_type abbrvs ibt]
    | Unsigned ibt -> ExApp [ExAtom "Unsigned"; visit_integer_base_type abbrvs ibt]

let visit_basic_type abbrvs bt =
  match bt with
    | Integer it -> ExApp [ExAtom "Integer"; visit_integer_type abbrvs it]

let visit_implementation_constant abbrvs c =
  match c with
    | Environment__startup_name -> ExAtom "Environment__startup_name"
    | Environment__startup_type -> ExAtom "Environment__startup_type"
    | Characters__bits_in_byte -> ExAtom "Characters__bits_in_byte"
    | Characters__execution_character_set_values -> ExAtom "Characters__execution_character_set_values"
    | Characters__TODO1 -> ExAtom "Characters__TODO1"
    | Characters__TODO2 -> ExAtom "Characters__TODO2"
    | Characters__plain_char_sign -> ExAtom "Characters__plain_char_sign"
    | Characters__TODO3 -> ExAtom "Characters__TODO3"
    | Characters__TODO4 -> ExAtom "Characters__TODO4"
    | Characters__TODO5 -> ExAtom "Characters__TODO5"
    | Characters__TODO6 -> ExAtom "Characters__TODO6"
    | Characters__TODO7 -> ExAtom "Characters__TODO7"
    | Characters__TODO8 -> ExAtom "Characters__TODO8"
    | Characters__TODO9 -> ExAtom "Characters__TODO9"
    | Characters__TODO10 -> ExAtom "Characters__TODO10"
    | Integer__encode -> ExAtom "Integer__encode"
    | Integer__decode -> ExAtom "Integer__decode"
    | Sizeof -> ExAtom "Sizeof"
    | Alignof -> ExAtom "Alignof"
    | SHR_signed_negative -> ExAtom "SHR_signed_negative"
    | Bitwise_complement -> ExAtom "Bitwise_complement"
    | Plain_bitfield_sign -> ExAtom "Plain_bitfield_sign"
    | Bitfield_other_types -> ExAtom "Bitfield_other_types"
    | Atomic_bitfield_permitted -> ExAtom "Atomic_bitfield_permitted"
    | Ctype_min -> ExAtom "Ctype_min"
    | Ctype_max -> ExAtom "Ctype_max"
    | StdFunction name -> ExApp [ExAtom "StdFunction"; visit_string abbrvs name]

let rec visit_ctype abbrvs c =
  match c with
    | Void0 -> ExAtom "Void0"
    | Basic0 bt -> ExApp [ExAtom "Basic0"; visit_basic_type abbrvs bt]
    | Array0 (ctype, bint) -> ExApp [ExAtom "Array0"; visit_ctype abbrvs ctype; visit_big_int abbrvs bint]
    | Function0 (ctype, ctypes, b) -> ExApp [ExAtom "Function0"; visit_ctype abbrvs ctype; visit_list visit_ctype abbrvs ctypes; visit_bool b]
    | Pointer0 ctype -> ExApp [ExAtom "Pointer0"; visit_ctype abbrvs ctype]
    | Atomic1 ctype -> ExApp [ExAtom "Atomic1"; visit_ctype abbrvs ctype]
    | SIZE_T -> ExAtom "SIZE_T"
    | INTPTR_T -> ExAtom "INTPTR_T"
    | WCHAR_T -> ExAtom "WCHAR_T"
    | CHAR16_T -> ExAtom "CHAR16_T"
    | CHAR32_T -> ExAtom "CHAR32_T"

let visit_mem_addr abbrvs = visit_pair (visit_list visit_sym, visit_location) abbrvs

let visit_undefined_behaviour abbrvs u =
  match u with
    | DUMMY -> ExAtom "DUMMY"
    | Outside_lifetime -> ExAtom "Outside_lifetime"
    | Data_race -> ExAtom "Data_race"
    | Unsequenced_race -> ExAtom "Unsequenced_race"
    | Exceptional_condition -> ExAtom "Exceptional_condition"
    | Illtyped_load -> ExAtom "Illtyped_load"
    | Access_atomic_structUnion_member -> ExAtom "Access_atomic_structUnion_member"
    | Indirection_invalid_value -> ExAtom "Indirection_invalid_value"
    | TODO_find_a_name -> ExAtom "TODO_find_a_name"
    | Division_by_zero -> ExAtom "Division_by_zero"
    | Modulo_by_zero -> ExAtom "Modulo_by_zero"
    | Array_pointer_addition_outside -> ExAtom "Array_pointer_addition_outside"
    | Array_pointer_subtraction_outside -> ExAtom "Array_pointer_subtraction_outside"
    | Array_pointer_addition_beyond_indirection -> ExAtom "Array_pointer_addition_beyond_indirection"
    | Array_pointer_substraction_beyond_indirection -> ExAtom "Array_pointer_substraction_beyond_indirection"
    | Disjoint_array_pointers_substraction -> ExAtom "Disjoint_array_pointers_substraction"
    | TODO_find_a_name5 -> ExAtom "TODO_find_a_name5"
    | Pointers_substraction_not_representable -> ExAtom "Pointers_substraction_not_representable"
    | Negative_shift -> ExAtom "Negative_shift"
    | Shift_too_large -> ExAtom "Shift_too_large"
    | Negative_left_shift -> ExAtom "Negative_left_shift"
    | Non_representable_left_shift -> ExAtom "Non_representable_left_shift"
    | Distinct_aggregate_union_pointer_comparison -> ExAtom "Distinct_aggregate_union_pointer_comparison"
    | TODO_find_a_name10 -> ExAtom "TODO_find_a_name10"
    | Pointer_to_dead_object -> ExAtom "Pointer_to_dead_object"
    | Use_indeterminate_automatic_object -> ExAtom "Use_indeterminate_automatic_object"
    | Lvalue_read_trap_representation -> ExAtom "Lvalue_read_trap_representation"
    | Lvalue_side_effect_trap_representation -> ExAtom "Lvalue_side_effect_trap_representation"
    | Unsupported_negative_zero -> ExAtom "Unsupported_negative_zero"
    | Lvalue_not_an_object -> ExAtom "Lvalue_not_an_object"
    | Illtyped_assert -> ExAtom "Illtyped_assert"
    | TODO_find_a_name12 -> ExAtom "TODO_find_a_name12"

let visit_memory_order abbrvs mo =
  match mo with
    | NA -> ExAtom "NA"
    | Seq_cst -> ExAtom "Seq_cst"
    | Relaxed -> ExAtom "Relaxed"
    | Release -> ExAtom "Release"
    | Acquire -> ExAtom "Acquire"
    | Consume -> ExAtom "Consume"
    | Acq_rel -> ExAtom "Acq_rel"

let visit_binop abbrvs b =
  match b with
    | OpAdd -> ExAtom "OpAdd"
    | OpSub -> ExAtom "OpSub"
    | OpMul -> ExAtom "OpMul"
    | OpDiv -> ExAtom "OpDiv"
    | OpMod -> ExAtom "OpMod"
    | OpEq -> ExAtom "OpEq"
    | OpLt -> ExAtom "OpLt"
    | OpAnd -> ExAtom "OpAnd"
    | OpOr -> ExAtom "OpOr"

let visit_polarity abbrvs p =
  match p with
    | Pos -> ExAtom "Pos"
    | Neg -> ExAtom "Neg"

let visit_name abbrvs n =
  match n with
    | Sym sym -> ExApp [ExAtom "Sym"; visit_sym abbrvs sym]
    | Impl const -> ExApp [ExAtom "Impl"; visit_implementation_constant abbrvs const]

let rec visit_expr abbrvs e =
  let visit_expr' abbrvs e =
    match e with
      | Enull -> ExAtom "Enull"
      | Etrue -> ExAtom "Etrue"
      | Efalse -> ExAtom "Efalse"
      | Econst c -> ExApp [ExAtom "Econst"; visit_constant abbrvs c]
      | Ectype ctype -> ExApp [ExAtom "Ectype"; visit_ctype abbrvs ctype]
      | Eaddr addr -> ExApp [ExAtom "Eaddr"; visit_mem_addr abbrvs addr]
      | Esym sym -> ExApp [ExAtom "Esym"; visit_sym abbrvs sym]
      | Eimpl const -> ExApp [ExAtom "Eimpl"; visit_implementation_constant abbrvs const]
      | Etuple exprs -> ExApp [ExAtom "Etuple"; visit_list visit_expr abbrvs exprs]
      | Enot expr -> ExApp [ExAtom "Enot"; visit_expr abbrvs expr]
      | Eop (binop, expr1, expr2) -> ExApp [ExAtom "Eop"; visit_binop abbrvs binop; visit_expr abbrvs expr1; visit_expr abbrvs expr2]
      | Ecall (name, exprs) -> ExApp [ExAtom "Ecall"; visit_name abbrvs name; visit_list visit_expr abbrvs exprs]
      | Eundef undef -> ExApp [ExAtom "Eundef"; visit_undefined_behaviour abbrvs undef]
      | Eerror -> ExAtom "Eerror"
      | Eskip -> ExAtom "Eskip"
      | Elet (sym, expr1, expr2) -> ExApp [ExAtom "Elet"; visit_sym abbrvs sym; visit_expr abbrvs expr1; visit_expr abbrvs expr2]
      | Eif (expr1, expr2, expr3) -> ExApp [ExAtom "Eif"; visit_expr abbrvs expr1; visit_expr abbrvs expr2; visit_expr abbrvs expr3]
      | Eproc (set, name, exprs) -> ExApp [ExAtom "Eproc"; visit_aset abbrvs set; visit_name abbrvs name; visit_list visit_expr abbrvs exprs]
      | Esame (expr1, expr2) -> ExApp [ExAtom "Esame"; visit_expr abbrvs expr1; visit_expr abbrvs expr2]
      | Eaction pa -> ExApp [ExAtom "Eaction"; visit_paction abbrvs pa]
      | Eunseq exprs -> ExApp [ExAtom "Eunseq"; visit_list visit_expr abbrvs exprs]
      | Ewseq (syms, expr1, expr2) -> ExApp [ExAtom "Ewseq"; visit_list (visit_option visit_sym) abbrvs syms; visit_expr abbrvs expr1; visit_expr abbrvs expr2]
      | Esseq (syms, expr1, expr2) -> ExApp [ExAtom "Esseq"; visit_list (visit_option visit_sym) abbrvs syms; visit_expr abbrvs expr1; visit_expr abbrvs expr2]
      | Easeq (sym, a, pa) -> ExApp [ExAtom "Easeq"; visit_option visit_sym abbrvs sym; visit_action abbrvs a; visit_paction abbrvs pa]
      | Eindet expr -> ExApp [ExAtom "Eindet"; visit_expr abbrvs expr]
      | Ebound (bint, expr) -> ExApp [ExAtom "Ebound"; visit_big_int abbrvs bint; visit_expr abbrvs expr]
      | Esave (ksym, sym_ctypes, expr) -> ExApp [ExAtom "Esave"; visit_ksym abbrvs ksym; visit_list (visit_pair (visit_sym, visit_ctype)) abbrvs sym_ctypes; visit_expr abbrvs expr]
      | Erun (set, ksym, sym_exprs) -> ExApp [ExAtom "Erun"; visit_aset abbrvs set; visit_ksym abbrvs ksym; visit_list (visit_pair (visit_sym, visit_expr)) abbrvs sym_exprs]
      | Eret expr -> ExApp [ExAtom "Eret"; visit_expr abbrvs expr]
      | End exprs -> ExApp [ExAtom "End"; visit_list visit_expr abbrvs exprs]
      | Epar exprs -> ExApp [ExAtom "Epar"; visit_list visit_expr abbrvs exprs]
      | Eshift (expr1, expr2) -> ExApp [ExAtom "Eshift"; visit_expr abbrvs expr1; visit_expr abbrvs expr2]
      | Eis_scalar expr -> ExApp [ExAtom "Eis_scalar"; visit_expr abbrvs expr]
      | Eis_integer expr -> ExApp [ExAtom "Eis_integer"; visit_expr abbrvs expr]
      | Eis_signed expr -> ExApp [ExAtom "Eis_signed"; visit_expr abbrvs expr]
      | Eis_unsigned expr -> ExApp [ExAtom "Eis_unsigned"; visit_expr abbrvs expr] in
  maybe_visit loc_expr visit_expr' abbrvs e

and visit_action_ abbrvs a =
  match a with
    | Create0 (expr, syms) -> ExApp [ExAtom "Create0"; visit_expr abbrvs expr; visit_list visit_sym abbrvs syms]
    | Alloc (expr, syms) -> ExApp [ExAtom "Alloc"; visit_expr abbrvs expr; visit_list visit_sym abbrvs syms]
    | Kill0 expr -> ExApp [ExAtom "Kill0"; visit_expr abbrvs expr]
    | Store0 (expr1, expr2, expr3, mo) -> ExApp [ExAtom "Store0"; visit_expr abbrvs expr1; visit_expr abbrvs expr2; visit_expr abbrvs expr3; visit_memory_order abbrvs mo]
    | Load0 (expr1, expr2, mo) -> ExApp [ExAtom "Load0"; visit_expr abbrvs expr1; visit_expr abbrvs expr2; visit_memory_order abbrvs mo]
    | CompareExchangeStrong (expr1, expr2, expr3, expr4, mo1, mo2) -> ExApp [ExAtom "CompareExchangeStrong"; visit_expr abbrvs expr1; visit_expr abbrvs expr2; visit_expr abbrvs expr3; visit_expr abbrvs expr4; visit_memory_order abbrvs mo1; visit_memory_order abbrvs mo2]
    | CompareExchangeWeak (expr1, expr2, expr3, expr4, mo1, mo2) -> ExApp [ExAtom "CompareExchangeWeak"; visit_expr abbrvs expr1; visit_expr abbrvs expr2; visit_expr abbrvs expr3; visit_expr abbrvs expr4; visit_memory_order abbrvs mo1; visit_memory_order abbrvs mo2]

and visit_action abbrvs (Action (aset, act)) = ExApp [ExAtom "Action"; visit_aset abbrvs aset; visit_action_ abbrvs act]
and visit_paction abbrvs (Paction (p, act)) = ExApp [ExAtom "Paction"; visit_polarity abbrvs p; visit_action abbrvs act]

let visit_fun =
  let visit_fun' =
    visit_triple (visit_core_type, visit_list (visit_pair (visit_sym, visit_core_base_type)), visit_expr) in
  maybe_visit loc_fun visit_fun'

let visit_fun_map =
  let visit_fun_map' abbrvs funs =
    visit_fmap visit_sym visit_fun abbrvs funs in
  maybe_visit loc_fun_map visit_fun_map'

let visit_impl_decl =
  let visit_impl_decl' abbrvs id =
    match id with
      | Def (cbt, expr) -> ExApp [ExAtom "Def"; visit_core_base_type abbrvs cbt; visit_expr abbrvs expr]
      | IFun (cbt, sym_cbts, expr) -> ExApp [ExAtom "IFun"; visit_core_base_type abbrvs cbt; visit_list (visit_pair (visit_sym, visit_core_base_type)) abbrvs sym_cbts; visit_expr abbrvs expr] in
  maybe_visit loc_impl_decl visit_impl_decl'

let visit_impl =
  let visit_impl' abbrvs impl =
    visit_fmap visit_implementation_constant visit_impl_decl abbrvs impl in
  maybe_visit loc_impl visit_impl'
