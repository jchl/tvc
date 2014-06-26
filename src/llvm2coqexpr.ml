open Syntax
open Coqgen
open Llvm_abbrvs

let maybe_visit ctr f abbrvs v =
  match find_abbrv abbrvs (ctr v) with
    | Some a -> ExAtom a
    | None -> f abbrvs v

let visit_list f abbrvs = Coqgen.visit_list (f abbrvs)
let visit_pair (f, g) abbrvs = Coqgen.visit_pair (f abbrvs, g abbrvs)
let visit_option f abbrvs = Coqgen.visit_option (f abbrvs)
let visit_int abbrvs = Coqgen.visit_int

let maybe_visit_list ctr f abbrvs v =
  let rec maybe_visit_list' acc ctr f abbrvs v =
    match find_abbrv abbrvs (ctr v) with
      | Some a ->
        (match acc with
          | [] -> ExAtom a
          | (x::[]) -> ExInfix (x, "::", ExAtom a)
          | _ -> ExApp [ExAtom "List.append"; ExList (List.rev acc); ExAtom a])
      | None ->
        match v with
          | [] -> ExList (List.rev acc)
          | (x::xs) -> maybe_visit_list' ((f abbrvs x)::acc) ctr f abbrvs xs in
  maybe_visit_list' [] ctr f abbrvs v

(*
  Other types that might make sense to treat as locations:
  const
  value
  attributes
  param
  clattrs
  params
  cmd
  phinode
  phinodes
  arg
  stmts
  args
  fnattrs
  fheader
  blocks
  gvar
  fdec
  product
  namedt
  coq_module
  insn
  modules
  ls
  insns
*)

type kind = Id | Label

let atoms = Hashtbl.create 0

let pos_int_re = Str.regexp "^[0-9]+$"
let pos_reg_re = Str.regexp "^%[0-9]+$"
let neg_reg_re = Str.regexp "^%-[0-9]+$"
let alpha_reg_re = Str.regexp "^%[a-zA-Z_][a-zA-Z_0-9]*+$"
let fn_name_re = Str.regexp "^@[a-zA-Z_][a-zA-Z_0-9]*$"

let make_atom k a =
  match k with
    | Label ->
      if Str.string_match pos_int_re a 0 then "l" ^ a
      else failwith "unexpected label format: " ^ a
    | Id ->
      if Str.string_match pos_reg_re a 0 then "r" ^ String.sub a 1 (String.length a - 1)
      else if Str.string_match neg_reg_re a 0 then "r'" ^ String.sub a 2 (String.length a - 2)
      else if Str.string_match alpha_reg_re a 0 then "r_" ^ String.sub a 1 (String.length a - 1)
      else if Str.string_match fn_name_re a 0 then "f_" ^ String.sub a 1 (String.length a - 1)
      else failwith "unexpected id format: " ^ a

let visit_atom abbrvs k a =
  if Hashtbl.mem atoms a
  then
    Hashtbl.find atoms a
  else
    let x = make_atom k a in
    Hashtbl.add atoms a x;
    x

let visit_id abbrvs id = ExAtom (visit_atom abbrvs Id id)
let visit_l abbrvs l = ExAtom (visit_atom abbrvs Label l)

let visit_floating_point abbrvs fp =
  match fp with
    | LLVMsyntax.Coq_fp_float -> ExAtom "fp_float"
    | LLVMsyntax.Coq_fp_double -> ExAtom "fp_double"
    | LLVMsyntax.Coq_fp_fp128 -> ExAtom "fp_fp128"
    | LLVMsyntax.Coq_fp_x86_fp80 -> ExAtom "fp_x86_fp80"
    | LLVMsyntax.Coq_fp_ppc_fp128 -> ExAtom "fp_ppc_fp128"

let visit_varg = visit_option visit_int

let rec visit_typ abbrvs ty =
  match ty with
    | LLVMsyntax.Coq_typ_int sz ->
      ExApp [ExAtom "typ_int"; visit_int abbrvs sz]
    | LLVMsyntax.Coq_typ_floatpoint fp ->
      ExApp [ExAtom "typ_floatpoint"; visit_floating_point abbrvs fp]
    | LLVMsyntax.Coq_typ_void ->
      ExAtom "typ_void"
    | LLVMsyntax.Coq_typ_label ->
      ExAtom "typ_label"
    | LLVMsyntax.Coq_typ_metadata ->
      ExAtom "typ_metadata"
    | LLVMsyntax.Coq_typ_array (sz, t) ->
      ExApp [ExAtom "typ_array"; visit_int abbrvs sz; visit_typ abbrvs t]
    | LLVMsyntax.Coq_typ_function (t, ts, va) ->
      ExApp [ExAtom "typ_function"; visit_typ abbrvs t; visit_list visit_typ abbrvs ts; visit_varg abbrvs va]
    | LLVMsyntax.Coq_typ_struct ts ->
      ExApp [ExAtom "typ_struct"; visit_list visit_typ abbrvs ts]
    | LLVMsyntax.Coq_typ_pointer t ->
      ExApp [ExAtom "typ_pointer"; visit_typ abbrvs t]
    | LLVMsyntax.Coq_typ_namedt id ->
      ExApp [ExAtom "typ_namedt"; visit_id abbrvs id]

let visit_bop abbrvs bop =
  match bop with
    | LLVMsyntax.Coq_bop_add -> ExAtom "bop_add"
    | LLVMsyntax.Coq_bop_sub -> ExAtom "bop_sub"
    | LLVMsyntax.Coq_bop_mul -> ExAtom "bop_mul"
    | LLVMsyntax.Coq_bop_udiv -> ExAtom "bop_udiv"
    | LLVMsyntax.Coq_bop_sdiv -> ExAtom "bop_sdiv"
    | LLVMsyntax.Coq_bop_urem -> ExAtom "bop_urem"
    | LLVMsyntax.Coq_bop_srem -> ExAtom "bop_srem"
    | LLVMsyntax.Coq_bop_shl -> ExAtom "bop_shl"
    | LLVMsyntax.Coq_bop_lshr -> ExAtom "bop_lshr"
    | LLVMsyntax.Coq_bop_ashr -> ExAtom "bop_ashr"
    | LLVMsyntax.Coq_bop_and -> ExAtom "bop_and"
    | LLVMsyntax.Coq_bop_or -> ExAtom "bop_or"
    | LLVMsyntax.Coq_bop_xor -> ExAtom "bop_xor"

let visit_fbop abbrvs fbop =
  match fbop with
    | LLVMsyntax.Coq_fbop_fadd -> ExAtom "fbop_fadd"
    | LLVMsyntax.Coq_fbop_fsub -> ExAtom "fbop_fsub"
    | LLVMsyntax.Coq_fbop_fmul -> ExAtom "fbop_fmul"
    | LLVMsyntax.Coq_fbop_fdiv -> ExAtom "fbop_fdiv"
    | LLVMsyntax.Coq_fbop_frem -> ExAtom "fbop_frem"

let visit_cond abbrvs cond =
  match cond with
    | LLVMsyntax.Coq_cond_eq -> ExAtom "cond_eq"
    | LLVMsyntax.Coq_cond_ne -> ExAtom "cond_ne"
    | LLVMsyntax.Coq_cond_ugt -> ExAtom "cond_ugt"
    | LLVMsyntax.Coq_cond_uge -> ExAtom "cond_uge"
    | LLVMsyntax.Coq_cond_ult -> ExAtom "cond_ult"
    | LLVMsyntax.Coq_cond_ule -> ExAtom "cond_ule"
    | LLVMsyntax.Coq_cond_sgt -> ExAtom "cond_sgt"
    | LLVMsyntax.Coq_cond_sge -> ExAtom "cond_sge"
    | LLVMsyntax.Coq_cond_slt -> ExAtom "cond_slt"
    | LLVMsyntax.Coq_cond_sle -> ExAtom "cond_sle"

let visit_fcond abbrvs fcond =
  match fcond with
    | LLVMsyntax.Coq_fcond_false -> ExAtom "fcond_false"
    | LLVMsyntax.Coq_fcond_oeq -> ExAtom "fcond_oeq"
    | LLVMsyntax.Coq_fcond_ogt -> ExAtom "fcond_ogt"
    | LLVMsyntax.Coq_fcond_oge -> ExAtom "fcond_oge"
    | LLVMsyntax.Coq_fcond_olt -> ExAtom "fcond_olt"
    | LLVMsyntax.Coq_fcond_ole -> ExAtom "fcond_ole"
    | LLVMsyntax.Coq_fcond_one -> ExAtom "fcond_one"
    | LLVMsyntax.Coq_fcond_ord -> ExAtom "fcond_ord"
    | LLVMsyntax.Coq_fcond_ueq -> ExAtom "fcond_ueq"
    | LLVMsyntax.Coq_fcond_ugt -> ExAtom "fcond_ugt"
    | LLVMsyntax.Coq_fcond_uge -> ExAtom "fcond_uge"
    | LLVMsyntax.Coq_fcond_ult -> ExAtom "fcond_ult"
    | LLVMsyntax.Coq_fcond_ule -> ExAtom "fcond_ule"
    | LLVMsyntax.Coq_fcond_une -> ExAtom "fcond_une"
    | LLVMsyntax.Coq_fcond_uno -> ExAtom "fcond_uno"
    | LLVMsyntax.Coq_fcond_true -> ExAtom "fcond_true"

let visit_extop abbrvs extop =
  match extop with
    | LLVMsyntax.Coq_extop_s -> ExAtom "extop_s"
    | LLVMsyntax.Coq_extop_z -> ExAtom "extop_z"
    | LLVMsyntax.Coq_extop_fp -> ExAtom "extop_fp"

let visit_castop abbrvs castop =
  match castop with
    | LLVMsyntax.Coq_castop_fptoui -> ExAtom "castop_fptoui"
    | LLVMsyntax.Coq_castop_fptosi -> ExAtom "castop_fptosi"
    | LLVMsyntax.Coq_castop_uitofp -> ExAtom "castop_uitofp"
    | LLVMsyntax.Coq_castop_sitofp -> ExAtom "castop_sitofp"
    | LLVMsyntax.Coq_castop_ptrtoint -> ExAtom "castop_ptrtoint"
    | LLVMsyntax.Coq_castop_inttoptr -> ExAtom "castop_inttoptr"
    | LLVMsyntax.Coq_castop_bitcast -> ExAtom "castop_bitcast"

let visit_truncop abbrvs truncop =
  match truncop with
    | LLVMsyntax.Coq_truncop_int -> ExAtom "truncop_int"
    | LLVMsyntax.Coq_truncop_fp -> ExAtom "truncop_fp"

let visit_inbounds abbrvs = visit_bool

let rec visit_constant abbrvs c =
  match c with
    | LLVMsyntax.Coq_const_zeroinitializer _ ->
      ExAtom "const_zeroinitializer"
    | LLVMsyntax.Coq_const_int (sz, i) ->
      ExApp [ExAtom "const_int"; visit_int abbrvs sz; ExAtom (Printf.sprintf "(%s)%%Z" (Llvm.APInt.to_string i))]
    | LLVMsyntax.Coq_const_floatpoint (fp, f) ->
      ExApp [ExAtom "const_floatpoint"; ExAtom (Llvm.APFloat.to_string f)]
    | LLVMsyntax.Coq_const_undef t ->
      ExApp [ExAtom "const_undef"; visit_typ abbrvs t]
    | LLVMsyntax.Coq_const_null t ->
      ExApp [ExAtom "const_null"; visit_typ abbrvs t]
    | LLVMsyntax.Coq_const_arr (t, cs) ->
      ExApp [ExAtom "const_arr"; visit_typ abbrvs t; visit_list_constant abbrvs cs]
    | LLVMsyntax.Coq_const_struct (t, cs) ->
      ExApp [ExAtom "const_struct"; visit_typ abbrvs t; visit_list_constant abbrvs cs]
    | LLVMsyntax.Coq_const_gid (t, id) ->
      ExApp [ExAtom "const_gid"; visit_typ abbrvs t; visit_id abbrvs id]
    | LLVMsyntax.Coq_const_truncop (op, c, t) ->
      ExApp [ExAtom "const_truncop"; visit_truncop abbrvs op; visit_constant abbrvs c; visit_typ abbrvs t]
    | LLVMsyntax.Coq_const_extop (op, c, t) ->
      ExApp [ExAtom "const_extop"; visit_extop abbrvs op; visit_constant abbrvs c; visit_typ abbrvs t]
    | LLVMsyntax.Coq_const_castop (op, c, t) ->
      ExApp [ExAtom "const_castop"; visit_castop abbrvs op; visit_constant abbrvs c; visit_typ abbrvs t]
    | LLVMsyntax.Coq_const_gep (ib, c, cs) ->
      ExApp [ExAtom "const_gep"; visit_inbounds abbrvs ib; visit_constant abbrvs c; visit_list_constant abbrvs cs]
    | LLVMsyntax.Coq_const_select (c0, c1, c2) ->
      ExApp [ExAtom "const_select"; visit_constant abbrvs c0; visit_constant abbrvs c1; visit_constant abbrvs c2]
    | LLVMsyntax.Coq_const_icmp (cond, c1, c2) ->
      ExApp [ExAtom "const_icmp"; visit_cond abbrvs cond; visit_constant abbrvs c1; visit_constant abbrvs c2]
    | LLVMsyntax.Coq_const_fcmp (cond, c1, c2) ->
      ExApp [ExAtom "const_fcmp"; visit_fcond abbrvs cond; visit_constant abbrvs c1; visit_constant abbrvs c2]
    | LLVMsyntax.Coq_const_extractvalue (c, cs) ->
      ExApp [ExAtom "const_extractvalue"; visit_constant abbrvs c; visit_list_constant abbrvs cs]
    | LLVMsyntax.Coq_const_insertvalue (c1, c2, cs) ->
      ExApp [ExAtom "const_insertvalue"; visit_constant abbrvs c1; visit_constant abbrvs c2; visit_list_constant abbrvs cs]
    | LLVMsyntax.Coq_const_bop (op, c1, c2) ->
      ExApp [ExAtom "const_bop"; visit_bop abbrvs op; visit_constant abbrvs c1; visit_constant abbrvs c2]
    | LLVMsyntax.Coq_const_fbop (op, c1, c2) ->
      ExApp [ExAtom "const_fbop"; visit_fbop abbrvs op; visit_constant abbrvs c1; visit_constant abbrvs c2]

and visit_list_constant abbrvs cs = visit_list visit_constant abbrvs cs

let visit_value abbrvs v =
  match v with
    | LLVMsyntax.Coq_value_id id ->
      ExApp [ExAtom "value_id"; visit_id abbrvs id]
    | LLVMsyntax.Coq_value_const c ->
      ExApp [ExAtom "value_const"; visit_constant abbrvs c]

let visit_attribute abbrvs attr =
  match attr with
    | LLVMsyntax.Coq_attribute_zext -> ExAtom "attribute_zext"
    | LLVMsyntax.Coq_attribute_sext -> ExAtom "attribute_sext"
    | LLVMsyntax.Coq_attribute_noreturn -> ExAtom "attribute_noreturn"
    | LLVMsyntax.Coq_attribute_inreg -> ExAtom "attribute_inreg"
    | LLVMsyntax.Coq_attribute_structret -> ExAtom "attribute_structret"
    | LLVMsyntax.Coq_attribute_nounwind -> ExAtom "attribute_nounwind"
    | LLVMsyntax.Coq_attribute_noalias -> ExAtom "attribute_noalias"
    | LLVMsyntax.Coq_attribute_byval -> ExAtom "attribute_byval"
    | LLVMsyntax.Coq_attribute_nest -> ExAtom "attribute_nest"
    | LLVMsyntax.Coq_attribute_readnone -> ExAtom "attribute_readnone"
    | LLVMsyntax.Coq_attribute_readonly -> ExAtom "attribute_readonly"
    | LLVMsyntax.Coq_attribute_noinline -> ExAtom "attribute_noinline"
    | LLVMsyntax.Coq_attribute_alwaysinline -> ExAtom "attribute_alwaysinline"
    | LLVMsyntax.Coq_attribute_optforsize -> ExAtom "attribute_optforsize"
    | LLVMsyntax.Coq_attribute_stackprotect -> ExAtom "attribute_stackprotect"
    | LLVMsyntax.Coq_attribute_stackprotectreq -> ExAtom "attribute_stackprotectreq"
    | LLVMsyntax.Coq_attribute_nocapture -> ExAtom "attribute_nocapture"
    | LLVMsyntax.Coq_attribute_noredzone -> ExAtom "attribute_noredzone"
    | LLVMsyntax.Coq_attribute_implicitfloat -> ExAtom "attribute_implicitfloat"
    | LLVMsyntax.Coq_attribute_naked -> ExAtom "attribute_naked"

let visit_attributes = visit_list visit_attribute
let visit_param = visit_pair (visit_pair (visit_typ, visit_attributes), visit_value)
let visit_params = visit_list visit_param
let visit_list_sz_value = visit_list (visit_pair (visit_int, visit_value))
let visit_list_value_l = visit_list (visit_pair (visit_value, visit_l))
let visit_args = visit_list (visit_pair (visit_pair (visit_typ, visit_attributes), visit_id))

let visit_terminator =
  let visit_terminator' abbrvs i =
    match i with
      | LLVMsyntax.Coq_insn_br (id, v, l1, l2) ->
        ExApp [ExAtom "insn_br"; visit_id abbrvs id; visit_value abbrvs v; visit_l abbrvs l1; visit_l abbrvs l2]
      | LLVMsyntax.Coq_insn_br_uncond (id, l) ->
        ExApp [ExAtom "insn_br_uncond"; visit_id abbrvs id; visit_l abbrvs l]
      | LLVMsyntax.Coq_insn_return (id, t, v) ->
        ExApp [ExAtom "insn_return"; visit_id abbrvs id; visit_typ abbrvs t; visit_value abbrvs v]
      | LLVMsyntax.Coq_insn_return_void id ->
        ExApp [ExAtom "insn_return_void"; visit_id abbrvs id]
      | LLVMsyntax.Coq_insn_unreachable id ->
        ExApp [ExAtom "insn_unreachable"; visit_id abbrvs id] in
  maybe_visit loc_terminator visit_terminator'

let visit_callconv abbrvs cc =
  match cc with
    | LLVMsyntax.Coq_callconv_ccc -> ExAtom "callconv_ccc"
    | LLVMsyntax.Coq_callconv_fast -> ExAtom "callconv_fast"
    | LLVMsyntax.Coq_callconv_cold -> ExAtom "callconv_cold"
    | LLVMsyntax.Coq_callconv_x86_stdcall -> ExAtom "callconv_x86_stdcall"
    | LLVMsyntax.Coq_callconv_x86_fastcall -> ExAtom "callconv_x86_fastcall"

let visit_clattrs abbrvs clattrs =
  match clattrs with
    | LLVMsyntax.Coq_clattrs_intro (tailc, cc, ra, ca) ->
      ExApp [ExAtom "clattrs_intro"; visit_bool tailc; visit_callconv abbrvs cc; visit_attributes abbrvs ra; visit_attributes abbrvs ca]

let visit_cmd abbrvs i =
  match i with
    | LLVMsyntax.Coq_insn_bop (id, bop, sz, v1, v2) ->
      ExApp [ExAtom "insn_bop"; visit_id abbrvs id; visit_bop abbrvs bop;
             visit_int abbrvs sz; visit_value abbrvs v1; visit_value abbrvs v2]
    | LLVMsyntax.Coq_insn_fbop (id, fbop, fp, v1, v2) ->
      ExApp [ExAtom "insn_fbop"; visit_id abbrvs id; visit_fbop abbrvs fbop;
             visit_floating_point abbrvs fp; visit_value abbrvs v1; visit_value abbrvs v2]
    | LLVMsyntax.Coq_insn_extractvalue (id, t, v, cs, t') ->
      ExApp [ExAtom "insn_extractvalue"; visit_id abbrvs id; visit_typ abbrvs t;
             visit_value abbrvs v; visit_list_constant abbrvs cs; visit_typ abbrvs t']
    | LLVMsyntax.Coq_insn_insertvalue (id, t1, v1, t2, v2, cs) ->
      ExApp [ExAtom "insn_insertvalue"; visit_id abbrvs id; visit_typ abbrvs t1;
             visit_value abbrvs v1; visit_typ abbrvs t2; visit_value abbrvs v2;
             visit_list_constant abbrvs cs]
    | LLVMsyntax.Coq_insn_malloc (id, t, v, align) ->
      ExApp [ExAtom "insn_malloc"; visit_id abbrvs id; visit_typ abbrvs t; visit_value abbrvs v; visit_int abbrvs align]
    | LLVMsyntax.Coq_insn_alloca (id, t, v, align) ->
      ExApp [ExAtom "insn_alloca"; visit_id abbrvs id; visit_typ abbrvs t; visit_value abbrvs v; visit_int abbrvs align]
    | LLVMsyntax.Coq_insn_free (id, t, v) ->
      ExApp [ExAtom "insn_free"; visit_id abbrvs id; visit_typ abbrvs t; visit_value abbrvs v]
    | LLVMsyntax.Coq_insn_load (id, t, v, a) ->
      ExApp [ExAtom "insn_load"; visit_id abbrvs id; visit_typ abbrvs t; visit_value abbrvs v; visit_int abbrvs a]
    | LLVMsyntax.Coq_insn_store (id, t, v1, v2, a) ->
      ExApp [ExAtom "insn_store"; visit_id abbrvs id; visit_typ abbrvs t;
             visit_value abbrvs v1; visit_value abbrvs v2; visit_int abbrvs a]
    | LLVMsyntax.Coq_insn_gep (id, inbounds, t, v, vs, t') ->
      ExApp [ExAtom "insn_gep"; visit_id abbrvs id; visit_bool inbounds;
             visit_typ abbrvs t; visit_value abbrvs v; visit_list_sz_value abbrvs vs; visit_typ abbrvs t']
    | LLVMsyntax.Coq_insn_trunc (id, truncop, t1, v, t2) ->
      ExApp [ExAtom "insn_trunc"; visit_id abbrvs id; visit_truncop abbrvs truncop;
             visit_typ abbrvs t1; visit_value abbrvs v; visit_typ abbrvs t2]
    | LLVMsyntax.Coq_insn_ext (id, extop, t1, v, t2) ->
      ExApp [ExAtom "insn_ext"; visit_id abbrvs id; visit_extop abbrvs extop;
             visit_typ abbrvs t1; visit_value abbrvs v; visit_typ abbrvs t2]
    | LLVMsyntax.Coq_insn_cast (id, castop, t1, v, t2) ->
      ExApp [ExAtom "insn_cast"; visit_id abbrvs id; visit_castop abbrvs castop;
             visit_typ abbrvs t1; visit_value abbrvs v; visit_typ abbrvs t2]
    | LLVMsyntax.Coq_insn_icmp (id, cond, t, v1, v2) ->
      ExApp [ExAtom "insn_icmp"; visit_id abbrvs id; visit_cond abbrvs cond;
             visit_typ abbrvs t; visit_value abbrvs v1; visit_value abbrvs v2]
    | LLVMsyntax.Coq_insn_fcmp (id, fcond, fp, v1, v2) ->
      ExApp [ExAtom "insn_fcmp"; visit_id abbrvs id; visit_fcond abbrvs fcond;
             visit_floating_point abbrvs fp; visit_value abbrvs v1; visit_value abbrvs v2]
    | LLVMsyntax.Coq_insn_select (id, v, t, v1, v2) ->
      ExApp [ExAtom "insn_select"; visit_id abbrvs id; visit_value abbrvs v;
             visit_typ abbrvs t; visit_value abbrvs v1; visit_value abbrvs v2]
    | LLVMsyntax.Coq_insn_call (id, noret, clattrs, t, va, fv, ps) ->
      ExApp [ExAtom "insn_call"; visit_id abbrvs id; visit_bool noret;
             visit_clattrs abbrvs clattrs; visit_typ abbrvs t; visit_varg abbrvs va;
             visit_value abbrvs fv; visit_params abbrvs ps]

let visit_cmds =
  maybe_visit_list loc_cmds visit_cmd

let visit_phi abbrvs i =
  match i with
    | LLVMsyntax.Coq_insn_phi (id, t, list_v_l) ->
      ExApp [ExAtom "insn_phi"; visit_id abbrvs id; visit_typ abbrvs t; visit_list_value_l abbrvs list_v_l]

let visit_stmts abbrvs s =
  match s with
    | LLVMsyntax.Coq_stmts_intro (ps, cs, tmn) ->
      ExApp [ExAtom "stmts_intro"; visit_list visit_phi abbrvs ps; visit_cmds abbrvs cs; visit_terminator abbrvs tmn]

let visit_block =
  maybe_visit loc_block (visit_pair (visit_l, visit_stmts))

let visit_intrinsic_id abbrvs id =
  match id with
    | LLVMsyntax.Coq_iid_expect -> ExAtom "iid_expect"
    | LLVMsyntax.Coq_iid_setjmp -> ExAtom "iid_setjmp"
    | LLVMsyntax.Coq_iid_sigsetjmp -> ExAtom "iid_sigsetjmp"
    | LLVMsyntax.Coq_iid_longjmp -> ExAtom "iid_longjmp"
    | LLVMsyntax.Coq_iid_siglongjmp -> ExAtom "iid_siglongjmp"
    | LLVMsyntax.Coq_iid_ctpop -> ExAtom "iid_ctpop"
    | LLVMsyntax.Coq_iid_bswap -> ExAtom "iid_bswap"
    | LLVMsyntax.Coq_iid_ctlz -> ExAtom "iid_ctlz"
    | LLVMsyntax.Coq_iid_cttz -> ExAtom "iid_cttz"
    | LLVMsyntax.Coq_iid_stacksave -> ExAtom "iid_stacksave"
    | LLVMsyntax.Coq_iid_stackrestore -> ExAtom "iid_stackrestore"
    | LLVMsyntax.Coq_iid_returnaddress -> ExAtom "iid_returnaddress"
    | LLVMsyntax.Coq_iid_frameaddress -> ExAtom "iid_frameaddress"
    | LLVMsyntax.Coq_iid_prefetch -> ExAtom "iid_prefetch"
    | LLVMsyntax.Coq_iid_pcmarker -> ExAtom "iid_pcmarker"
    | LLVMsyntax.Coq_iid_readcyclecounter -> ExAtom "iid_readcyclecounter"
    | LLVMsyntax.Coq_iid_dbg_declare -> ExAtom "iid_dbg_declare"
    | LLVMsyntax.Coq_iid_eh_exception -> ExAtom "iid_eh_exception"
    | LLVMsyntax.Coq_iid_eh_selector -> ExAtom "iid_eh_selector"
    | LLVMsyntax.Coq_iid_eh_typeidfor -> ExAtom "iid_eh_typeidfor"
    | LLVMsyntax.Coq_iid_var_annotation -> ExAtom "iid_var_annotation"
    | LLVMsyntax.Coq_iid_memcpy -> ExAtom "iid_memcpy"
    | LLVMsyntax.Coq_iid_memmove -> ExAtom "iid_memmove"
    | LLVMsyntax.Coq_iid_memset -> ExAtom "iid_memset"
    | LLVMsyntax.Coq_iid_sqrt -> ExAtom "iid_sqrt"
    | LLVMsyntax.Coq_iid_log -> ExAtom "iid_log"
    | LLVMsyntax.Coq_iid_log2 -> ExAtom "iid_log2"
    | LLVMsyntax.Coq_iid_log10 -> ExAtom "iid_log10"
    | LLVMsyntax.Coq_iid_exp -> ExAtom "iid_exp"
    | LLVMsyntax.Coq_iid_exp2 -> ExAtom "iid_exp2"
    | LLVMsyntax.Coq_iid_pow -> ExAtom "iid_pow"
    | LLVMsyntax.Coq_iid_flt_rounds -> ExAtom "iid_flt_rounds"
    | LLVMsyntax.Coq_iid_invariantstart -> ExAtom "iid_invariantstart"
    | LLVMsyntax.Coq_iid_lifetimestart -> ExAtom "iid_lifetimestart"
    | LLVMsyntax.Coq_iid_invariantend -> ExAtom "iid_invariantend"
    | LLVMsyntax.Coq_iid_lifetimeend -> ExAtom "iid_lifetimeend"
    | LLVMsyntax.Coq_iid_unsupported -> ExAtom "iid_unsupported"

let visit_external_id abbrvs id =
  match id with
    | LLVMsyntax.Coq_eid_malloc -> ExAtom "eid_malloc"
    | LLVMsyntax.Coq_eid_free -> ExAtom "eid_free"
    | LLVMsyntax.Coq_eid_other -> ExAtom "eid_other"
    | LLVMsyntax.Coq_eid_io -> ExAtom "eid_io"

let visit_deckind abbrvs dck =
  match dck with
    | LLVMsyntax.Coq_deckind_intrinsic id ->
      ExApp [ExAtom "deckind_intrinsic"; visit_intrinsic_id abbrvs id]
    | LLVMsyntax.Coq_deckind_external id ->
      ExApp [ExAtom "deckind_external"; visit_external_id abbrvs id]

let visit_linkage abbrvs lk =
  match lk with
    | LLVMsyntax.Coq_linkage_external -> ExAtom "linkage_external"
    | LLVMsyntax.Coq_linkage_available_externally -> ExAtom "linkage_available_externally"
    | LLVMsyntax.Coq_linkage_link_once -> ExAtom "linkage_link_once"
    | LLVMsyntax.Coq_linkage_link_once_odr -> ExAtom "linkage_link_once_odr"
    | LLVMsyntax.Coq_linkage_weak -> ExAtom "linkage_weak"
    | LLVMsyntax.Coq_linkage_weak_odr -> ExAtom "linkage_weak_odr"
    | LLVMsyntax.Coq_linkage_appending -> ExAtom "linkage_appending"
    | LLVMsyntax.Coq_linkage_internal -> ExAtom "linkage_internal"
    | LLVMsyntax.Coq_linkage_private -> ExAtom "linkage_private"
    | LLVMsyntax.Coq_linkage_linker_private -> ExAtom "linkage_linker_private"
    | LLVMsyntax.Coq_linkage_dllimport -> ExAtom "linkage_dllimport"
    | LLVMsyntax.Coq_linkage_dllexport -> ExAtom "linkage_dllexport"
    | LLVMsyntax.Coq_linkage_external_weak -> ExAtom "linkage_external_weak"
    | LLVMsyntax.Coq_linkage_ghost -> ExAtom "linkage_ghost"
    | LLVMsyntax.Coq_linkage_common -> ExAtom "linkage_common"

let visit_visibility abbrvs vis =
  match vis with
    | LLVMsyntax.Coq_visibility_default -> ExAtom "visibility_default"
    | LLVMsyntax.Coq_visibility_hidden -> ExAtom "visibility_hidden"
    | LLVMsyntax.Coq_visibility_protected -> ExAtom "visibility_protected"

let visit_fnattrs abbrvs attrs =
  match attrs with
    | LLVMsyntax.Coq_fnattrs_intro (lk, vis, cc, attrs1, attrs2) ->
      ExApp [ExAtom "fnattrs_intro"; visit_linkage abbrvs lk; visit_visibility abbrvs vis; visit_callconv abbrvs cc;
             visit_attributes abbrvs attrs1; visit_attributes abbrvs attrs2]

let visit_fheader abbrvs h =
  match h with
    | LLVMsyntax.Coq_fheader_intro (attrs, t, id, args, va) ->
      ExApp [ExAtom "fheader_intro"; visit_fnattrs abbrvs attrs; visit_typ abbrvs t; visit_id abbrvs id; visit_args abbrvs args; visit_varg abbrvs va]

let visit_fdec abbrvs f =
  match f with
    | LLVMsyntax.Coq_fdec_intro (h, dck) ->
      ExApp [ExAtom "fdef_intro"; visit_fheader abbrvs h; visit_deckind abbrvs dck]

let visit_fdef =
  let visit_fdef' abbrvs f =
    match f with
      | LLVMsyntax.Coq_fdef_intro (h, bs) ->
        ExApp [ExAtom "fdef_intro"; visit_fheader abbrvs h; visit_list visit_block abbrvs bs] in
  maybe_visit loc_fdef visit_fdef'

let visit_gvar_spec abbrvs gs =
  match gs with
    | LLVMsyntax.Coq_gvar_spec_global -> ExAtom "gvar_spec_global"
    | LLVMsyntax.Coq_gvar_spec_constant -> ExAtom "gvar_spec_constant"

let visit_gvar abbrvs g =
  match g with
    | LLVMsyntax.Coq_gvar_intro (id, lk, spec, t, c, a) ->
      ExApp [ExAtom "gvar_intro"; visit_id abbrvs id; visit_linkage abbrvs lk; visit_gvar_spec abbrvs spec;
             visit_typ abbrvs t; visit_constant abbrvs c; visit_int abbrvs a]
    | LLVMsyntax.Coq_gvar_external (id, spec, t) ->
      ExApp [ExAtom "gvar_external"; visit_id abbrvs id; visit_gvar_spec abbrvs spec; visit_typ abbrvs t]

let visit_product abbrvs g =
  match g with
    | LLVMsyntax.Coq_product_gvar g ->
      ExApp [ExAtom "product_gvar"; visit_gvar abbrvs g]
    | LLVMsyntax.Coq_product_fdec f ->
      ExApp [ExAtom "product_fdec"; visit_fdec abbrvs f]
    | LLVMsyntax.Coq_product_fdef f ->
      ExApp [ExAtom "product_fdef"; visit_fdef abbrvs f]

let visit_products =
  maybe_visit_list loc_products visit_product

let visit_layout abbrvs dlt =
  match dlt with
    | LLVMsyntax.Coq_layout_be ->
      ExAtom "layout_be"
    | LLVMsyntax.Coq_layout_le ->
      ExAtom "layout_le"
    | LLVMsyntax.Coq_layout_ptr (sz, a1, a2) ->
      ExApp [ExAtom "layout_ptr"; visit_int abbrvs sz; visit_int abbrvs a1; visit_int abbrvs a2]
    | LLVMsyntax.Coq_layout_int (sz, a1, a2) ->
      ExApp [ExAtom "layout_int"; visit_int abbrvs sz; visit_int abbrvs a1; visit_int abbrvs a2]
    | LLVMsyntax.Coq_layout_float (sz, a1, a2) ->
      ExApp [ExAtom "layout_float"; visit_int abbrvs sz; visit_int abbrvs a1; visit_int abbrvs a2]
    | LLVMsyntax.Coq_layout_aggr (sz, a1, a2) ->
      ExApp [ExAtom "layout_aggr"; visit_int abbrvs sz; visit_int abbrvs a1; visit_int abbrvs a2]
    | LLVMsyntax.Coq_layout_stack (sz, a1, a2) ->
      ExApp [ExAtom "layout_stack"; visit_int abbrvs sz; visit_int abbrvs a1; visit_int abbrvs a2]
    | LLVMsyntax.Coq_layout_vector (sz, a1, a2) ->
      ExApp [ExAtom "layout_vector"; visit_int abbrvs sz; visit_int abbrvs a1; visit_int abbrvs a2]

let visit_layouts =
  maybe_visit_list loc_layouts visit_layout

let visit_namedt =
  visit_pair (visit_id, visit_list visit_typ)

let visit_namedts =
  maybe_visit_list loc_namedts visit_namedt

let visit_module abbrvs m =
  match m with
    | LLVMsyntax.Coq_module_intro (dlts, nts, ps) ->
      ExApp [ExAtom "module_intro";
             visit_layouts abbrvs dlts;
             visit_namedts abbrvs nts;
             visit_products abbrvs ps]
