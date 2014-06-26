open Printf
open Syntax
open Behaviour
open Utils

let ret_unsigned = ref false
let arg_unsigned = ref ([] : int list)

let fid_to_fn_name fid = tr '@' '_' fid

let output_block chan abbrvs fn_name i llvm_block =
  let (llvm_cmds, llvm_term) =
    match llvm_block with
      | (_, LLVMsyntax.Coq_stmts_intro (_, cmds, term)) -> (cmds, term) in

  revitertails (fun j cmds ->
    let name = sprintf "%s_cmds_%d_%i" fn_name i j in
    fprintf chan "Definition %s : list cmd :=\n" name;
    Coqgen.pp_expr chan (Llvm2coqexpr.visit_cmds !abbrvs cmds) 2;
    fprintf chan ".\n";
    abbrvs := Llvm_abbrvs.add_abbrv (Llvm_abbrvs.Loc_cmds cmds) name !abbrvs) llvm_cmds;
  fprintf chan "\n";

  let name = sprintf "%s_cmds_%d" fn_name i in
  fprintf chan "Definition %s : list cmd :=\n" name;
  Coqgen.pp_expr chan (Llvm2coqexpr.visit_cmds !abbrvs llvm_cmds) 2;
  fprintf chan ".\n\n";
  abbrvs := Llvm_abbrvs.add_abbrv (Llvm_abbrvs.Loc_cmds llvm_cmds) name !abbrvs;

  let name = sprintf "%s_term_%d" fn_name i in
  fprintf chan "Definition %s : terminator :=\n" name;
  Coqgen.pp_expr chan (Llvm2coqexpr.visit_terminator !abbrvs llvm_term) 2;
  fprintf chan ".\n\n";
  abbrvs := Llvm_abbrvs.add_abbrv (Llvm_abbrvs.Loc_terminator llvm_term) name !abbrvs;

  let name = sprintf "%s_block_%d" fn_name i in
  fprintf chan "Definition %s : block :=\n" name;
  Coqgen.pp_expr chan (Llvm2coqexpr.visit_block !abbrvs llvm_block) 2;
  fprintf chan ".\n\n";
  abbrvs := Llvm_abbrvs.add_abbrv (Llvm_abbrvs.Loc_block llvm_block) name !abbrvs

let output_fdef chan abbrvs llvm_fdef =
  let (fn_name, llvm_args) =
    match llvm_fdef with
      | LLVMsyntax.Coq_fdef_intro (fheader, _) ->
        match fheader with
          | LLVMsyntax.Coq_fheader_intro (_, _, fid, args, _) -> (fid_to_fn_name fid, args) in

  (* llvm_args is a list of ((typ, attrs), id) *)

  let llvm_blocks =
    match llvm_fdef with
      | LLVMsyntax.Coq_fdef_intro (_, blocks) -> blocks in

  List.iteri (output_block chan abbrvs fn_name) llvm_blocks;

  let name = sprintf "%s_fdef" fn_name in
  fprintf chan "Definition %s : fdef :=\n" name;
  Coqgen.pp_expr chan (Llvm2coqexpr.visit_fdef !abbrvs llvm_fdef) 2;
  fprintf chan ".\n\n";
  abbrvs := Llvm_abbrvs.add_abbrv (Llvm_abbrvs.Loc_fdef llvm_fdef) name !abbrvs

let output_llvm_program chan coqm =
  ignore (Llvm2coqexpr.visit_module [] coqm); (* To build the list of atoms *)

  let (llvm_layouts, llvm_namedts, llvm_products) =
    match coqm with
      | LLVMsyntax.Coq_module_intro (layouts, namedts, products) -> (layouts, namedts, products) in

  let llvm_fdefs =
    filter_option (List.map (function LLVMsyntax.Coq_product_fdef fdef -> Some fdef | _ -> None) llvm_products) in

  let compare_atoms = string_compare in
  List.iteri
    (fun i (k, v) ->
      fprintf chan "Notation %s := (ax %d).\n" v i)
    (List.sort (fun (k1, v1) (k2, v2) -> compare_atoms v1 v2) (Hashtbl.fold (fun k v acc -> (k, v)::acc) Llvm2coqexpr.atoms []));
  fprintf chan "\n";

  let abbrvs = ref Llvm_abbrvs.empty_abbrvs in

  List.iter (output_fdef chan abbrvs) llvm_fdefs;

  fprintf chan "Definition llvm_layouts : list layout :=\n";
  Coqgen.pp_expr chan (Llvm2coqexpr.visit_layouts !abbrvs llvm_layouts) 2;
  fprintf chan ".\n\n";
  abbrvs := Llvm_abbrvs.add_abbrv (Llvm_abbrvs.Loc_layouts llvm_layouts) "llvm_layouts" !abbrvs;

  fprintf chan "Definition llvm_namedts : list namedt :=\n";
  Coqgen.pp_expr chan (Llvm2coqexpr.visit_namedts !abbrvs llvm_namedts) 2;
  fprintf chan ".\n\n";
  abbrvs := Llvm_abbrvs.add_abbrv (Llvm_abbrvs.Loc_namedts llvm_namedts) "llvm_namedts" !abbrvs;

  fprintf chan "Definition llvm_products : list product :=\n";
  Coqgen.pp_expr chan (Llvm2coqexpr.visit_products !abbrvs llvm_products) 2;
  fprintf chan ".\n\n";
  abbrvs := Llvm_abbrvs.add_abbrv (Llvm_abbrvs.Loc_products llvm_products) "llvm_products" !abbrvs;

  fprintf chan "Definition llvm_prog : module :=\n";
  Coqgen.pp_expr chan (Llvm2coqexpr.visit_module !abbrvs coqm) 2;
  fprintf chan ".\n\n";

  fprintf chan "Definition llvm_system : system := [llvm_prog].\n\n";

  fprintf chan "Definition llvm_td : targetdata := (llvm_layouts, llvm_namedts).\n\n";

  llvm_fdefs, abbrvs

let output_core_abbrvs chan abbrvs =
  let syms = ref [] in
  reviterwithtail (fun (loc, v) abbrvs ->
    match loc with
      | Core_abbrvs.Loc_sym sym -> syms := (v, sym, abbrvs) :: !syms
      | _ -> ()) abbrvs;
  let compare_syms (v1, _, _) (v2, _, _) = string_compare v1 v2 in
  List.iter (fun (v, sym, abbrvs) -> (fprintf chan "Definition %s : sym := " v;
                                      Coqgen.pp_expr chan (Core2coqexpr.visit_sym abbrvs sym) 0;
                                      fprintf chan ".\n")) (List.sort compare_syms !syms);
  fprintf chan "\n";

  reviterwithtail (fun (loc, v) abbrvs ->
    match loc with
      | Core_abbrvs.Loc_fun func -> (fprintf chan "Definition %s : (core_type * (list (sym * core_base_type)) * expr global.zero) :=\n" v;
                                     Coqgen.pp_expr chan (Core2coqexpr.visit_fun abbrvs func) 2;
                                     fprintf chan ".\n\n")
      | _ -> ()) abbrvs;

  reviterwithtail (fun (loc, v) abbrvs ->
    match loc with
      | Core_abbrvs.Loc_impl_decl impl_decl -> (fprintf chan "Definition %s : impl_decl global.zero :=\n" v;
                                                Coqgen.pp_expr chan (Core2coqexpr.visit_impl_decl abbrvs impl_decl) 2;
                                                fprintf chan ".\n\n")
      | _ -> ()) abbrvs

let output_core_program chan core_file =
  let core_abbrvs = ref Core_abbrvs.empty_abbrvs in

  Core_abbreviator.visit_fun_map core_abbrvs core_file.Core.funs;
  output_core_abbrvs chan !core_abbrvs;

  fprintf chan "Definition core_file : file_ global.zero := {|\n";
  fprintf chan "  main := ";
  Coqgen.pp_expr chan (Core2coqexpr.visit_sym !core_abbrvs core_file.Core.main) 0;
  fprintf chan ";\n";
  fprintf chan "  stdlib := core_stdlib;\n";
  fprintf chan "  impl := core_impl;\n";
  fprintf chan "  funs := ";
  Coqgen.pp_expr chan (Core2coqexpr.visit_fun_map !core_abbrvs core_file.Core.funs) 0;
  fprintf chan "\n";
  fprintf chan "|}.\n\n"

let output_stdlib_and_impl chan core_file =
  output_string chan "Require Import Csem.core.\n\n";

  let core_abbrvs = ref Core_abbrvs.empty_abbrvs in

  Core_abbreviator.visit_fun_map core_abbrvs core_file.Core.stdlib;
  Core_abbreviator.visit_impl core_abbrvs core_file.Core.impl;
  output_core_abbrvs chan !core_abbrvs;

  fprintf chan "Definition core_stdlib : fun_map global.zero :=\n";
  Coqgen.pp_expr chan (Core2coqexpr.visit_fun_map !core_abbrvs core_file.Core.stdlib) 2;
  fprintf chan ".\n\n";
  core_abbrvs := Core_abbrvs.add_abbrv (Core_abbrvs.Loc_fun_map core_file.Core.stdlib) "core_stdlib" !core_abbrvs;

  fprintf chan "Definition core_impl : impl_ global.zero :=\n";
  Coqgen.pp_expr chan (Core2coqexpr.visit_impl !core_abbrvs core_file.Core.impl) 2;
  fprintf chan ".\n\n";
  core_abbrvs := Core_abbrvs.add_abbrv (Core_abbrvs.Loc_impl core_file.Core.impl) "core_impl" !core_abbrvs

let output_statement_of_convergence_theorem chan main_reg llvm_args =
  fprintf chan "Theorem core_converges_if_llvm_converges :\n";
  fprintf chan "  forall (v ";
  List.iteri (fun i _ -> fprintf chan "v%d " i) llvm_args;
  fprintf chan ": llvm_value),\n";
  List.iteri (fun i v -> fprintf chan "    %s ->\n" (Proof_gen.arg_precondition i v)) llvm_args;
  fprintf chan "    llvm_converges llvm_system %s %s v ->\n" main_reg (Proof_gen.llvm_args_str' llvm_args);
  if List.length llvm_args > 0
  then (fprintf chan "    (exists (";
        List.iteri (fun i _ -> fprintf chan "cv%d " i) llvm_args;
        fprintf chan ": core_value),\n");
  let indent = if List.length llvm_args > 0 then "   " else "" in
  List.iteri (fun i _ -> fprintf chan "       (llvm_value_to_core_value llvm_td arg%d_ty v%d = Some cv%d) /\\\n" i i i) llvm_args;
  fprintf chan "%s    ((exists (cv : core_value),\n" indent;
  fprintf chan "%s        (llvm_value_to_core_value llvm_td ret_ty v = Some cv) /\\\n" indent;
  fprintf chan "%s        (core_converges core_file [" indent;
  fprintf chan "%s" (String.concat "; " (List.mapi (fun i _ -> sprintf "cv%d" i) llvm_args));
  fprintf chan "] cv)) \\/\n";
  fprintf chan "%s     (core_undefined core_file [" indent;
  fprintf chan "%s" (String.concat "; " (List.mapi (fun i _ -> sprintf "cv%d" i) llvm_args));
  fprintf chan "]))";
  if List.length llvm_args > 0
  then fprintf chan ")";
  fprintf chan ".\n"

let output_statement_of_divergence_theorem chan main_reg llvm_args =
  fprintf chan "Theorem core_diverges_if_llvm_diverges :\n";
  if List.length llvm_args > 0
  then (fprintf chan "  forall (";
        List.iteri (fun i _ -> fprintf chan "v%d " i) llvm_args;
        fprintf chan ": llvm_value),\n";
        List.iteri (fun i v -> fprintf chan "    %s ->\n" (Proof_gen.arg_precondition i v)) llvm_args);
  let indent = if List.length llvm_args > 0 then "  " else "" in
  fprintf chan "%s  llvm_diverges llvm_system %s %s ->\n" indent main_reg (Proof_gen.llvm_args_str' llvm_args);
  if List.length llvm_args > 0
  then (fprintf chan "%s  (exists (" indent;
        List.iteri (fun i _ -> fprintf chan "cv%d " i) llvm_args;
        fprintf chan ": core_value),\n");
  let indent = indent ^ (if List.length llvm_args > 0 then "   " else "") in
  List.iteri (fun i _ -> fprintf chan "%s  (llvm_value_to_core_value llvm_td arg%d_ty v%d = Some cv%d) /\\\n" indent i i i) llvm_args;
  fprintf chan "%s  ((core_diverges core_file [" indent;
  fprintf chan "%s" (String.concat "; " (List.mapi (fun i _ -> sprintf "cv%d" i) llvm_args));
  fprintf chan "]) \\/\n";
  fprintf chan "%s   (core_undefined core_file [" indent;
  fprintf chan "%s" (String.concat "; " (List.mapi (fun i _ -> sprintf "cv%d" i) llvm_args));
  fprintf chan "]))";
  if List.length llvm_args > 0
  then fprintf chan ")";
  fprintf chan ".\n"

let output_proof_script chan coqm core_file behaviour_opt deterministic llvm_behaviour main_fn skip_core_proof skip_llvm_proof =
  fprintf chan "Require Import Tvc.common.\n\n";

  Coqgen.output_comment chan "Definition of the LLVM IR program.";
  let llvm_fdefs, abbrvs = output_llvm_program chan coqm in

  Coqgen.output_comment chan "Definition of the Core program.";
  output_core_program chan core_file;

  let rec find_fdef fdefs id =
    match fdefs with
      | [] -> failwith (main_fn ^ " not found")
      | (((LLVMsyntax.Coq_fdef_intro (LLVMsyntax.Coq_fheader_intro (_, _, fid, _, _), _)) as fdef)::fdefs') ->
        if fid = ("@" ^ main_fn)
        then fdef
        else find_fdef fdefs' id in

  let llvm_fdef = find_fdef llvm_fdefs ("@" ^ main_fn) in

  let (ret_ty, main_fid, llvm_args) =
    match llvm_fdef with
      | LLVMsyntax.Coq_fdef_intro (fheader, _) ->
        match fheader with
          | LLVMsyntax.Coq_fheader_intro (_, ret_ty, fid, args, _) -> (ret_ty, fid, args) in

  let ret_width =
    match ret_ty with
      | LLVMsyntax.Coq_typ_int w -> w
      | _ -> failwith "function has non-integer return value" in

  Coqgen.output_comment chan "Definitions of the function argument and return types.";

  let make_ctype w signed =
    sprintf "%s %d" (if signed then "Signed_" else "Unsigned_") w in
  List.iteri (fun i v -> fprintf chan "Definition arg%d_ty : ctype := %s.\n" i (make_ctype (Proof_gen.arg_width v) (not (List.mem i !arg_unsigned)))) llvm_args;
  fprintf chan "Definition ret_ty : ctype := %s.\n\n" (make_ctype ret_width (not !ret_unsigned));

  let main_name = fid_to_fn_name main_fid in
  let main_reg = Hashtbl.find Llvm2coqexpr.atoms main_fid in

  Coqgen.output_comment chan "Statements and proofs of lemmas.";
  Proof_gen.output_lemmas chan !abbrvs behaviour_opt deterministic llvm_behaviour llvm_fdef skip_core_proof skip_llvm_proof main_name main_reg llvm_args ret_ty;

  Coqgen.output_comment chan "Statements and proofs of the semantic equivalence theorems.";
  output_statement_of_convergence_theorem chan main_reg llvm_args;
  Proof_gen.output_proof_of_convergence_theorem chan behaviour_opt llvm_args;
  output_statement_of_divergence_theorem chan main_reg llvm_args;
  Proof_gen.output_proof_of_divergence_theorem chan behaviour_opt llvm_args
