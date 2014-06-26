open Printf
open Syntax
open Behaviour
open Utils

type memory_op =
  | Alloc of string * int
  | Load of string * int
  | Store of string * int

let arg_precondition i v =
  sprintf "is_well_typed arg%d_ty v%d" i i

let arg_width ((t, _), _) =
  match t with
    | LLVMsyntax.Coq_typ_int w -> w
    | _ -> failwith "function takes non-integer argument"

let llvm_args_str llvm_args =
  "[" ^ (String.concat "; " (List.mapi (fun i v -> sprintf "$ v%d # typ_int %d $" i (arg_width v)) llvm_args)) ^ "]"
let llvm_args_str_with_stuff llvm_args =
  "[" ^ (String.concat "; " (List.mapi (fun i v -> sprintf "(%s, $ v%d # typ_int %d $)" (Hashtbl.find Llvm2coqexpr.atoms (snd v)) (List.length llvm_args - i - 1) (arg_width v)) (List.rev llvm_args))) ^ "]"
let llvm_args_str' llvm_args =
  "[" ^ (String.concat "; " (List.mapi (fun i _ -> sprintf "(v%d, arg%d_ty)" i i) llvm_args)) ^ "]"
let cvs_str llvm_args =
  "[" ^ (String.concat "; " (List.mapi (fun i _ -> sprintf "cv%d" i) llvm_args)) ^ "]"

let output_lemmas chan abbrvs behaviour deterministic llvm_behaviour llvm_fdef skip_core_proof skip_llvm_proof main_name main_reg llvm_args ret_ty =
  let llvm_blocks =
    match llvm_fdef with
      | LLVMsyntax.Coq_fdef_intro (_, blocks) -> blocks in

  let label_to_cmds l =
    match List.assoc l llvm_blocks with
      | LLVMsyntax.Coq_stmts_intro (_, cmds, term) -> (List.map (fun c -> Either.Left c) cmds) @ [Either.Right term] in
  let labels_to_cmds labels = List.concat (List.map label_to_cmds labels) in

  let label_to_cmds_term l =
    match List.assoc l llvm_blocks with
      | LLVMsyntax.Coq_stmts_intro (_, cmds, term) -> (cmds, term) in

  if converges behaviour || diverges behaviour
  then (fprintf chan "Lemma initState_is :\n";
        fprintf chan "  forall cfg IS";
        List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
        fprintf chan ",\n";
        List.iteri (fun i v -> fprintf chan "    %s ->\n" (arg_precondition i v)) llvm_args;
        fprintf chan "    @s_genInitState GVsSig llvm_system %s %s Memory.Mem.empty = Some (cfg, IS) ->\n" main_reg (llvm_args_str llvm_args);
        fprintf chan "    (exists g f,\n";
        fprintf chan "       (cfg = mkCfg llvm_system llvm_td llvm_products g f) /\\\n";
        fprintf chan "       (IS = mkState [mkEC %s_fdef %s_block_0 %s_cmds_0 %s_term_0 %s []] Memory.Mem.empty)).\n" main_name main_name main_name main_name (llvm_args_str_with_stuff llvm_args);
        fprintf chan "Proof.\n";
        Coqgen.output_progress chan "Proving initState_is...";
        fprintf chan "  intros ? ?";
        List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
        List.iteri (fun i _ -> fprintf chan " [i%d H%d']" i i) llvm_args;
        fprintf chan ".\n";
        fprintf chan "  prove_initState_is_1.\n";
        fprintf chan "  Transparent initLocals.\n";
        fprintf chan "  unfold initLocals in H2.\n";
        fprintf chan "  Opaque initLocals.\n";
        fprintf chan "  Opaque ndopsem.MNDGVs.gv2gvs.\n";
        fprintf chan "  simpl in H2.\n";
        fprintf chan "  Transparent ndopsem.MNDGVs.gv2gvs.\n";
        fprintf chan "  destruct_all_eq_dec.\n";
        List.iteri (fun i _ -> fprintf chan "  prove_initState_is_2 H2 v%d i%d.\n" i i) llvm_args;
        fprintf chan "  injection H2; intro; clear H2; subst.\n";
        fprintf chan "  injection H; intros; subst.\n";
        fprintf chan "  split; reflexivity.\n";
        fprintf chan "Qed.\n\n");

  let f cmd (allocs, loads, stores) =
    match cmd with
      | Either.Left (LLVMsyntax.Coq_insn_alloca (id, _, _, _)) ->
        (Some (Alloc (id, allocs), (allocs + 1, loads, stores)))
      | Either.Left (LLVMsyntax.Coq_insn_load (_, _, LLVMsyntax.Coq_value_id id, _)) ->
        (Some (Load (id, loads), (allocs, loads + 1, stores)))
      | Either.Left (LLVMsyntax.Coq_insn_store (_, _, _, LLVMsyntax.Coq_value_id id, _)) ->
        (Some (Store (id, stores), (allocs, loads, stores + 1)))
      | _ -> None in

  let g (ops, counts) cmd =
    match f cmd counts with
      | Some (op, counts) -> (op::ops, counts)
      | None -> (ops, counts) in

  let rec ops_before_load i ops =
    match ops with
      | (Load (id, j))::ops' -> if i = j then (id, ops') else ops_before_load i ops'
      | _::ops' -> ops_before_load i ops'
      | [] -> failwith (sprintf "didn't find load #%d" i) in

  let rec ops_before_store i ops =
    match ops with
      | (Store (id, j))::ops' -> if i = j then (id, ops') else ops_before_store i ops'
      | _::ops' -> ops_before_store i ops'
      | [] -> failwith (sprintf "didn't find store #%d" i) in

  let rec store_or_alloc_for_id id stores ops =
    match ops with
      | (Store (id', j))::ops' -> if id = id' then (Either.Left j, stores) else store_or_alloc_for_id id (j::stores) ops'
      | (Alloc (id', j))::ops' -> if id = id' then (Either.Right j, stores) else store_or_alloc_for_id id stores ops' (* XXX should keep track of intervening allocs too *)
      | _::ops' -> store_or_alloc_for_id id stores ops'
      | [] -> failwith (sprintf "didn't find the store or alloc of %s" id) in

  let store_or_alloc_for_load rev_memory_ops i =
    let (id, ops) = ops_before_load i rev_memory_ops in
    store_or_alloc_for_id id [] ops in

  let rec alloc_for_id id ops =
    match ops with
      | (Alloc (id', j))::ops' -> if id = id' then j else alloc_for_id id ops'
      | _::ops' -> alloc_for_id id ops'
      | [] -> failwith (sprintf "didn't find the alloc of %s" id) in

  let alloc_for_load rev_memory_ops i =
    let (id, ops) = ops_before_load i rev_memory_ops in
    alloc_for_id id ops in

  let alloc_for_store rev_memory_ops i =
    let (id, ops) = ops_before_store i rev_memory_ops in
    alloc_for_id id ops in

  let insn_tactic =
    let num_allocs = ref 0 in
    let num_loads = ref 0 in
    let num_stores = ref 0 in
    let not_equal_allocs = ref [] in (* to avoid generating redundant 'assert_allocs_not_equal' *)

    fun rev_memory_ops -> function
      | Either.Left insn ->
        (match insn with
          | LLVMsyntax.Coq_insn_alloca _ -> (incr num_allocs; sprintf "do_alloca. simplify_alloca Halloc%d." !num_allocs)
          | LLVMsyntax.Coq_insn_load (_, _, LLVMsyntax.Coq_value_id id, _) -> (
            incr num_loads;
            let (the_store_or_alloc, stores) = store_or_alloc_for_load rev_memory_ops !num_loads in
            sprintf "do_load. simplify_load Hload%d.\n" !num_loads ^
              String.concat "" (List.map (fun i ->
                let alloc_l = alloc_for_load rev_memory_ops !num_loads in
                let alloc_s = alloc_for_store rev_memory_ops i in
                if not (List.mem (alloc_l, alloc_s) !not_equal_allocs)
                then (not_equal_allocs := (alloc_l, alloc_s) :: !not_equal_allocs;
                      sprintf "  assert_allocs_not_equal Halloc%d Halloc%d.\n" alloc_l alloc_s)
                else "") (List.rev stores)) ^
              String.concat "" (List.map (fun i -> sprintf "  commute_store_and_load Hstore%d Hload%d.\n" i !num_loads) (List.rev stores)) ^
              (match the_store_or_alloc with
                | Either.Left the_store -> sprintf "  equate_store_and_load Hstore%d Hload%d.\n" the_store !num_loads
                | Either.Right the_alloc -> sprintf "  equate_alloc_and_load Halloc%d Hload%d.\n" the_alloc !num_loads) ^
              (sprintf "  try rewrite <- repr_unsigned_inverse in Hload%d.\n" !num_loads) ^
              sprintf "  subst.")
          | LLVMsyntax.Coq_insn_store _ -> (incr num_stores;
                                            (sprintf "do_store. simplify_store Hstore%d.\n" !num_stores) ^
                                              (sprintf "  try rewrite <- signed_repr_inverse in Hstore%d by prove_a_lt_b_lt_c." !num_stores))
          | LLVMsyntax.Coq_insn_bop _ -> "do_bop. simplify_bop."
          | LLVMsyntax.Coq_insn_trunc _ -> "do_trunc. simplify_trunc."
          | LLVMsyntax.Coq_insn_ext _ -> "do_ext. simplify_ext."
          | LLVMsyntax.Coq_insn_icmp _ -> "do_icmp. simplify_icmp."
          | LLVMsyntax.Coq_insn_select _ -> "do_select. simplify_select."
          | _ -> failwith "unsupported instruction")
      | Either.Right term ->
        (match term with
          | LLVMsyntax.Coq_insn_return _ -> "do_ret. simplify_ret."
          | LLVMsyntax.Coq_insn_br_uncond _ -> "do_br_uncond. simplify_br_uncond."
          | LLVMsyntax.Coq_insn_br _ -> "do_br. simplify_br."
          | _ -> failwith "unsupported terminator") in

  let visit_cmd_or_term abbrvs cmd_or_term =
    match cmd_or_term with
      | Either.Left cmd -> Llvm2coqexpr.visit_cmd abbrvs cmd
      | Either.Right term -> Llvm2coqexpr.visit_terminator abbrvs term in

  let output_insn_tactic rev_memory_ops insn =
    Coqgen.output_progress_fn chan (fun chan -> output_string chan "-   "; Coqgen.pp_expr chan (visit_cmd_or_term [] insn) 0);
    fprintf chan "  %s\n\n" (insn_tactic rev_memory_ops insn) in

  if converges behaviour
  then (fprintf chan "Definition thevalue";
        if List.length llvm_args > 0
        then fprintf chan " (%s : GenericValue)" (String.concat " " (List.mapi (fun i _ -> sprintf "v%d" i) llvm_args));
        fprintf chan " : GenericValue :=\n";
        let w =
          match ret_ty with
            | LLVMsyntax.Coq_typ_int w -> (w - 1)
            | _ -> failwith "function returns non-integer type" in
        (match get_return_value behaviour with
          | Ret_int i -> fprintf chan "  [(Values.Vint %d (Integers.Int.repr %d (%s)%%Z), AST.Mint %d)]" w w (Big_int.string_of_big_int i) w
          | Ret_var s -> fprintf chan "  %s" s);
        fprintf chan ".\n\n";

        fprintf chan "Lemma llvm_converges_only_to_thevalue :\n";
        fprintf chan "  forall v";
        List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
        fprintf chan ",\n";
        List.iteri (fun i v -> fprintf chan "    %s ->\n" (arg_precondition i v)) llvm_args;
        fprintf chan "    llvm_converges llvm_system %s %s v ->\n" main_reg (llvm_args_str' llvm_args);
        fprintf chan "    v = thevalue";
        List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
        fprintf chan ".\n";
        fprintf chan "Proof.\n";
        Coqgen.output_progress chan "Proving llvm_converges_only_to_thevalue...";
        fprintf chan "  intros ? ";
        List.iter (fun _ -> fprintf chan "? ") llvm_args;
        List.iteri (fun i _ -> fprintf chan "H%d' " i) llvm_args;
        fprintf chan "[? [[? H] ?]].\n";
        List.iteri (fun i _ -> fprintf chan "  case H%d'; intros.\n" i) llvm_args;
        fprintf chan "  apply invert_converges in H.\n";
        fprintf chan "  decompose_ex H; destruct H as [H' [? ?]].\n";
        fprintf chan "  destruct_initState (initState_is _ _";
        List.iter (fun _ -> fprintf chan " _") llvm_args;
        List.iteri (fun i _ -> fprintf chan " H%d'" i) llvm_args;
        fprintf chan " H').\n";
        if List.length llvm_args > 0
        then fprintf chan "  clear %s.\n" (String.concat " " (List.mapi (fun i _ -> sprintf "H%d'" i) llvm_args));
        fprintf chan "\n";

        if skip_llvm_proof
        then (fprintf chan "  (* hard bit goes here *)\n";
              fprintf chan "Admitted.\n\n")
        else (let cfg = Llvm_analyzer.build_cfg llvm_fdef in
              let llvm_behaviour =
                match llvm_behaviour with
                  | Neither -> Llvm_analyzer.is_linear_or_loopy cfg
                  | _ -> llvm_behaviour in

              let llvm_cmds =
                match llvm_behaviour with
                  | Linear labels -> labels_to_cmds labels
                  | _ -> failwith "control-flow graph is not linear!" in

              let rev_memory_ops = fst (List.fold_left g ([], (1, 1, 1)) llvm_cmds) in
              List.iter (output_insn_tactic rev_memory_ops) llvm_cmds;

              fprintf chan "  try (compute; intrange_proof_irr).\n";
              fprintf chan "  reflexivity.\n";
              fprintf chan "Qed.\n\n");

        fprintf chan "Lemma llvm_does_not_diverge :\n";
        if List.length llvm_args > 0
        then (fprintf chan "  forall";
              List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
              fprintf chan ",\n";
              List.iteri (fun i v -> fprintf chan "    %s ->\n" (arg_precondition i v)) llvm_args);
        let indent = if List.length llvm_args > 0 then "  " else "" in
        fprintf chan "%s  ~(llvm_diverges llvm_system %s %s).\n" indent main_reg (llvm_args_str' llvm_args);
        fprintf chan "Proof.\n";
        Coqgen.output_progress chan "Proving llvm_does_not_diverge...";
        fprintf chan "  intros ";
        List.iter (fun _ -> fprintf chan "? ") llvm_args;
        List.iteri (fun i _ -> fprintf chan "H%d' " i) llvm_args;
        fprintf chan "[? H].\n";
        List.iteri (fun i _ -> fprintf chan "  case H%d'; intros.\n" i) llvm_args;
        fprintf chan "  apply invert_diverges in H.\n";
        fprintf chan "  decompose_ex H; destruct H as [H' ?].\n";
        fprintf chan "  destruct_initState (initState_is _ _";
        List.iter (fun _ -> fprintf chan " _") llvm_args;
        List.iteri (fun i _ -> fprintf chan " H%d'" i) llvm_args;
        fprintf chan " H').\n";
        if List.length llvm_args > 0
        then fprintf chan "  clear %s.\n" (String.concat " " (List.mapi (fun i _ -> sprintf "H%d'" i) llvm_args));
        if skip_llvm_proof
        then (fprintf chan "\n  (* hard bit goes here *)\n";
              fprintf chan "Admitted.\n\n")
        else (fprintf chan "  apply opsem_props.OpsemProps.sop_diverges__sop_diverges' in H.\n"; (* we want to work with sInsn, not sop_plus *)
              fprintf chan "  single_basic_block_does_not_diverge;\n";
              fprintf chan "    repeat (terminator_does_not_diverge; single_basic_block_does_not_diverge).\n";
              fprintf chan "Qed.\n\n");

        fprintf chan "Lemma core_converges_to_thevalue :\n";
        if List.length llvm_args > 0
        then (fprintf chan "  forall";
              List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
              fprintf chan ",\n");
        let indent = if List.length llvm_args > 0 then "  " else "" in
        List.iteri (fun i v -> fprintf chan "%s  %s ->\n" indent (arg_precondition i v)) llvm_args;
        fprintf chan "%s  (exists (cv" indent;
        List.iteri (fun i _ -> fprintf chan " cv%d" i) llvm_args;
        fprintf chan " : expr global.zero),\n";
        fprintf chan "%s     (llvm_value_to_core_value llvm_td ret_ty (thevalue" indent;
        List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
        fprintf chan ") = Some cv) /\\\n";
        List.iteri (fun i _ -> fprintf chan "%s     (llvm_value_to_core_value llvm_td arg%d_ty v%d = Some cv%d) /\\\n" indent i i i) llvm_args;
        fprintf chan "%s     (core_converges core_file %s cv)).\n" indent (cvs_str llvm_args);
        fprintf chan "Proof.\n";
        Coqgen.output_progress chan "Proving core_converges_to_thevalue...";
        fprintf chan "  intros";
        List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
        List.iteri (fun i _ -> fprintf chan " [i%d H%d]" i i) llvm_args;
        fprintf chan ".\n";
        fprintf chan "  pose_cv (llvm_value_to_core_value llvm_td ret_ty (thevalue";
        List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
        fprintf chan ")) cv.\n";
        List.iteri (fun i _ -> fprintf chan "  pose_cv (llvm_value_to_core_value llvm_td arg%d_ty v%d) cv%d.\n" i i i) llvm_args;
        fprintf chan "  set (args := [%s]).\n" (String.concat "; " (List.mapi (fun i _ -> sprintf "cv%d" i) llvm_args));
        if deterministic
        then fprintf chan "  pose_s_and_t' core_file args %d.\n" (get_termination_iterations behaviour)
        else fprintf chan "  pose_s_and_t core_file args %d.\n" (get_termination_iterations behaviour);
        fprintf chan "  subst.\n";
        fprintf chan "  exists cv.\n";
        List.iteri (fun i _ -> fprintf chan "  exists cv%d.\n" i) llvm_args;
        fprintf chan "  repeat split.\n";
        fprintf chan "  exists t.\n";
        fprintf chan "  exists s.\n";
        if skip_core_proof
        then (fprintf chan "\n  (* hard bit goes here *)\n";
              fprintf chan "Admitted.\n\n")
        else (if deterministic
              then fprintf chan "  apply (red2n'_implies_star_red2_ind %d).\n" (get_termination_iterations behaviour)
              else fprintf chan "  apply (red2n_implies_star_red2_ind %d).\n" (get_termination_iterations behaviour);
              if List.length llvm_args > 0
              then fprintf chan "  compute -[Integers.Int.signed Integers.Int.modulus].\n"
              else fprintf chan "  vm_compute.\n"; (* Hack: vm_compute is faster -- but only if there are no (signed) arguments *)
              if deterministic
              then fprintf chan "  reflexivity.\n"
              else fprintf chan "  repeat first [left; reflexivity | right].\n";
              fprintf chan "Qed.\n\n"))

  else if diverges behaviour
  then (fprintf chan "Lemma llvm_does_not_converge :\n";
        if List.length llvm_args > 0
        then (fprintf chan "  forall";
              List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
              fprintf chan ",\n";
              List.iteri (fun i v -> fprintf chan "    %s ->\n" (arg_precondition i v)) llvm_args);
        let indent = if List.length llvm_args > 0 then "  " else "" in
        fprintf chan "%s  ~(exists (v : llvm_value),\n" indent;
        fprintf chan "%s      llvm_converges llvm_system %s %s v).\n" indent main_reg (llvm_args_str' llvm_args);
        fprintf chan "Proof.\n";
        Coqgen.output_progress chan "Proving llvm_does_not_converge...";
        fprintf chan "  intros ";
        List.iter (fun _ -> fprintf chan "? ") llvm_args;
        List.iteri (fun i _ -> fprintf chan "H%d' " i) llvm_args;
        fprintf chan "[_ [? [[? H] _]]].\n";
        List.iteri (fun i _ -> fprintf chan "  case H%d'; intros.\n" i) llvm_args;
        fprintf chan "  apply invert_converges in H.\n";
        fprintf chan "  decompose_ex H; destruct H as [H' [? ?]].\n";
        fprintf chan "  destruct_initState (initState_is _ _";
        List.iter (fun _ -> fprintf chan " _") llvm_args;
        List.iteri (fun i _ -> fprintf chan " H%d'" i) llvm_args;
        fprintf chan " H').\n";
        if List.length llvm_args > 0
        then fprintf chan "  clear %s.\n" (String.concat " " (List.mapi (fun i _ -> sprintf "H%d'" i) llvm_args));
        fprintf chan "\n";

        if skip_llvm_proof
        then (fprintf chan "  (* hard bit goes here *)\n";
              fprintf chan "Admitted.\n\n")
        else (let cfg = Llvm_analyzer.build_cfg llvm_fdef in
              let llvm_behaviour =
                match llvm_behaviour with
                  | Neither -> Llvm_analyzer.is_linear_or_loopy cfg
                  | _ -> llvm_behaviour in

              let (llvm_cmds1, llvm_cmds2, cmds_term_s) =
                match llvm_behaviour with
                  | Loopy (xs, ys) -> (labels_to_cmds xs, labels_to_cmds ys, List.map label_to_cmds_term ys)
                  | _ -> failwith "control-flow graph not loopy!" in

              let rev_memory_ops = fst (List.fold_left g ([], (1, 1, 1)) llvm_cmds1) in
              List.iter (output_insn_tactic rev_memory_ops) llvm_cmds1;

              fprintf chan "  start_induction ";
              Coqgen.pp_expr chan (Llvm2coqexpr.visit_list (Llvm2coqexpr.visit_pair (Llvm2coqexpr.visit_cmds, Llvm2coqexpr.visit_terminator)) abbrvs cmds_term_s) 0;
              fprintf chan ".\n\n";

              let ih_tactic =
                function
                  | Either.Left insn ->
                    (match insn with
                      | LLVMsyntax.Coq_insn_alloca _ -> "do_alloca_simple."
                      | LLVMsyntax.Coq_insn_load _ -> "do_load_simple."
                      | LLVMsyntax.Coq_insn_store _ -> "do_store_simple."
                      | LLVMsyntax.Coq_insn_bop _ -> "do_bop_simple."
                      | LLVMsyntax.Coq_insn_trunc _ -> "do_trunc_simple."
                      | LLVMsyntax.Coq_insn_ext _ -> "do_ext_simple."
                      | LLVMsyntax.Coq_insn_icmp _ -> "do_icmp_simple."
                      | LLVMsyntax.Coq_insn_select _ -> "do_select_simple."
                      | _ -> failwith "unsupported instruction")
                  | Either.Right term ->
                    (match term with
                      | LLVMsyntax.Coq_insn_br_uncond _ -> "do_br_uncond_simple. simplify_br_uncond."
                      | LLVMsyntax.Coq_insn_br _ -> "do_br_simple. simplify_br."
                      | _ -> failwith "unsupported terminator") in

              let output_ih_tactic insn =
                Coqgen.output_progress_fn chan (fun chan -> output_string chan "-   "; Coqgen.pp_expr chan (visit_cmd_or_term [] insn) 0);
                fprintf chan "  %s\n" (ih_tactic insn);
                fprintf chan "  apply_induction_hypothesis IHsop_star.\n\n" in

              List.iter output_ih_tactic llvm_cmds2;

              fprintf chan "Qed.\n\n");

        fprintf chan "Lemma core_does_diverge :\n";
        if List.length llvm_args > 0
        then (fprintf chan "  forall";
              List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
              fprintf chan ",\n";
              List.iteri (fun i v -> fprintf chan "    %s ->\n" (arg_precondition i v)) llvm_args;
              fprintf chan "    (exists (";
              List.iteri (fun i _ -> fprintf chan "cv%d " i) llvm_args;
              fprintf chan ": expr global.zero),\n";
              List.iteri (fun i _ -> fprintf chan "       (llvm_value_to_core_value llvm_td arg%d_ty v%d = Some cv%d) /\\\n" i i i) llvm_args);
        let indent = if List.length llvm_args > 0 then "     " else "" in
        fprintf chan "%s  (core_diverges core_file %s)" indent (cvs_str llvm_args);
        if List.length llvm_args > 0
        then fprintf chan ")";
        fprintf chan ".\n";
        let a = get_loop_iterations behaviour in
        let b = get_termination_iterations behaviour in
        fprintf chan "Proof.\n";
        Coqgen.output_progress chan "Proving core_does_diverge...";
        fprintf chan "  intros";
        List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
        List.iteri (fun i _ -> fprintf chan " [i%d H%d]" i i) llvm_args;
        fprintf chan ".\n";
        fprintf chan "  subst.\n";
        List.iter (fun _ -> fprintf chan "  eexists.\n") llvm_args;
        fprintf chan "  repeat split.\n";
        fprintf chan "  apply plus_red2_diverges_implies_star_red2_diverges.\n";
        if skip_core_proof
        then (fprintf chan "\n  (* hard bit goes here *)\n";
              fprintf chan "Admitted.\n\n")
        else (let output_divergence_block n =
                fprintf chan "\n";
                fprintf chan "  pose_s_and_e %d.\n" n;
                fprintf chan "  apply core_run_inductive.plus_red2_diverges_intro with (s2 := s) (e2 := e).\n";
                fprintf chan "  apply (red2n_implies_plus_red2_ind %d); [ omega |].\n" n;
                fprintf chan "  compute -[Integers.Int.signed Integers.Int.modulus].\n";
                fprintf chan "  repeat first [left; reflexivity | right].\n";
                fprintf chan "  subst s e.\n";
                fprintf chan "\n" in

              output_divergence_block a;
              fprintf chan "  generalize_trace_and_tid.\n"; (* Might want to generalize more, but it's hard to know what. *)
              fprintf chan "  cofix.\n";
              fprintf chan "  intros.\n";
              output_divergence_block (2 * (b - a));
              (* XXX The "2 *" above is a hack, because the 'a list in Erun sometimes gets its order
                 inverted after each iteration -- it is a set in Ocaml, but a list in Coq, and hence
                 the ordering matters to Coq. *)
              fprintf chan "  trivial.\n";
              fprintf chan "Qed.\n\n"))

  else if undefined behaviour
  then (fprintf chan "Lemma core_is_undefined :\n";
        if List.length llvm_args > 0
        then (fprintf chan "  forall";
              List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
              fprintf chan ",\n";
              List.iteri (fun i v -> fprintf chan "    %s ->\n" (arg_precondition i v)) llvm_args;
              fprintf chan "    (exists (";
              List.iteri (fun i _ -> fprintf chan "cv%d " i) llvm_args;
              fprintf chan ": expr global.zero),\n";
              List.iteri (fun i _ -> fprintf chan "       (llvm_value_to_core_value llvm_td arg%d_ty v%d = Some cv%d) /\\\n" i i i) llvm_args);
        let indent = if List.length llvm_args > 0 then "     " else "" in
        fprintf chan "%s  (core_undefined core_file %s)" indent (cvs_str llvm_args);
        if List.length llvm_args > 0
        then fprintf chan ")";
        fprintf chan ".\n";
        fprintf chan "Proof.\n";
        Coqgen.output_progress chan "Proving core_is_undefined...";
        fprintf chan "  intros";
        List.iteri (fun i _ -> fprintf chan " v%d" i) llvm_args;
        List.iteri (fun i _ -> fprintf chan " [i%d H%d]" i i) llvm_args;
        fprintf chan ".\n";
        List.iteri (fun i _ -> fprintf chan "  pose_cv (llvm_value_to_core_value llvm_td arg%d_ty v%d) cv%d.\n" i i i) llvm_args;
        fprintf chan "  set (args := [%s]).\n" (String.concat "; " (List.mapi (fun i _ -> sprintf "cv%d" i) llvm_args));
        if deterministic
        then fprintf chan "  pose_s_and_u' core_file args %d.\n" (get_termination_iterations behaviour + 1)
        else fprintf chan "  pose_s_and_u core_file args %d.\n" (get_termination_iterations behaviour + 1);
        fprintf chan "  subst.\n";
        List.iteri (fun i _ -> fprintf chan "  exists cv%d.\n" i) llvm_args;
        fprintf chan "  repeat split.\n";
        if skip_core_proof
        then (fprintf chan "\n  (* hard bit goes here *)\n";
              fprintf chan "Admitted.\n\n")
        else (if deterministic
              then fprintf chan "  apply (red2n'_implies_star_red2_undef %d) with (s2 := s) (u := u).\n" (get_termination_iterations behaviour + 1)
              else fprintf chan "  apply (red2n_implies_star_red2_undef %d) with (s2 := s) (u := u).\n" (get_termination_iterations behaviour + 1);
              fprintf chan "  compute -[Integers.Int.signed Integers.Int.modulus].\n";
              if deterministic
              then fprintf chan "  reflexivity.\n"
              else fprintf chan "  repeat first [left; reflexivity | right].\n";
              fprintf chan "Qed.\n\n"))

let output_proof_using_undefinedness chan llvm_args =
  fprintf chan "  intros ";
  List.iter (fun _ -> fprintf chan "? ") llvm_args;
  List.iteri (fun i _ -> fprintf chan "H%d " i) llvm_args;
  fprintf chan "H.\n";
  fprintf chan "  pose proof (core_is_undefined";
  List.iter (fun _ -> fprintf chan " _") llvm_args;
  List.iteri (fun i _ -> fprintf chan " H%d" i) llvm_args;
  fprintf chan ") as H'.\n";
  if List.length llvm_args > 0
  then (fprintf chan "  decompose_ex H'.\n";
        fprintf chan "  decompose [and] H'; clear H'.\n";
        List.iteri (fun i _ -> fprintf chan "  exists cv%d.\n" i) llvm_args;
        fprintf chan "  repeat split; try assumption.\n");
  fprintf chan "  right.\n";
  fprintf chan "  assumption.\n";
  fprintf chan "Qed.\n\n"

let output_proof_of_convergence_theorem chan behaviour llvm_args =
  fprintf chan "Proof.\n";
  Coqgen.output_progress chan "Proving core_converges_if_llvm_converges...";
  if converges behaviour
  then (fprintf chan "  intros ? ";
        List.iter (fun _ -> fprintf chan "? ") llvm_args;
        List.iteri (fun i _ -> fprintf chan "H%d " i) llvm_args;
        fprintf chan "H.\n";
        fprintf chan "  pose proof (core_converges_to_thevalue";
        List.iter (fun _ -> fprintf chan " _") llvm_args;
        List.iteri (fun i _ -> fprintf chan " H%d" i) llvm_args;
        fprintf chan ") as H'.\n";
        fprintf chan "  decompose_ex H'.\n";
        fprintf chan "  decompose [and] H'; clear H'.\n";
        if List.length llvm_args > 0
        then (List.iteri (fun i _ -> fprintf chan "  exists cv%d.\n" i) llvm_args;
              fprintf chan "  repeat split; try assumption.\n");
        fprintf chan "  left.\n";
        fprintf chan "  exists cv.\n";
        fprintf chan "  eapply llvm_converges_only_to_thevalue in H; try eassumption.\n";
        fprintf chan "  subst v.\n";
        fprintf chan "  split; assumption.\n";
        fprintf chan "Qed.\n\n")
  else if diverges behaviour
  then (fprintf chan "  intros ? ";
        List.iter (fun _ -> fprintf chan "? ") llvm_args;
        List.iteri (fun i _ -> fprintf chan "H%d " i) llvm_args;
        fprintf chan "[gvs H].\n";
        fprintf chan "  decompose [and] H; clear H.\n";
        fprintf chan "  contradiction (llvm_does_not_converge";
        List.iter (fun _ -> fprintf chan " _") llvm_args;
        List.iteri (fun i _ -> fprintf chan " H%d" i) llvm_args;
        fprintf chan ").\n";
        fprintf chan "  exists v.\n";
        fprintf chan "  unfold llvm_converges.\n";
        fprintf chan "  eauto.\n";
        fprintf chan "Qed.\n\n")
  else if undefined behaviour
  then (fprintf chan "  intro v.\n";
        output_proof_using_undefinedness chan llvm_args)
  else (fprintf chan "  (* hard bit goes here *)\n";
        fprintf chan "Admitted.\n\n")

let output_proof_of_divergence_theorem chan behaviour llvm_args =
  fprintf chan "Proof.\n";
  Coqgen.output_progress chan "Proving core_diverges_if_llvm_converges...";
  if converges behaviour
  then (fprintf chan "  intros ";
        List.iter (fun _ -> fprintf chan "? ") llvm_args;
        List.iteri (fun i _ -> fprintf chan "H%d " i) llvm_args;
        fprintf chan "H.\n";
        fprintf chan "  contradiction (llvm_does_not_diverge";
        List.iter (fun _ -> fprintf chan " _") llvm_args;
        List.iteri (fun i _ -> fprintf chan " H%d" i) llvm_args;
        fprintf chan ").\n";
        fprintf chan "Qed.\n\n")
  else if diverges behaviour
  then (fprintf chan "  intros ";
        List.iter (fun _ -> fprintf chan "? ") llvm_args;
        List.iteri (fun i _ -> fprintf chan "H%d " i) llvm_args;
        fprintf chan "H.\n";
        fprintf chan "  pose proof (core_does_diverge";
        List.iter (fun _ -> fprintf chan " _") llvm_args;
        List.iteri (fun i _ -> fprintf chan " H%d" i) llvm_args;
        fprintf chan ") as H'.\n";
        if List.length llvm_args > 0
        then (fprintf chan "  decompose_ex H'.\n";
              fprintf chan "  decompose [and] H'; clear H'.\n";
              List.iteri (fun i _ -> fprintf chan "  exists cv%d.\n" i) llvm_args;
              fprintf chan "  repeat split; try assumption.\n");
        fprintf chan "  left.\n";
        fprintf chan "  assumption.\n";
        fprintf chan "Qed.\n\n")
  else if undefined behaviour
  then output_proof_using_undefinedness chan llvm_args
  else (fprintf chan "  (* hard bit goes here *)\n";
        fprintf chan "Admitted.\n\n")
