open Llvm
open Utils

let debug = false

let load_llvm llvm_filename =
  let ctx = create_context () in
  let mbuf = MemoryBuffer.of_file llvm_filename in
  let m = Llvm_bitreader.parse_bitcode ctx mbuf in
  let st = SlotTracker.create_of_module m in
  let coqm = Llvm2coq.translate_module debug st m in
  SlotTracker.dispose st;
  dispose_module m;
  coqm

type c_or_core_file =
  | C of string
  | Core of string

let load_c filename stdlib impl =
  let cabs = Cparser_driver.parse (Input.file filename) in
  let ail = match Cabs_to_ail.desugar "main" cabs with (* XXX why "main"? *)
    | Exception.Result r -> r
    | Exception.Exception err -> failwith ("Error desugaring cabs to ail: " ^ Pp_errors.to_string err) in
  let ail_annotated = match GenTyping.annotate_program Annotation.concrete_annotation (snd ail) with
    | Either.Left _ -> failwith "Error annotating ail program"
    | Either.Right r -> (fst ail, r) in
  let core = Translation.translate stdlib impl ail_annotated in
  let core_simplified = (* Core_simpl.simplify *) core in
  core_simplified

let load_core core_parser filename stdlib impl =
  let load_file core_parser filename =
    match core_parser (Input.file filename) with
      | Exception.Result (Core_parser_util.Rfile (main, funs)) -> (main, funs)
      | Exception.Exception err -> failwith ("Error loading core file: " ^ Pp_errors.to_string err)
      | _ -> failwith "Unknown error loading core file" in

  let (main, funs) = load_file core_parser filename in
  { Core.main = main; Core.stdlib = stdlib; Core.impl = impl; Core.funs = funs }

let load_c_or_core stdlib_filename impl_filename c_or_core_filename =
  let load_stdlib core_parser filename =
    match core_parser (Input.file filename) with
      | Exception.Result (Core_parser_util.Rstd stdlib) -> stdlib
      | Exception.Exception err -> failwith ("Error loading stdlib file: " ^ Pp_errors.to_string err)
      | _ -> failwith "Unknown error loading stdlib file" in

  let load_impl core_parser filename =
    match core_parser (Input.file filename) with
      | Exception.Result (Core_parser_util.Rimpl impl) -> impl
      | Exception.Exception err -> failwith ("Error loading impl file: " ^ Pp_errors.to_string err)
      | _ -> failwith "Unknown error loading impl file" in

  let core_sym_counter = ref Symbol.init in

  (* Create an initial instance of the Core parser. *)
  let module Core_parser_base = struct
    include Core_parser.Make (struct
      let sym_counter = core_sym_counter
      let std = Pmap.empty compare
    end)
    type token = Core_parser_util.token
    type result = Core_parser_util.result
  end in
  let module Initial_core_parser =
        Parser_util.Make(Core_parser_base) (Lexer_util.Make(Core_lexer)) in

  (* Load the core standard library. *)
  let stdlib = load_stdlib Initial_core_parser.parse stdlib_filename in
  
  (* Create an instance of the Core parser knowing about the standard library functions we just loaded. *)
  let module Core_parser_base = struct
    include Core_parser.Make (struct
      let sym_counter = core_sym_counter
      let std = List.fold_left
        (fun acc (fsym, _) -> match fsym with
          | Symbol.Symbol (_, Some fname) -> Pmap.add fname fsym acc
          | _                             -> failwith "invalid symbol")
        (Pmap.empty compare) (Pmap.bindings_list stdlib)
    end)
    type token = Core_parser_util.token
    type result = Core_parser_util.result
  end in
  let module Real_core_parser =
        Parser_util.Make(Core_parser_base) (Lexer_util.Make(Core_lexer)) in
  
  (* Load the implementation file. *)
  let impl = load_impl Real_core_parser.parse impl_filename in

  match c_or_core_filename with
    | C filename -> load_c filename stdlib impl
    | Core filename -> load_core Real_core_parser.parse filename stdlib impl

let dump_emacs_vars chan =
  output_string chan ("(*\n" ^
         "*** Local " ^ "Variables: ***\n" ^
         "*** coq-prog-name: \"coqtop\" ***\n" ^
         "*** coq-prog-args: (\"-emacs-U\" \"-require\" \"coqharness\" \"-impredicative-set\" \"-R\" \"../coq\" \"Tvc\" \"-R\" \"../../csem/_coq\" \"Csem\" \"-I\" \"../../vellvm-coq84pl2/release/vol/src/Vellvm\" \"-I\" \"../../vellvm-coq84pl2/release/vol/src/Vellvm/ott\" \"-I\" \"../../vellvm-coq84pl2/release/vol/src/Vellvm/monads\" \"-I\" \"../../vellvm-coq84pl2/release/vol/src/Vellvm/compcert\" \"-I\" \"../../vellvm-coq84pl2/release/vol/src/Vellvm/GraphBasics\" \"-I\" \"../../vellvm-coq84pl2/release/vol/src/Vellvm/Dominators\" \"-I\" \"../../vellvm-coq84pl2/release/vol/extralibs/metatheory_8.4\" \"-I\" \"../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/src\" \"-R\" \"../../vellvm-coq84pl2/release/vol/extralibs/Coq-Equations/theories\" \"Equations\" \"-I\" \"~/lem/coq-lib\") ***\n" ^
         "*** End: ***\n" ^
         "*)\n")

let main llvm_filename stdlib_filename impl_filename core_filename coq_filename assume_deterministic behaviour_opt llvm_behaviour main_fn skip_core_proof skip_llvm_proof skeleton no_emacs_vars =
  let coqm = load_llvm llvm_filename in
  let core_file = load_c_or_core stdlib_filename impl_filename (Core core_filename) in
  (* We don't necessarily agree with the core file's choice of main function. *)
  let main_sym = fromSome (Pmap.fold (fun (Symbol.Symbol (n, s) as sym) _ acc ->
    match acc with
      | Some x -> Some x
      | None -> if s = Some main_fn then Some sym else None) core_file.Core.funs None) in
  let core_file = { core_file with Core.main = main_sym } in

  let (behaviour_opt, deterministic) =
    match behaviour_opt with
      | Some b -> (Some b, true)
      | None ->
        match skeleton with
          | true -> (None, true)
          | false ->
            let (b, d) = Core_analyzer.determine_behaviour core_file assume_deterministic in
            (Some b, d) in

  let chan = open_out coq_filename in

  Theorem_gen.output_proof_script chan coqm core_file behaviour_opt deterministic llvm_behaviour main_fn (skip_core_proof || skeleton) (skip_llvm_proof || skeleton);

  if not no_emacs_vars
  then dump_emacs_vars chan;

  close_out chan

let go_dump_stdlib_and_impl stdlib_filename impl_filename core_filename coq_filename no_emacs_vars =
  let core_file = load_c_or_core stdlib_filename impl_filename (Core core_filename) in
  let chan = open_out coq_filename in
  Theorem_gen.output_stdlib_and_impl chan core_file;
  if not no_emacs_vars
  then dump_emacs_vars chan;
  close_out chan

let usage = "Usage: " ^ Sys.executable_name ^ " <llvm-filename> <stdlib-filename> <impl-filename> <core-filename> <coq-filename> [options]"

let parse_retval s =
  try
    Behaviour.Ret_int (Big_int.big_int_of_string s)
  with
    | _ -> Behaviour.Ret_var s

let parse_start s =
  try int_of_string s
  with (Failure _) -> raise (Arg.Bad "start iteration should be an integer")

let parse_string_list s =
  Str.split (Str.regexp ",") s

let deref var =
  match !var with
    | None -> failwith "insufficient anonymous arguments"
    | Some s -> s

let make_behaviour n = function
  | None -> None
  | Some b -> Some (n, b)

let () =
  let llvm_filename = ref None in
  let stdlib_filename = ref None in
  let impl_filename = ref None in
  let core_filename = ref None in
  let coq_filename = ref None in
  let assume_deterministic = ref false in
  let behaviour_opt = ref None in
  let llvm_behaviour = ref Behaviour.Neither in
  let iterations = ref 0 in
  let main_fn = ref "main" in
  let skip_core_proof = ref false in
  let skip_llvm_proof = ref false in
  let skeleton = ref false in
  let no_emacs_vars = ref false in
  let dump_stdlib_and_impl = ref false in

  let num_anon = ref 0 in
  let anon_fn s =
    let var =
      match !num_anon with
        | 0 -> llvm_filename
        | 1 -> stdlib_filename
        | 2 -> impl_filename
        | 3 -> core_filename
        | 4 -> coq_filename
        | _ -> raise (Arg.Bad "too many anonymous arguments") in
    var := Some s;
    incr num_anon in

  let speclist = [
    ("--main", Arg.Set_string main_fn, "Set the name of the main function (default: 'main')");
    ("--ret-unsigned", Arg.Set Theorem_gen.ret_unsigned, "Specify that the type of the return value is unsigned");
    ("--arg-unsigned", Arg.Int (fun i -> Theorem_gen.arg_unsigned := i :: !Theorem_gen.arg_unsigned), "Specify that the type of the given argument is unsigned");
    ("--assume-deterministic", Arg.Set assume_deterministic, "Assume that the program is deterministic");
    ("--converges", Arg.String (fun s -> behaviour_opt := Some (Behaviour.Converges (parse_retval s))), "Specifies that the program converges to the given value");
    ("--diverges", Arg.String (fun s -> behaviour_opt := Some (Behaviour.Diverges (parse_start s))), "Specifies that the program diverges starting at the specified iteration");
    ("--undefined", Arg.Unit (fun () -> behaviour_opt := Some Behaviour.Undefined), "Specifies that the program has undefined behaviour");
    ("--basic-blocks", Arg.String (fun s -> llvm_behaviour := Behaviour.Linear (parse_string_list s)), "Specifies the sequence of basic blocks that are executed");
    ("--iterations", Arg.Set_int iterations, "Set the number of iterations before the program converges/diverges/has undefined behaviour");
    ("--skip-core-proof", Arg.Set skip_core_proof, "Skip the proofs about the behaviour of the Core program");
    ("--skip-llvm-proof", Arg.Set skip_llvm_proof, "Skip the proofs about the behaviour of the LLVM IR program");
    ("--skeleton", Arg.Set skeleton, "Skeleton mode");
    ("--width", Arg.Set_int Coqgen.term_width, "Set the width of the terminal (default: 120)");
    ("--no-emacs-vars", Arg.Set no_emacs_vars, "Disable inclusion of emacs variables");
    ("--no-progress", Arg.Set Coqgen.no_progress, "Disable printing of progress indications");
    ("--dump-stdlib-and-impl", Arg.Set dump_stdlib_and_impl, "Dump the Core standard library and implementation library")
  ] in

  Arg.parse speclist anon_fn usage;

  if !dump_stdlib_and_impl
  then go_dump_stdlib_and_impl (deref stdlib_filename) (deref impl_filename) (deref core_filename) (deref coq_filename) (!no_emacs_vars)
  else main (deref llvm_filename) (deref stdlib_filename) (deref impl_filename) (deref core_filename) (deref coq_filename) (!assume_deterministic) (make_behaviour !iterations !behaviour_opt) (!llvm_behaviour) (!main_fn) (!skip_core_proof) (!skip_llvm_proof) (!skeleton) (!no_emacs_vars)
