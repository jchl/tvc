let term_width = ref 120

let no_progress = ref false

let output_progress_fn chan f =
  if not !no_progress
  then (output_string chan "  idtac \"";
        f chan;
        output_string chan "\".\n")

let output_progress chan s =
  output_progress_fn chan (fun chan -> output_string chan s)

let no_comment = ref false
let output_comment chan s =
  if not !no_comment
  then (let line = "(*" ^ String.make (!term_width - 4) '*' ^ "*)\n" in
        output_string chan line;
        let middle = "(*" ^ String.make (!term_width - 4) ' ' ^ "*)\n" in
        assert ((String.length s) < (!term_width - 6));
        String.blit s 0 middle 3 (String.length s);
        output_string chan middle;
        output_string chan line;
        output_string chan "\n")

type expr =
  | ExAtom of string (* atomic expression *)
  | ExTuple of expr list (* tuple expression (x1, ..., xn) *)
  | ExList of expr list (* list expression [x1; ...; xn] *)
  | ExApp of expr list (* application expression (x1 ... xn) *)
  | ExInfix of expr * string * expr (* infix application expression (x1 op x2) *)

let output_expr chan e =
  let rec output_expr' a chan e =
    let output_seq sbegin ssep send f xs =
      output_string chan sbegin;
      List.iteri (fun i x -> (if i <> 0 then output_string chan ssep); f chan x) xs;
      output_string chan send
    in match e with
      | ExAtom a -> output_string chan a
      | ExTuple xs -> output_seq "(" ", " ")" (output_expr' false) xs
      | ExList xs -> output_seq "[" "; " "]" (output_expr' false) xs
      | ExApp xs ->
        if a
        then output_seq "(" "" ")" (output_expr' true) xs
        else output_seq "" "" "" (output_expr' true) xs
      | ExInfix (x1, op, x2) ->
        if a then output_string chan "(";
        output_expr' true chan x1;
        Printf.fprintf chan " %s " op;
        output_expr' true chan x2;
        if a then output_string chan ")" in
  output_expr' false chan e

let pp_expr chan e n =
  let rec pp_expr' a fmtr e =
    let output_seq n sbegin ssep send f xs =
      Format.pp_open_hovbox fmtr n;
      Format.pp_print_string fmtr sbegin;
      List.iteri (fun i x -> (if i <> 0 then Format.fprintf fmtr "%s@ " ssep); f fmtr x) xs;
      Format.pp_print_string fmtr send;
      Format.pp_close_box fmtr ()
    in match e with
      | ExAtom a -> Format.pp_print_string fmtr a
      | ExTuple xs -> output_seq 1 "(" "," ")" (pp_expr' false) xs
      | ExList xs -> output_seq 1 "[" ";" "]" (pp_expr' false) xs
      | ExApp xs ->
        if a
        then output_seq 2 "(" "" ")" (pp_expr' true) xs
        else output_seq 1 "" "" "" (pp_expr' true) xs
      | ExInfix (x1, op, x2) ->
        if a then Format.pp_print_string fmtr "(";
        pp_expr' true fmtr x1;
        Format.fprintf fmtr " %s " op;
        pp_expr' true fmtr x2;
        if a then Format.pp_print_string fmtr ")" in
  let fmtr = Format.formatter_of_out_channel chan in
  Format.pp_set_margin fmtr !term_width;
(*
  Format.pp_set_max_indent fmtr 0; (* Doesn't work as advertised. *)
  Format.pp_set_max_boxes fmtr 0; (* Not sure if this does anything; try this if we ever exceed the maximum number of boxes. *)
*)
  Format.pp_print_string fmtr (String.make n ' ');
  Format.pp_open_hovbox fmtr 4;
  pp_expr' false fmtr e;
  Format.pp_close_box fmtr ();
  Format.pp_print_flush fmtr ()

let visit_int i = ExAtom (string_of_int i)
let visit_big_int bint = ExAtom (Printf.sprintf "((%s)%%Z)" (Big_int.string_of_big_int bint))
let visit_string s = ExAtom ("\"" ^ s ^ "\"") (* XXX escaping *)

let visit_bool b =
  match b with
    | true -> ExAtom "true"
    | false -> ExAtom "false"

let visit_pair (f, g) (x, y) = ExTuple [f x; g y]
let visit_triple (f, g, h) (x, y, z) = ExTuple [f x; g y; h z]
let visit_list f xs = ExList (List.map f xs)

let visit_option f x =
  match x with
    | None -> ExAtom "None"
    | Some y -> ExApp [ExAtom "Some"; f y]
