open Printf

type retval =
  | Ret_int of Big_int.big_int
  | Ret_var of string

let eq_retval rv1 rv2 =
  match (rv1, rv2) with
    | (Ret_int n1, Ret_int n2) -> Big_int.eq_big_int n1 n2
    | (Ret_var s1, Ret_var s2) -> s1 = s2
    | _ -> false

let compare_retval rv1 rv2 =
  match (rv1, rv2) with
    | (Ret_int n1, Ret_int n2) -> Big_int.compare_big_int n1 n2
    | (Ret_var s1, Ret_var s2) -> compare s1 s2
    | (Ret_int _, _) -> 1
    | (_, Ret_int _) -> -1

type behaviour =
  | Converges of retval
  | Diverges of int
  | Undefined

let eq_behaviour (_, b1) (_, b2) =
  match (b1, b2) with
    | (Converges rv1, Converges rv2) -> eq_retval rv1 rv2
    | (Diverges _, Diverges _) -> true
    | (Undefined, Undefined) -> true
    | _ -> false

let compare_behaviour (n1, b1) (n2, b2) =
  let c = match (b1, b2) with
    | (Converges rv1, Converges rv2) -> compare_retval rv1 rv2
    | (Diverges start1, Diverges start2) -> compare start1 start2
    | (Undefined, Undefined) -> 0
    | (Converges _, _) -> 1
    | (_, Converges _) -> -1
    | (Diverges _, _) -> 1
    | (_, Diverges _) -> -1 in
  if c = 0 then compare n1 n2 else c

let string_of_behaviour = function
  | Converges (Ret_int i) -> sprintf "converges to value %s" (Big_int.string_of_big_int i)
  | Converges (Ret_var s) -> sprintf "converges to expression %s" s
  | Diverges start -> sprintf "diverges starting at %d" start
  | Undefined -> "undefined"

let converges = function
  | Some (_, Converges _) -> true
  | _ -> false

let diverges = function
  | Some (_, Diverges _) -> true
  | _ -> false

let undefined = function
  | Some (_, Undefined) -> true
  | _ -> false

let isundefined = function
  | (_, Undefined) -> true
  | _ -> false

let get_return_value = function
  | Some (_, Converges v) -> v
  | _ -> failwith "get_return_value"

let get_termination_iterations = function
  | Some (n, _) -> n
  | None -> failwith "get_termination_iterations"

let get_loop_iterations = function
  | Some (_, Diverges start) -> start
  | _ -> failwith "get_loop_iterations"

type label = Syntax.LLVMsyntax.l
type linear_or_loopy =
  | Linear of label list
  | Loopy of (label list * label list)
  | Neither
