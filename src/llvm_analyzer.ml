open Syntax
open Behaviour

type next_nodes =
  | Return
  | Branch of label * label
  | BranchUncond of label
  | Unreachable

type control_flow_node = label * next_nodes

type control_flow_graph = label * control_flow_node list

let nextnodes term =
  match term with
    | LLVMsyntax.Coq_insn_return (_, _, _) -> Return
    | LLVMsyntax.Coq_insn_return_void _ -> Return
    | LLVMsyntax.Coq_insn_br (_, _, l1, l2) -> Branch (l1, l2)
    | LLVMsyntax.Coq_insn_br_uncond (_, l) -> BranchUncond l
    | LLVMsyntax.Coq_insn_unreachable _ -> Unreachable

let node block =
  match block with
    | (l, LLVMsyntax.Coq_stmts_intro (_, _, term)) -> (l, nextnodes term)

let build_cfg llvm_fdef =
  let llvm_blocks =
    match llvm_fdef with
      | LLVMsyntax.Coq_fdef_intro (_, blocks) -> blocks in
  let nodes = List.map node llvm_blocks in
  let init_label = match List.hd nodes with (l, _) -> l in
  (init_label, nodes)

let find_node l nodes = List.assoc l nodes

let rec split_at f xs =
  match xs with
    | [] -> failwith "split_at"
    | (y::ys) when f y -> ([], xs)
    | (y::ys) -> let (ps, qs) = split_at f ys in (y::ps, qs)

let is_linear_or_loopy (l, nodes) =
  let rec is_linear_or_loopy' l nodes visited =
    if List.mem l visited
    then Loopy (split_at ((=) l) (List.rev visited))
    else (let next = find_node l nodes in
          match next with
            | Return -> Linear (List.rev (l::visited))
            | Branch _ -> Neither
            | BranchUncond l' -> is_linear_or_loopy' l' nodes (l::visited)
            | Unreachable -> Neither) in
  is_linear_or_loopy' l nodes []
