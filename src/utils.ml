let fromSome x =
  match x with
    | None -> failwith "fromSome"
    | Some x -> x

let tr a b = String.map (fun c -> if c == a then b else c)

let explode s =
  let rec explode' i acc =
    if i < 0 then acc else explode' (i - 1) (s.[i] :: acc) in
  explode' (String.length s - 1) []

let implode cs =
  let s = String.create (List.length cs) in
  let rec implode' i cs =
    match cs with
      | [] -> s
      | (c::cs) -> s.[i] <- c; implode' (i + 1) cs in
  implode' 0 cs

let isdigit = function
  | '0' | '1' .. '9' -> true
  | _ -> false

let rec filter_option xs =
  match xs with
    | [] -> []
    | None::ys -> filter_option ys
    | (Some x)::ys -> x::(filter_option ys)

let revitertails f xs =
  let rec revitertails' f i xs =
    match xs with
      | [] -> ()
      | (_::ys) ->
        revitertails' f (i + 1) ys;
        f i xs in
  revitertails' f 0 xs

let reviterwithtail f xs =
  let rec reviterwithtail' f i xs =
    match xs with
      | [] -> ()
      | (y::ys) ->
        reviterwithtail' f (i + 1) ys;
        f y ys in
  reviterwithtail' f 0 xs

let rec dedup eq xs =
  match xs with
    | [] -> []
    | [x] -> [x]
    | x::y::zs -> if eq x y then dedup eq (y::zs) else x :: dedup eq (y::zs)

let unique eq cmp xs = dedup eq (List.sort cmp xs)

let group_digits cs =
  let convert id cs =
    let s = implode (List.rev cs) in
    if id then Either.Left (int_of_string s) else Either.Right s in

  let rec group_digits' id cs' acc cs =
    match cs with
      | [] -> (convert id cs')::acc
      | (c::cs) ->
        if id = isdigit c
        then group_digits' id (c::cs') acc cs
        else group_digits' (not id) [c] ((convert id cs')::acc) cs in

  List.rev (group_digits' false [] [] cs)

let string_compare s1 s2 =
  let ds1 = group_digits (explode s1) in
  let ds2 = group_digits (explode s2) in
  let rec sc ds1 ds2 =
    match (ds1, ds2) with
      | ([], []) -> 0
      | ([], _) -> -1
      | (_, []) -> 1
      | (d1::ds1', d2::ds2') ->
        match (d1, d2) with
          | (Either.Left n1, Either.Left n2) -> let c = compare n1 n2 in if c = 0 then sc ds1' ds2' else c
          | (Either.Right s1, Either.Right s2) -> let c = String.compare s1 s2 in if c = 0 then sc ds1' ds2' else c
          | (Either.Left _, _) -> -1
          | (_, Either.Left _) -> 1 in
  sc ds1 ds2
