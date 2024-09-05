open List
open Nfa

(*********)
(* Types *)
(*********)

type regexp_t =
  | Empty_String
  | Char of char
  | Union of regexp_t * regexp_t
  | Concat of regexp_t * regexp_t
  | Star of regexp_t

(***********)
(* Utility *)
(***********)

let fresh =
  let cntr = ref 0 in
  fun () ->
    cntr := !cntr + 1 ;
    !cntr

(*******************************)
(* Part 3: Regular Expressions *)
(*******************************)

let regexp_to_nfa (regexp: regexp_t) : (int, char) nfa_t =
  let rec regexp_to_nfa_helper regexp = 
    match regexp with
    |Empty_String -> let q = fresh () in {sigma = []; qs = [q]; q0 = q; fs = [q]; delta = []}
    |Char ch -> 
      let q1 = fresh () in 
      let q2 = fresh () in 
      {sigma = [ch]; qs = [q1; q2]; q0 = q1; fs = [q2]; delta = [(q1, Some ch, q2)]}
    |Union (exp1, exp2) -> 
      let nfa1 = regexp_to_nfa_helper exp1 in
      let nfa2 = regexp_to_nfa_helper exp2 in
      let q_original = fresh () in
      let q_final = fresh () in
      let old_finals = nfa1.fs @ nfa2.fs in
      let delta = nfa1.delta @ nfa2.delta @ [(q_original, None, nfa1.q0); (q_original, None, nfa2.q0)] @
                  List.map (fun q -> (q, None, q_final)) old_finals in
      { sigma = nfa1.sigma @ nfa2.sigma; qs = nfa1.qs @ nfa2.qs @ [q_original; q_final]; q0 = q_original; fs = [q_final]; delta = delta }
    |Concat (exp1, exp2) ->
      let nfa1 = regexp_to_nfa_helper exp1 in
      let nfa2 = regexp_to_nfa_helper exp2 in
      let delta = nfa1.delta @ nfa2.delta  @ List.map(fun q -> (q, None, nfa2.q0)) nfa1.fs in
      { sigma = nfa1.sigma @ nfa2.sigma; qs = nfa1.qs @ nfa2.qs; q0 = nfa1.q0; fs = nfa2.fs; delta = delta }
    |Star exp -> 
      let nfa1 = regexp_to_nfa_helper exp in
      let q_original = fresh () in
      let q_final = fresh () in
      let delta = nfa1.delta @ [(q_original, None, q_final); (q_final, None, q_original); (q_original, None, nfa1.q0)]
       @ List.map (fun q -> (q, None, q_final)) nfa1.fs in
      {sigma = nfa1.sigma; qs = nfa1.qs @ [q_original; q_final]; q0 = q_original; fs = [q_final]; delta = delta}
    in
    regexp_to_nfa_helper regexp
  ;;




(*****************************************************************)
(* Below this point is parser code that YOU DO NOT NEED TO TOUCH *)
(*****************************************************************)

exception IllegalExpression of string

(* Scanner *)
type token =
  | Tok_Char of char
  | Tok_Epsilon
  | Tok_Union
  | Tok_Star
  | Tok_LParen
  | Tok_RParen
  | Tok_END

let str2re s = Re.(seq [start; Re.Posix.re s ]) |> Re.compile

let tokenize str =
  let re_toks = [
    (str2re "[a-z]", fun gs -> Some(Tok_Char (Re.Group.get gs 0).[0], 1));
    (str2re "E",     fun _  -> Some(Tok_Epsilon, 1));
    (str2re "\\|",   fun _  -> Some(Tok_Union, 1));
    (str2re "\\*",   fun _  -> Some(Tok_Star, 1));
    (str2re "\\(",   fun _  -> Some(Tok_LParen, 1));
    (str2re "\\)",   fun _  -> Some(Tok_RParen, 1))] in
  let rec helper pos s =
    if pos >= String.length s then [Tok_END]
    else match (List.find_map (fun (re, f) -> Option.bind (Re.exec_opt ~pos re s) f) re_toks) with 
      | None -> raise (IllegalExpression ("tokenize: " ^ s)) 
      | Some(tok, len) -> tok :: helper (pos + len) s
  in
  helper 0 str

let tok_to_str t =
  match t with
  | Tok_Char v -> Char.escaped v
  | Tok_Epsilon -> "E"
  | Tok_Union -> "|"
  | Tok_Star -> "*"
  | Tok_LParen -> "("
  | Tok_RParen -> ")"
  | Tok_END -> "END"

(*
   S -> A Tok_Union S | A
   A -> B A | B
   B -> C Tok_Star | C
   C -> Tok_Char | Tok_Epsilon | Tok_LParen S Tok_RParen

   FIRST(S) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(A) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(B) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(C) = Tok_Char | Tok_Epsilon | Tok_LParen
 *)

let parse_regexp (l : token list) =
  let lookahead tok_list =
    match tok_list with
    | [] -> raise (IllegalExpression "lookahead")
    | h :: t -> (h, t)
  in
  let rec parse_S l =
    let a1, l1 = parse_A l in
    let t, n = lookahead l1 in
    match t with
    | Tok_Union ->
        let a2, l2 = parse_S n in
        (Union (a1, a2), l2)
    | _ -> (a1, l1)
  and parse_A l =
    let a1, l1 = parse_B l in
    let t, n = lookahead l1 in
    match t with
    | Tok_Char c ->
        let a2, l2 = parse_A l1 in
        (Concat (a1, a2), l2)
    | Tok_Epsilon ->
        let a2, l2 = parse_A l1 in
        (Concat (a1, a2), l2)
    | Tok_LParen ->
        let a2, l2 = parse_A l1 in
        (Concat (a1, a2), l2)
    | _ -> (a1, l1)
  and parse_B l =
    let a1, l1 = parse_C l in
    let t, n = lookahead l1 in
    match t with Tok_Star -> (Star a1, n) | _ -> (a1, l1)
  and parse_C l =
    let t, n = lookahead l in
    match t with
    | Tok_Char c -> (Char c, n)
    | Tok_Epsilon -> (Empty_String, n)
    | Tok_LParen ->
        let a1, l1 = parse_S n in
        let t2, n2 = lookahead l1 in
        if t2 = Tok_RParen then (a1, n2)
        else raise (IllegalExpression "parse_C 1")
    | _ -> raise (IllegalExpression "parse_C 2")
  in
  let rxp, toks = parse_S l in
  match toks with
  | [Tok_END] -> rxp
  | _ -> raise (IllegalExpression "parse didn't consume all tokens")


let string_to_regexp str = parse_regexp @@ tokenize str

let string_to_nfa str = regexp_to_nfa @@ string_to_regexp str
