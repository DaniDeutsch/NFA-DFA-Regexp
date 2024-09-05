open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)
let rec remove_dupes lst =
  List.fold_left (fun acc s -> if elem s acc then acc else s::acc) [] lst
;;
let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =  
  let rec e_closure_helper qs lst = 
    match lst with
    | [] -> qs
    | (src, None, dest)::tl when elem src qs -> union [dest] (e_closure_helper qs tl)
    | _::tl -> e_closure_helper qs tl
  in
  let rec end_checker qlst = 
    let e_states = e_closure_helper qlst nfa.delta in 
    let union_e_closure = union e_states (e_closure_helper e_states nfa.delta) in
      if e_states = union_e_closure then e_states else (end_checker union_e_closure)
  in end_checker qs
;;

let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  List.fold_left (fun acc element -> 
    match element with 
    | (src, trans, dest) -> if trans = s && elem src qs then insert dest acc else acc) 
  [] nfa.delta;;
;;

(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  List.map (fun s -> e_closure nfa (move nfa qs s)) (List.map (fun s -> Some s) (nfa.sigma))
;;

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  List.map (fun s -> (qs, s, e_closure nfa (move nfa qs s))) (List.map (fun s -> Some s) (nfa.sigma))
;;

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  let rec finals_helper lst = 
    match lst with
    |[] -> []
    |hd::tl -> if elem hd nfa.fs then [qs] else finals_helper tl
  in finals_helper qs
;;
let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t = 
    match work with
  |[] -> dfa
  |hd::tl ->
    let new_dfa_states = diff (insert_all (new_states nfa hd) work) [[]] in
    let new_dfa_trans = List.filter (fun tran -> match tran with | (_,_,[]) -> false | _ -> true) (union (new_trans nfa hd) dfa.delta) in
    let new_dfa_finals = insert_all (new_finals nfa hd) dfa.fs in
    let new_dfa = {dfa with qs = union dfa.qs [hd]; fs = new_dfa_finals;
                    delta = new_dfa_trans} in
    nfa_to_dfa_step nfa new_dfa (diff (union new_dfa_states work) dfa.qs)
;;


let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
  let r = e_closure nfa [nfa.q0] in
  let dfa = { sigma = nfa.sigma; qs = [r]; q0 = r; fs = []; delta = [] } in
  nfa_to_dfa_step nfa dfa [r]
;;

let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  let lst = explode s in
  let dfa = nfa_to_dfa nfa in
  let rec state_finder q tr lst = 
    match lst with
    |[] -> None
    |(state, Some tran, nq)::tl when state = q && tran = tr -> Some nq
    |_::tl -> state_finder q tr tl
  in 
  let rec processor lst curr =
    match lst with
    | [] -> elem curr dfa.fs
    | hd::tl -> 
      let next_state = state_finder curr hd dfa.delta in
      match next_state with
      |None -> false
      |Some nq-> processor tl nq
  in processor lst dfa.q0
;;