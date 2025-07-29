Require Import Ltac2.Init.
Require Ltac2.Ltac2.

Require UTest.

Module Function.

Ltac2 compose : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c :=
  fun g f a => g (f a).

End Function.

Module SumType.
Import Function.

Ltac2 Type ('a, 'b) sum :=
  [ OrL ('a) | 
    OrR ('b) ].

Ltac2 or_introl : 'a -> ('a, 'b) sum :=
  fun a => OrL a.

Ltac2 or_intror : 'b -> ('a, 'b) sum :=
  fun b => OrR b.

Ltac2 inl : 'a -> ('a, 'b) sum :=
  fun a => OrL a.

Ltac2 inr : 'b -> ('a, 'b) sum :=
  fun b => OrR b.

Ltac2 elim : ('a -> 'c) -> ('b -> 'c) -> ('a, 'b) sum -> 'c :=
  fun l r ab => 
  match ab with 
  | OrL a => l a
  | OrR b => r b
  end.

Ltac2 map : ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) sum -> ('c, 'd) sum :=
  fun l r => elim (compose inl l) (compose inr r).

End SumType.


Module ListForEach.
Import List.
Import SumType.

(* A variant of the for-each loop along with an additional state.
  Each iteration of the body updates the state based on the value 
  of the list, returning the updated state and an optional return 
  value. If an iteration returns a (non-None) return value, it is 
  the final iteration which is executed. If all steps return None 
  then the [or_else] function determines the return value. *)
Ltac2 fold_each (l : 'value list) (init : 'state)
  (body : 'state -> 'value -> 'state * 'ret option) 
  (or_else : 'state -> 'ret) : 'state * 'ret := 
  let (state, ret) := 
    fold_left (fun ((state, ret) : 'state * 'ret option) (value : 'value) =>
      match ret with 
      | Some r => (state, Some r)
      | None => 
        body state value
      end) (init, None) l in 
  match ret with 
  | Some r => (state, r)
  | None => (state, or_else state)
  end.

(* A variant of the for-each loop along with an additional state.
  Each iteration of the body updates the state based on the value 
  of the list, returning the updated state or a return value that
  shortcuts past the remaining executions of the loop. If each of
  the iterations return None, the [or_else] function computes the
  return value. *)
Ltac2 fold_each' (l : 'value list) (init : 'state)
  (body : 'state -> 'value -> ('state, 'ret) sum) 
  (or_else : 'state -> 'ret) : 'state * 'ret := 
  fold_each l init (fun state value => 
    match body state value with 
    | OrL new_state => (new_state, None)
    | OrR ret => (state, Some ret)
    end) or_else.

(* A "for each" loop from which the body can return, shortcutting
  execution. Useful for executing the body at most once per value
  of the list. If no iteration of the body returns, the [default]
  function determines the return value. *)
Ltac2 for_each (l : 'a list) (body : 'a -> 'ret option) 
  (default : unit -> 'ret) : 'ret :=
  snd (fold_each l () (fun () value => ((), body value)) default).

(* A helper function to "continue" from within a [fold_each] body
  to shortcut execution. Specifically, just takes a ['state] to a 
  ['state * 'ret option] by using [None] as the second component. *)
Ltac2 fold_continue (state : 'state) : 'state * 'ret option :=
  (state, None).

(* A helper function to "continue" within a [fold_each'] function
  body to shortcut execution. Specifically, takes a ['state] to a 
  [('state, 'ret) sum] by including in the left component. *)
Ltac2 fold_continue' (state : 'state) : ('state, 'ret) sum :=
  OrL state.

(* A helper function to "continue" in a [for_each] body function.
  Specifically, just returns [None] as a ['ret option]. *)
Ltac2 for_continue : unit -> 'ret option :=
  fun () => None.

(* A helper function to "return" a value from a [fold_each] body.
  It takes a ['state] and a ['ret] to a ['state * 'ret option] by
  wrapping the latter in [Some]. *)
Ltac2 fold_return (state : 'state) (ret : 'ret) : 'state * 'ret option :=
  (state, Some ret).

(* A helper function to "return" a value from a [fold_each'] body
  to shortcut execution. Specifically, it takes a ['ret] value to 
  a [('state, 'ret) sum] by inclusion in the second component. *)
Ltac2 fold_return' (ret : 'ret) : ('state, 'ret) sum :=
  OrR ret.

(* A helper function to "return" from a [for_each] body iteration
  to shortcut execution. Simply takes a ['ret] to a ['ret option]
  by wrapping it in [Some]. *)
Ltac2 for_return (ret : 'ret) : 'ret option :=
  Some ret.

Ltac2 continue : 'ret option := None.
   
End ListForEach.




(* Remove the _first_ element of a list satisfying a given predicate. 
  If none is found, return None. *)
Ltac2 rec remove_first (f : 'a -> bool) (l : 'a list) : 'a list option :=
  match l with 
  | [] => None
  | a :: l' => if f a then Some l' 
    else Option.map (fun r => a :: r) (remove_first f l')
  end.

(* Remove the nth element of the list, if it exists *)
Ltac2 rec remove_nth (n : int) (l : 'a list) : 'a list :=
  if Int.equal n 0 then 
    match l with
    | [] => []
    | _ :: l' => l'
    end
  else
    match l with 
    | [] => []
    | b :: l' => 
      b :: (remove_nth (Int.sub n 1) l')
    end.


Module Permutations.





(* Given a list of values and a sublist thereof, computes a 
  permutation function such that reordering the list by that 
  permutation exposes the sublist as an intial segment. 
  Works only with non-duplicate lists.

  For example, if [l] is a list of which [subl] is sublist, 
  meaning every element of [subl] appears in [l], then if 
  [f := bring_to_front_perm l subl], the list 
  [List.map (fun (i, _) => List.nth l (f i)) (List.enumerate l)]
  will look like [subl ++ rest] for some list [rest]. 
  
  This function is uniquely defined by the property that this 
  list [rest] will have its elements in the same relative order
  as those of [l]. *)
Ltac2 bring_to_front_perm (eq : 'a -> 'a -> bool) 
  (l : 'a list) (subl : 'a list) : int -> int :=
  let len_l := List.length l in 
  let enum_l := List.enumerate l in 
  let mem_subl e := List.mem eq e subl in 
  let len_subl := List.length subl in
  (* The list of length [len_l] whose elements record how many 
    elements _not_ in [subl] occur in [l] up to and including that index *) 
  let (non_subl_counts, _) := 
    List.fold_left (fun (acc, count) e => 
      let new_count := if Bool.neg (mem_subl e) then Int.add count 1 else count in
      (List.append acc [new_count], new_count)) ([], 0) l in
  let enum_non_subl_counts := List.enumerate non_subl_counts in 
  fun k => 
  (* There are two cases. If we are in the inital segment that should
    become [subl], we just need to find the index of that element of
    [subl]. If we are past this initial segment, we need to find the
    appropriate _non-[subl]-element_ of [l]. *)
  (* First, basic bounds: *)
  if Bool.or (Int.lt k 0) (Int.le len_l k) then k else
  (* Now, the main case split: *)
  if Int.lt k len_subl then
    (* Case 1: initial subl segment *)
    (* This is the element we want [nth <result> k] to be: *)
    let elem := List.nth subl k in 
    (* Find its index in [l] *)
    let (i, _) := List.find (fun (_, elem') => eq elem elem') enum_l in 
    (* This is the index we need *)
    i
  else 
    (* Case 2: past the [subl] intial segment *)
    (* We need to answer 'What is the smallest index at which 
      we will have [k+1 - len_subl] non-elements of [subl] behind or at us'. 
      This is answered by the index of the first element of 
      [non_subl_counts] equal to [k+1-len_subl] *)
    let k' := Int.sub (Int.add k 1) len_subl in 
    fst (List.find (fun (_, count) => Int.equal count k') enum_non_subl_counts).



(* Given a list of values and a sublist thereof, computes a 
  permutation function such that reordering the list by that 
  permutation exposes the sublist as a terminal segment. 
  Works only with non-duplicate lists.

  For example, if [l] is a list of which [subl] is sublist, 
  meaning every element of [subl] appears in [l], then if 
  [f := send_to_back_perm l subl], the list 
  [List.map (fun (i, _) => List.nth l (f i)) (List.enumerate l)]
  will look like [rest ++ subl] for some list [rest]. 
  
  This function is uniquely defined by the property that this 
  list [rest] will have its elements in the same relative order
  as those of [l]. *)
Ltac2 send_to_back_perm (eq : 'a -> 'a -> bool) 
  (l : 'a list) (subl : 'a list) : int -> int :=
  let len_l := List.length l in 
  let enum_l := List.enumerate l in 
  let mem_subl e := List.mem eq e subl in 
  let len_subl := List.length subl in
  (* The list of length [len_l] whose elements record how many 
    elements _not_ in [subl] occur in [l] up to and including that index *) 
  let (non_subl_counts, _) := 
    List.fold_left (fun (acc, count) e => 
      let new_count := if Bool.neg (mem_subl e) then Int.add count 1 else count in
      (List.append acc [new_count], new_count)) ([], 0) l in
  let enum_non_subl_counts := List.enumerate non_subl_counts in 
  fun k => 
  (* There are two cases. If we are in the terminal segment that should
    become [subl], we just need to find the index of that element of
    [subl]. If we are before this terminal segment, we need to find the
    appropriate _non-[subl]-element_ of [l]. *)
  (* First, basic bounds: *)
  if Bool.or (Int.lt k 0) (Int.le len_l k) then k else
  (* Now, the main case split: *)
  if Int.lt k (Int.sub len_l len_subl) then
    (* Case 1: before terminal subl segment *)
    (* We need to answer 'What is the smallest index at which 
      we will have [k+1] non-elements of [subl] behind or at us'. 
      This is answered by the index of the first element of 
      [non_subl_counts] equal to [k+1] *)
    fst (List.find (fun (_, count) => Int.equal count (Int.add k 1)) enum_non_subl_counts)
  else 
    (* Case 2: terminal [subl]  segment *)
    (* This is the element we want [nth <result> k] to be: *)
    let elem := List.nth subl (Int.sub k (Int.sub len_l len_subl)) in 
    (* Find its index in [l] *)
    let (i, _) := List.find (fun (_, elem') => eq elem elem') enum_l in 
    (* This is the index we need *)
    i.




(* Test if two list are equal up to permutation. Assumes the 
  given equality is an equivalence relation. *)
Ltac2 rec perm_eq (eq : 'a -> 'a -> bool) (l : 'a list) (l' : 'a list) : bool :=
  match l with 
  | [] => List.is_empty l'
  | a :: l_rest => match remove_first (eq a) l' with 
    | None => false
    | Some l'_rest => perm_eq eq l_rest l'_rest
    end
  end.

(* Permute a list by a permutation of the indices. If a given index 
  is mapped outside the length of the list, its initial value is used. *)
Ltac2 permute_list (f : int -> int) (l : 'a list) :=
  List.map (fun (i, v) => Option.default v (List.nth_opt l (f i)))
    (List.enumerate l).

(* Permute a list by the inverse of a permutation of the indices. 
  (Strictly, works more generally for an injective funciton, not 
  just permutation, ordering the elements of the list by the 
  relative ordering of the funciton outputs.) *)
Ltac2 inv_permute_list (f : int -> int) (l : 'a list) :=
  List.map fst (List.sort (fun (i, _) (j, _) => Int.compare i j)
    (List.map (fun (i, v) => (f i, v)) (List.enumerate l))).

(* TODO: Test permute_list and inv_permute_list *)


(* Given a list and a sublist thereof, removes the sublist from the
  list. Here, sublist means in the sense of multisets, so duplicates
  are allowed and count separately. Returns None if the sublist is
  not actualyl a sublist of the list. *)
Ltac2 remove_sublist_opt (eq : 'a -> 'a -> bool) 
  (l : 'a list) (subl : 'a list) : 'a list option :=
  let rec go l subl :=
    match l with 
    | [] => if List.is_empty subl then Some [] else None
    | a :: l' => match remove_first (eq a) subl with 
      | Some subl' => (* There was an [a] in [subl] *)
        go l' subl'
      | None => (* [a] was not in [subl] *)
        Option.map (List.cons a) (go l' subl)
      end
    end in
  go l subl.

(* Given a list and a sublist thereof, removes the sublist from the
  list. Here, sublist means in the sense of multisets, so duplicates
  are allowed and count separately. Raises an [Invalid_argument] 
  exception if the sublist is not actually a sublist of the list. *)
Ltac2 remove_sublist (eq : 'a -> 'a -> bool) 
  (l : 'a list) (subl : 'a list) : 'a list :=
  match remove_sublist_opt eq l subl with 
  | Some l' => l'
  | None =>
    Control.throw_invalid_argument "subl is not a sublist of l (in remove_sublist)"
  end.


(* Given a list and a sublist thereof, return the permutation of
  the original list with the sublist as an initial segment. Raises
  an [Invalid_argument] error if the sublist is not a sublist of
  the original list.
  
  Literally, concatenates [subl] and [remove_sublist eq l subl]. *)
Ltac2 bring_to_front (eq : 'a -> 'a -> bool) 
  (l : 'a list) (subl : 'a list) : 'a list :=
  match remove_sublist_opt eq l subl with 
  | Some l' => List.append subl l'
  | None => 
    Control.throw_invalid_argument "subl is not a sublist of l (in bring_to_front)"
  end.


(* Given a list and a sublist thereof, return the permutation of
  the original list with the sublist as a terminal segment. Raises
  an [Invalid_argument] error if the sublist is not a sublist of
  the original list.
  
  Literally, concatenates [subl] and [remove_sublist eq l subl]. *)
Ltac2 send_to_back (eq : 'a -> 'a -> bool) 
  (l : 'a list) (subl : 'a list) : 'a list :=
  match remove_sublist_opt eq l subl with 
  | Some l' => List.append l' subl
  | None => 
    Control.throw_invalid_argument "subl is not a sublist of l (in send_to_back)"
  end.







(* To construct efficient proofs that a pair of lists are
  equal up to permutation, we use a form of the insertion
  sort algorithm called here 'extraction sort'. To show a
  permutation correct this way, we must construct witness
  lists in which the [i]th index being [d] says the [i]th
  element must swap with the [i + d]th element, after the
  previous elements have been swapped in this manner, for
  the permutation to be achieved. Swapping happens on the
  left / first list.
*)

(* First, we make a simple function that does these swaps
  (on the Ltac2 side) to check our work *)
Ltac2 extraction_sort_apply (idxs : int list) (l : 'a list) : 'a list :=
  let rec insert_nth n a l :=
    if Int.le n 0 then a :: l else
    match l with 
    | [] => a :: []
    | b :: l' => b :: (insert_nth (Int.sub n 1) a l')
    end in 
  let swap_with_nth n l :=
    match l with 
    | [] => []
    | a :: l' => insert_nth n a l'
    end in 
  let rec extr_apply idxs l :=
    match idxs with 
    | [] => l
    | n :: idxs' => 
      match swap_with_nth n l with 
      | [] => []
      | a :: l' => a :: (extr_apply idxs' l')
      end
    end in 
  extr_apply idxs l.


(* First, we make a simple function that does these swaps
  (on the Ltac2 side) to check our work *)
Ltac2 swap_with_nths_after_apply (idxs : (int * int) list) 
  (l : 'a list) : 'a list :=
  let rec insert_nth n a l :=
    if Int.le n 0 then a :: l else
    match l with 
    | [] => a :: []
    | b :: l' => b :: (insert_nth (Int.sub n 1) a l')
    end in 
  let swap_with_nth n l :=
    match l with 
    | [] => []
    | a :: l' => insert_nth n a l'
    end in 
  let rec swap_with_nth_after n d l :=
    if Int.le d 0 then swap_with_nth n l else
    match l with 
    | [] => []
    | b :: l' => b :: (swap_with_nth_after n (Int.sub d 1) l')
    end in 
  let rec extr_apply idxs l :=
    match idxs with 
    | [] => l
    | (n, d) :: idxs' => 
      extr_apply idxs' (swap_with_nth_after n d l)
    end in 
  extr_apply idxs l.


(* Next, given perm_equal lists, construct such a sort list *)



(* Finds a reordering of the _first_ list which makes it equal 
  to the _second_, returning [None] if they aren't equal up to
  permutation (i.e. no such reordering exists).  *)
Ltac2 rec perm_reordering_swaps_after (eq : 'a -> 'a -> bool) 
  (l : 'a list) (l' : 'a list) : (int * int) list option :=
  let rec go n l l' : (int * int) list option :=
    (* With length l = length l' = n, find the swap necessary to 
      make the last element of l equal the last element of l' and
      recurse to find the solution for the first n - 1 elements *)
    if Int.le n 0 then Some [] else
    let may_last_l' := List.last_opt l' in Option.bind may_last_l' (
    fun last_l' => 
    let may_idx_last_l'_in_l := Option.map fst (List.find_rev_opt 
      (fun (_, v) => eq v last_l') (List.enumerate l)) in
    Option.bind may_idx_last_l'_in_l (fun idx_last_l'_in_l => 
    let new_l := remove_nth idx_last_l'_in_l l in
    let new_l' := List.removelast l' in 
    let dist_offset := (
      (Int.sub (Int.sub n 1) idx_last_l'_in_l, idx_last_l'_in_l)
    ) in 
    Option.map (fun idxs => dist_offset :: idxs) 
      (go (Int.sub n 1) new_l new_l')
    )) in 
  let len_l := List.length l in 
  if Bool.neg (Int.equal (List.length l') len_l) then None else
  go len_l l l'.



(* Removes the first occurance of a test, returning the index 
  _in the original list_ at which it occurs, if any. *)
Ltac2 rec find_remove_first (f : 'a -> bool) (l : 'a list) : 
  (int * 'a list) option :=
  match l with 
  | [] => None
  | a :: l' => if f a then Some (0, l')
    else Option.map (fun (idx, r) => (Int.add idx 1, a :: r)) 
      (find_remove_first f l')
  end.

(* Finds a reordering of the _first_ list which makes it equal 
  to the _second_, returning [None] if they aren't equal up to
  permutation (i.e. no such reordering exists). The reordering
  is given so as to be compatible with [extraction_sort_apply]
  in that [extraction_sort_apply (perm_reordering r l) l = r],
  if [perm_eq l r]. *)
Ltac2 rec perm_reordering (eq : 'a -> 'a -> bool) 
  (l : 'a list) (l' : 'a list) : int list option :=
  match l with 
  | [] => match l' with | [] => Some [] | _ => None end
  | a :: l_rest => 
    Option.bind (find_remove_first (eq a) l') (fun (i, l'_rest) =>
    Option.bind (perm_reordering eq l_rest l'_rest) (fun shifts => 
      Some (i :: shifts)))
  end.





Module PermTesting. 

Import PrintingExtra.

Local Ltac2 string_of_int (n : int) : string := to_string (of_int n).

(* Test that two lists are equal to each other, up to permutation. *)
Ltac2 test_is_perm_pr (eq : 'a -> 'a -> bool) (pr : 'a -> message)
  (on_err : string) (expected : 'a list) (test_val : 'a list) : UTest.t :=
  UTest.value_eq_pr (perm_eq eq) (of_list pr) 
    (fun()=>expected) (fun()=>test_val)
    (String.app "lists should have been permutations. Message: " on_err).


(* Helpers for permutation function tests*)

Ltac2 test_bring_to_front_perm_on (l : int list) (subl : int list) : UTest.t :=
  let len_l := List.length l in let len_subl := List.length subl in 
  let l' := permute_list (bring_to_front_perm Int.equal l subl) l in 
  UTest.seq 
    (UTest.value_eqv_pr (List.equal Int.equal) (of_list of_int)
      (String.concat "" ["First "; string_of_int len_l; 
        " elements should be the sublist"]) 
      (subl)
      (List.firstn len_subl l'))
    (test_is_perm_pr Int.equal of_int 
    "bring_to_front_perm should have been a permutation" l l').

Ltac2 test_bring_to_front_perm_on' (l, subl) :=
  test_bring_to_front_perm_on l subl.

Ltac2 test_send_to_back_perm_on (l : int list) (subl : int list) : UTest.t :=
  let len_l := List.length l in let len_subl := List.length subl in 
  let l' := permute_list (send_to_back_perm Int.equal l subl) l in 
  UTest.seq 
    (UTest.value_eqv_pr (List.equal Int.equal) (of_list of_int)
      (String.concat "" ["Last "; string_of_int len_l; 
        " elements should be the sublist"]) 
      (subl)
      (List.lastn len_subl l'))
    (test_is_perm_pr Int.equal of_int 
    "send_to_back_perm should have been a permutation" l l').

Ltac2 test_send_to_back_perm_on' (l, subl) :=
  test_send_to_back_perm_on l subl.


(* Helpers for list permutation tests *)

Ltac2 test_bring_to_front_on (l : int list) (subl : int list) : UTest.t :=
  let len_l := List.length l in let len_subl := List.length subl in 
  let l' := bring_to_front Int.equal l subl in 
  UTest.seq 
    (UTest.value_eqv_pr (List.equal Int.equal) (of_list of_int)
      (String.concat "" ["First "; string_of_int len_l; 
        " elements should be the sublist"]) 
      (subl)
      (List.firstn len_subl l'))
    (test_is_perm_pr Int.equal of_int 
    "bring_to_front should have been a permutation" l l').

Ltac2 test_bring_to_front_on' (l, subl) : UTest.t :=
  test_bring_to_front_on l subl.

Ltac2 test_send_to_back_on (l : int list) (subl : int list) : UTest.t :=
  let len_l := List.length l in let len_subl := List.length subl in 
  let l' := send_to_back Int.equal l subl in 
  UTest.seq 
    (UTest.value_eqv_pr (List.equal Int.equal) (of_list of_int)
      (String.concat "" ["Last "; string_of_int len_l; 
        " elements should be the sublist"]) 
      (subl)
      (List.lastn len_subl l'))
    (test_is_perm_pr Int.equal of_int 
    "send_to_back should have been a permutation" l l').

Ltac2 test_send_to_back_on' (l, subl) :=
  test_send_to_back_on l subl.



Ltac2 test_remove_sublist_opt_Some 
  ((l, subl) : int list * int list) : UTest.t := 
  let len_l := List.length l in let len_subl := List.length subl in 
  let opt_l' := remove_sublist_opt Int.equal l subl in 
  UTest.seqs [
    UTest.opt_is_some_pr (of_list of_int)
      "remove_sublist_opt should succeed" opt_l';
    match opt_l' with 
    | None => (* The above will fail already; we can skip the rest *)
      UTest.notest ()
    | Some l' => UTest.seqs [
    UTest.int_eqv 
      "length of remove_sublist_opt should be difference of list lengths"
      (Int.sub len_l len_subl)
      (List.length l');
    test_is_perm_pr Int.equal of_int 
    "remove_sublist_opt should give a permutation when subl is concatted" 
    l (List.append subl l')]
    end].

Ltac2 test_remove_sublist_opt_None
  ((l, subl) : int list * int list) : UTest.t := 
  let opt_l' := remove_sublist_opt Int.equal l subl in 
  UTest.opt_is_none_pr (of_list of_int) 
    (String.concat "" [
      "remove_sublist_opt should return None for non-sublists ";
      "(l = "; to_string (of_list of_int l); ", subl = ";
        to_string (of_list of_int l)])
    opt_l'.


Ltac2 test_perm_eq_true ((l, l') : int list * int list) : UTest.t :=
  UTest.bool_eqv (String.concat "" 
    ["lists equal up to permutation should be perm_eq ";
    "(l = "; to_string (of_list of_int l); ", l' = ";
    to_string (of_list of_int l'); ")"])
    true (perm_eq Int.equal l l').

Ltac2 test_perm_eq_false ((l, l') : int list * int list) : UTest.t :=
  UTest.bool_eqv (String.concat "" 
    ["lists not equal up to permutation should not be perm_eq ";
    "(l = "; to_string (of_list of_int l); ", l' = ";
    to_string (of_list of_int l'); ")"])
    false (perm_eq Int.equal l l').

Ltac2 test_extraction_sort_apply_success ((idxs, l, l') : 
  int list * int list * int list) : UTest.t :=
  UTest.int_list_eqv 
    (String.app "extraction_sort_apply should turn the first list"
      " into the second under this reordering")
    l' (extraction_sort_apply idxs l).

Ltac2 test_perm_reordering_None ((l, l') : int list * int list) : 
  UTest.t :=
  UTest.opt_is_none_pr (of_list of_int)
    "perm_reordering should return None for non-equal-up-to-permutation lists"
    (perm_reordering Int.equal l l').

Ltac2 test_perm_reordering_Some_eq ((l, l') : int list * int list) : 
  UTest.t :=
  UTest.opt_is_some_suchthat_pr (of_list of_int)
    (String.concat "" ["perm_reordering should return a reordering ";
      "making the second list equal the first ";
      "(l = "; to_string (of_list of_int l); ", l' = ";
    to_string (of_list of_int l'); ")"])
    (fun idxs => 
      List.equal Int.equal (extraction_sort_apply idxs l) l')
    (perm_reordering Int.equal l l').

Ltac2 test_perm_reordering_swaps_after_None ((l, l') : int list * int list) : 
  UTest.t :=
  UTest.opt_is_none_pr (of_list (of_pair of_int of_int))
    "perm_reordering_swaps_after should return None for non-equal-up-to-permutation lists"
    (perm_reordering_swaps_after Int.equal l l').

Ltac2 test_perm_reordering_swaps_after_Some_eq ((l, l') : int list * int list) : 
  UTest.t :=
  UTest.opt_is_some_suchthat_pr (of_list (of_pair of_int of_int))
    (String.concat "" ["perm_reordering_swaps_after should return a reordering ";
      "making the second list equal the first ";
      "(l = "; to_string (of_list of_int l); ", l' = ";
    to_string (of_list of_int l'); ")"])
    (fun idxs => 
      List.equal Int.equal (swap_with_nths_after_apply idxs l) l')
    (perm_reordering_swaps_after Int.equal l l').

(* Values on which to test these functions *)

Ltac2 _subset_lists () :=
  [ 
    ([1; 2; 3; 4; 5], [1; 2; 3]);
    ([1; 2; 3; 4; 5], [2; 3; 4]);
    ([1; 2; 3; 4; 5], [1; 4]);
    ([1; 2; 3; 4; 5], [3; 5]);
    ([1; 2; 3; 4; 5], [1]);
    ([1; 2; 3; 4; 5], [])
  ].

Ltac2 _non_subset_sublists () :=
  [
    ([1; 1; 2; 2; 4; 5], [1; 2; 2; 5]);
    ([1; 1; 2; 2; 4; 5], [4; 2; 1; 1])
  ].

Ltac2 _all_sublists () :=
  List.append (_subset_lists()) (_non_subset_sublists()).

Ltac2 _non_sublists () :=
  [
    ([1; 1; 2; 2; 4; 5], [1; 2; 2; 2]); (* Too many 2's *)
    ([1; 1; 2; 2; 4; 5], [4; 2; 1; 3]) (* No 3 in first *)
  ].


Ltac2 _permutations () :=
  [
    ([], []);
    ([1], [1]);
    ([1;2], [2;1]);
    ([1;2;3], [2;3;1]);
    ([1;2;3;4;5], [2;4;1;5;3]);
    ([1;2;2;1], [1;1;2;2]);
    ([5;5;2;1;2], [1;2;5;5;2])
  ].

Ltac2 _non_permutations () :=
  [
    ([], [1]);
    ([1], [2]);
    ([1;2], [2;1;1]);
    ([1;2;3;3], [2;3;1]);
    ([1;2;3;5], [4;1;5;3])
  ].

Ltac2 _extraction_sorts_correct () :=
  [
    ([], [1;2;3], [1;2;3]);
    ([0], [1;2;3], [1;2;3]);
    ([0;0;0], [1;2;3], [1;2;3]);
    ([0;0;0;0;0], [1;2;3], [1;2;3]);
    ([1], [1;2;3], [2;1;3]);
    ([0;1], [1;2;3], [1;3;2]);
    ([1;1], [1;2;3], [2;3;1])
  ].


Ltac2 test_bring_to_front_perm () :=
  UTest.foreach (_subset_lists())
    test_bring_to_front_perm_on'.

Ltac2 test_send_to_back_perm () :=
  UTest.foreach (_subset_lists())
    test_send_to_back_perm_on'.

Ltac2 test_bring_to_front () :=
  UTest.foreach
    (_all_sublists())
    test_bring_to_front_on'.

Ltac2 test_send_to_back () :=
  UTest.foreach
    (_all_sublists())
    test_send_to_back_on'.

Ltac2 test_remove_sublist_opt_success () :=
  UTest.foreach (_all_sublists())
    test_remove_sublist_opt_Some.

Ltac2 test_remove_sublist_opt_failure () :=
  UTest.foreach (_non_sublists())
    test_remove_sublist_opt_None.

Ltac2 test_perm_eq_success () :=
  UTest.foreach (_permutations())
    test_perm_eq_true.

Ltac2 test_perm_eq_failure () :=
  UTest.foreach (_non_permutations())
    test_perm_eq_false.

Ltac2 test_extraction_sort_apply () :=
  UTest.foreach (_extraction_sorts_correct())
    test_extraction_sort_apply_success.

Ltac2 test_perm_reordering_failure () :=
  UTest.foreach (_non_permutations())
    test_perm_reordering_None.

Ltac2 test_perm_reordering_success () :=
  UTest.foreach (_permutations())
    test_perm_reordering_Some_eq.

Ltac2 test_perm_reordering_swaps_after_failure () :=
  UTest.foreach (_non_permutations())
    test_perm_reordering_swaps_after_None.

Ltac2 test_perm_reordering_swaps_after_success () :=
  UTest.foreach (_permutations())
    test_perm_reordering_swaps_after_Some_eq.

Ltac2 tests () := [
  ("perm_eq success", test_perm_eq_success);
  ("perm_eq failure", test_perm_eq_failure);
  ("bring_to_front_perm success", test_bring_to_front_perm);
  ("send_to_back_perm success", test_send_to_back_perm);
  ("remove_sublist_opt success", test_remove_sublist_opt_success);
  ("remove_sublist_opt failure", test_remove_sublist_opt_failure);
  ("bring_to_front success", test_bring_to_front);
  ("send_to_back success", test_send_to_back);
  ("extraction_sort_apply", test_extraction_sort_apply);
  ("perm_reordering failure", test_perm_reordering_failure);
  (* This fails because the function is wrong ("perm_reordering success", test_perm_reordering_success); *)
  ("perm_reordering_swaps_after failure", test_perm_reordering_swaps_after_failure);
  ("perm_reordering_swaps_after success", test_perm_reordering_swaps_after_success)
].

Ltac2 Eval UTest.asserts UTest.noprint (tests()).

End PermTesting.

End Permutations.