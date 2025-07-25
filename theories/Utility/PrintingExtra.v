Require Ltac2.Ltac2.
Import Ltac2.Init.

Module Message.
Include Message.

Ltac2 concats (ms : message list) : message :=
  List.fold_right concat ms (of_string "").


Ltac2 of_bool (b : bool) : message :=
  match b with 
  | true => Message.of_string "true"
  | false => Message.of_string "false"
  end.

Ltac2 _quote_str () : string := 
  String.make 1 (Char.of_int 34).

Ltac2 _quote () : message := of_string (_quote_str()).

End Message.

Module Pp.

Import Message.

(* TODO: Module Pp with bindings from pp.ml (str, brk, pr_comma, etc.)
  and notation ++ for Message.concat *)

(* TODO: Make this actually use Pp.seq in pp.ml *)
Ltac2 seq := concats.

Ltac2 Notation l(self) "++" r(self) : 2 :=
  Message.concat l r.

Ltac2 str := of_string.
(* TODO: sized_str *)
Ltac2 brk := break.
Ltac2 fnl () := force_new_line.
Ltac2 ws n := brk n 0.

(* TODO: Make this Message.empty in a future version (9.0?)*)
Ltac2 mt    () := str "".
Ltac2 spc   () := brk 1 0.
Ltac2 cut   () := brk 0 0.
Ltac2 align () := brk 0 0.
Ltac2 int      := of_int.
(* TODO : real (float) *)
Ltac2 bool     := of_bool.

(* FIXME: Make this use Message.is_empty in a future version (9.0?) *)
Ltac2 ismt m := String.is_empty (to_string m).

Ltac2 h     := hbox.
Ltac2 v   n := vbox n.
Ltac2 hv  n := hvbox n.
Ltac2 hov n := hovbox n.

(* TODO: tag *)

Ltac2 quote m := h (_quote() ++ m ++ _quote()).

Ltac2 pr_comma () := str "," ++ spc ().
Ltac2 pr_semicolon () := str ";" ++ spc ().
Ltac2 pr_bar () := str "|" ++ spc ().
Ltac2 pr_spcbar () := str " |" ++ spc ().
Ltac2 pr_arg pr x := spc () ++ pr x.
Ltac2 pr_non_empty_arg pr x := let pp := pr x in if ismt pp then mt () else spc () ++ pr x.
Ltac2 pr_opt pr := fun o => 
  match o with 
  | None => mt () 
  | Some x => pr_arg pr x
  end.
Ltac2 pr_opt_no_spc pr := fun o => match o with 
  |None => mt () 
  | Some x => pr x
  end.
Ltac2 pr_opt_default prdf pr := fun o => match o with 
  | None => prdf () 
  | Some x => pr_arg pr x
  end.
Ltac2 pr_opt_no_spc_default prdf pr := fun o => 
  match o with 
  | None => prdf () 
  | Some x => pr x
  end.

Ltac2 pr_nth n :=
  let s :=
    if Int.equal (Int.mod (Int.div n 10) 10) 1 then "th"
    else match Int.mod n 10 with
    | 1 => "st"
    | 2 => "nd"
    | 3 => "rd"
    | _ => "th"
    end
  in
  int n ++ str s.


Ltac2 prlist pr l := seq (List.map pr l).

Ltac2 prlist_sep_lastsep (no_empty : bool) (sep_thunk : unit -> message) 
  (lastsep_thunk : unit -> message) (elem : 'a -> message) (l : 'a list) : message :=
  let sep := sep_thunk () in
  let lastsep := lastsep_thunk () in
  let elems := List.map elem l in
  let filtered_elems :=
    if no_empty then
      List.filter (fun e => Bool.neg (String.is_empty (to_string e))) elems
    else
      elems
  in
  let rec insert_seps es :=
    match es with
    | []     => of_string ""
    | h :: rest => match rest with 
      | [] => h
      | e :: rest' => match rest' with 
        | [] => h ++ lastsep ++ e
        | _ => concats [h; sep; insert_seps (e :: rest')]
        end
      end
    end
  in
  insert_seps filtered_elems.

Ltac2 prlist_strict pr l := prlist_sep_lastsep true 
  (fun () => of_string "") (fun () => of_string "") pr l.
(* [prlist_with_sep sep pr [a ; ... ; c]] outputs
   [pr a ++ sep() ++ ... ++ sep() ++ pr c] *)
Ltac2 prlist_with_sep sep pr l := 
  prlist_sep_lastsep false sep sep pr l.


(* Print sequence of objects separated by space (unless an element is empty) *)
Ltac2 pr_sequence pr l := prlist_sep_lastsep true spc spc pr l.
(* [pr_enum pr [a ; b ; ... ; c]] outputs
   [pr a ++ str "," ++ pr b ++ str "," ++ ... ++ str "and" ++ pr c] *)
Ltac2 pr_enum pr l := prlist_sep_lastsep true pr_comma (fun () => str " and" ++ spc ()) pr l.

Ltac2 pr_choice pr l := prlist_sep_lastsep true pr_comma (fun () => str " or" ++ spc ()) pr l.

Ltac2 pr_vertical_list pr := fun l => match l with
  | [] => str "none" ++ fnl ()
  | l => fnl () ++ str "  " ++ hov 0 (prlist_with_sep fnl pr l) ++ fnl ()
  end.

(* [prvecti_with_sep sep pr [|a0 ; ... ; an|]] outputs
   [pr 0 a0 ++ sep() ++ ... ++ sep() ++ pr n an] *)

Ltac2 prvecti_with_sep sep elem v :=
  let v := Array.mapi (fun i x =>
      let pp := if Int.equal i 0 then mt() else sep() in
      pp ++ elem i x)
      v
  in
  seq (Array.to_list v).

(* [prvecti pr [|a0 ; ... ; an|]] outputs [pr 0 a0 ++ ... ++ pr n an] *)

Ltac2 prvecti elem v := prvecti_with_sep mt elem v.

(* [prvect_with_sep sep pr [|a ; ... ; c|]] outputs
   [pr a ++ sep() ++ ... ++ sep() ++ pr c] *)

Ltac2 prvect_with_sep sep elem v := prvecti_with_sep sep (fun _ => elem) v.

(* [prvect pr [|a ; ... ; c|]] outputs [pr a ++ ... ++ pr c] *)

Ltac2 prvect elem v := prvect_with_sep mt elem v.

Ltac2 surround p := hov 1 (str"(" ++ p ++ str")").


End Pp.

Module PpExtra.

Include Pp.

Ltac2 pr_colon () := str ":" ++ spc().
Ltac2 pr_spccolon () := str " :" ++ spc().

Ltac2 surround_braket p := hov 1 (str"[" ++ p ++ str"]").

End PpExtra.

Include Message.

Include Printf.

(* Ltac2 print_sep_list' sep (l : 'a list) (f : 'a -> message) : message :=
  List.fold_right (fun a m =>
    Message.concat (f a) (Message.concat 
    (if String.is_empty (Message.to_string m) then (Message.of_string "") else sep) m)) 
    l (Message.of_string ""). *)

Import PpExtra.


Ltac2 of_list (pr : 'a -> message) : 'a list -> message := fun l => 
  str "[" ++ prlist_with_sep pr_comma pr l ++ str "]".



Ltac2 print_sep_list sep (l : 'a list) (f : 'a -> string) : string :=
  List.fold_right (fun a m =>
    Message.to_string (fprintf "%s%s%s" (f a)
    (if String.is_empty m then "" else sep) m)) l "".

Ltac2 print_cs_list (l : 'a list) (f : 'a -> string) : string :=
  print_sep_list ", " l f.






Ltac2 print_map (pr_k : 'k -> message) (pr_v : 'v -> message) : ('k, 'v) FMap.t -> message := 
  fun m => concats [str "{" ; 
  prlist_with_sep pr_comma
    (fun (k, v) => 
    pr_k k ++ str " : " ++ pr_v v) (FMap.bindings m)
    ; str "}"].

Ltac2 print_int_map m := print_map of_int of_int m.

Ltac2 print_set (pr_v : 'v -> message) : 'v FSet.t -> message := 
  fun s => concats [of_string "{" ; 
  prlist_with_sep pr_comma
    pr_v (FSet.elements s)
    ; of_string "}"].

Ltac2 print_int_set m := print_set of_int m.


Ltac2 pr_int_set (s : int FSet.t) : message :=
  concats [str "{";
    prlist_with_sep pr_comma int (FSet.elements s);
    str "}"
  ].

Ltac2 pr_int_list (s : int list) : message :=
  concats [str "[";
    prlist_with_sep pr_comma int s;
    str "]"
  ].

