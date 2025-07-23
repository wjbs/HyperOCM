Require Import Ltac2.Init.

Require Ltac2.Ltac2.

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