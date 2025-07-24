Require Ltac2.Ltac2.
Import Ltac2.Init.
Require Import PrintingExtra.


(* A test is a function taking printers for info, warnings, and errors
  which returns a boolean *)
Ltac2 Type t := 
    (message -> unit) -> (* Info printer *)
    (message -> unit) -> (* Warning printer *)
    (message -> unit) -> (* Error printer *)
    (unit -> bool).



Ltac2 pr_with_prefix (m : message) : message -> unit :=
  fun m' => 
  Message.print (Message.concat 
  (Message.concat m (Message.break 1 0)) m').

Ltac2 pr_info m := 
  pr_with_prefix (Message.of_string "[INFO]") m.
Ltac2 pr_warn m := 
  pr_with_prefix (Message.of_string "[WARNING]") m.
Ltac2 pr_err m := 
  pr_with_prefix (Message.of_string "[ERROR]") m.

Ltac2 noprint (_ : message) : unit := ().



(* Run a test, printing all messages as-is *)
Ltac2 run_raw (test : unit -> t) : bool :=
  test () Message.print Message.print Message.print ().

(* Run a test, printing all messages with prefixes indicating their type *)
Ltac2 run (test : unit -> t) : bool :=
  test () pr_info pr_warn pr_err ().

(* Run a test, printing any warnings and errors but no info *)
Ltac2 check (test : unit -> t) : bool :=
  test ()
    noprint 
    pr_warn
    pr_err
    ().

(* Run a test, printing only errors and throwing a fatal exception 
  if the result is false*)
Ltac2 assert (test : unit -> t) : unit :=
  match test () noprint noprint pr_err () with
  | true => ()
  | false => Control.throw Assertion_failure
  end.

(* Versions of running a test for lists of labeled tests *)

Ltac2 run_raws (tests : (string * (unit -> t)) list) : bool :=
  List.fold_left (fun b (name, t) => 
  pr_info (Message.of_string (String.app "Running test: " name));
  Bool.and (run_raw t) b) true tests.

Ltac2 runs (tests : (string * (unit -> t)) list) : bool :=
  List.fold_left (fun b (name, t) => 
  pr_info (Message.of_string (String.app "Running test: " name));
  Bool.and (run t) b) true tests.

Ltac2 checks (tests : (string * (unit -> t)) list) : bool :=
  List.fold_left (fun b (name, t) => 
  pr_info (Message.of_string (String.app "Running test: " name));
  Bool.and (check t) b) true tests.

Ltac2 asserts (pr_run : message -> unit) 
  (tests : (string * (unit -> t)) list) : unit :=
  List.iter (fun (name, t) => 
  pr_run (Message.of_string (String.app "Running test: " name));
  assert t) tests.

(** Common assertion constructors *)

Ltac2 notest () : t :=
  fun _info _warn _err () => true.

Ltac2 seq : t -> t -> t := fun test1 test2 => 
  fun info warn err () => 
  match test1 info warn err () with 
  | true => test2 info warn err ()
  | false => false
  end.

Ltac2 seqs : t list -> t := fun tests => 
  List.fold_right seq tests (notest ()).

Ltac2 foreach (l : 'a list) (f : 'a -> t) : t :=
  seqs (List.map f l).

(* Returns the boolean value, printing the message if the value is false *)
Ltac2 with_err (pr : message -> unit) (m : message) (b : bool) : bool :=
  match b with 
  | true => true
  | false => pr m; false
  end.

(* Returns the boolean value, printing the string if the value is false *)
Ltac2 with_errs (pr : message -> unit) (s : string) (b : bool) : bool :=
  match b with 
  | true => true
  | false => pr (Message.of_string s); false
  end.

Import PpExtra.

(* Tests that an optional value is Some, and satisfies a condition, 
  using a printer for better info/error messages *)
Ltac2 opt_is_some_suchthat_pr (pr : 'a -> message) (on_err : string) 
  (test : 'a -> bool) (test_val : 'a option) : t :=
  fun info _warn err () =>
  match test_val with 
  | None => let err_msg := str "Value was None," ++ spc() ++ 
    str "not Some! Message" ++ pr_colon() ++ str on_err in 
    err err_msg;
    false
  | Some v => 
    info (str "Value was Some" ++ spc() ++ pr v);
    let err_msg := str "Value" ++ spc() ++ pr v ++ spc() ++
      str "did not sasisfy" ++spc() ++
      str "condition. Message" ++ pr_colon() ++ str on_err in 
    with_err err err_msg (test v)
  end.

(* Tests that an optional value is Some,
  using a printer for better info/error messages *)
Ltac2 opt_is_some_pr (pr : 'a -> message) (on_err : string) 
  (test_val : 'a option) : t :=
  opt_is_some_suchthat_pr pr on_err (fun _ => true) test_val.

(* Tests that an optional value is None, 
  using a printer for better info/error messages *)
Ltac2 opt_is_none_pr (pr : 'a -> message) (on_err : string) 
  (test_val : 'a option) : t :=
  fun info _warn err () =>
  match test_val with 
  | None => true
  | Some v => 
    info (str "Value was Some" ++ spc() ++ pr v);
    let err_msg := str "Value Some" ++ spc() ++ pr v ++ spc() ++
      str "was Some," ++spc() ++
      str "not none. Message" ++ pr_colon() ++ str on_err in 
    err err_msg;
    false
  end.


(* Tests that an optional value is Some and satisfies a condition *)
Ltac2 opt_is_some_suchthat (on_err : string) 
  (test : 'a -> bool) (test_val : 'a option) : t :=
  fun _info _warn err () =>
  match test_val with 
  | None => let err_msg := str "Value was None," ++ spc() ++ 
    str "not Some! Message" ++ pr_colon() ++ str on_err in 
    err err_msg;
    false
  | Some v => 
    let err_msg := str "Value was Some, but" ++ spc() ++ 
      str "did not sasisfy" ++spc() ++
      str "condition. Message" ++ pr_colon() ++ str on_err in 
    with_err err err_msg (test v)
  end.

(* Tests that an optional value is Some *)
Ltac2 opt_is_some (on_err : string) 
  (test_val : 'a option) : t :=
  opt_is_some_suchthat on_err (fun _ => true) test_val.

(* Tests that an optional value is None *)
Ltac2 opt_is_none (on_err : string) 
  (test_val : 'a option) : t :=
  fun _info _warn err () =>
  match test_val with 
  | None => true
  | Some _ => 
    let err_msg := str "Value was Some," ++ spc() ++ 
      str "not none. Message" ++ pr_colon() ++ str on_err in 
    err err_msg;
    false
  end.

(* TODO: Change order of ops *)
(* Tests two values for equality, using a printer for better info/error messages *)
Ltac2 value_eq_pr (eq : 'a -> 'a -> bool) (pr : 'a -> message)
  (expected : unit -> 'a) (test_val : unit -> 'a) (on_err : string) : t :=
  fun info _warn err () => 
  let ev := expected () in 
  info (Message.concat (Message.of_string "Expected value: ") (pr ev));
  let v := test_val () in 
  info (Message.concat (Message.of_string "Actual value:   ") (pr v));
  let res := eq ev v in 
  let base_err_msg := Message.concat (Message.concat (Message.concat 
    (Message.of_string "Values did not match! Expected ")
    (pr ev))
    (Message.of_string ", got "))
    (pr v) in
  let err_msg := Message.concat (Message.concat 
    base_err_msg 
    (Message.of_string ". Message: "))
    (Message.of_string on_err) in
  with_err err err_msg res.

(* Tests two values for equality *)
Ltac2 value_eq (eq : 'a -> 'a -> bool)
  (expected : unit -> 'a) (test_val : unit -> 'a) (on_err : string) : t :=
  fun _info _warn err () => 
  let ev := expected () in 
  let v := test_val () in 
  let res := eq ev v in 
  let err_msg := Message.concat 
    (Message.of_string "Values did not match! Message: ")
    (Message.of_string on_err) in
  with_err err err_msg res.

(* Tests two unthunked values for equality, using a printer for better info/error messages *)
Ltac2 value_eqv_pr (eq : 'a -> 'a -> bool) (pr : 'a -> message)
  (on_err : string) (expected : 'a) (test_val : 'a) : t :=
  value_eq_pr eq pr (fun () => expected) (fun () => test_val) on_err.

(* Tests two unthunked values for equality *)
Ltac2 value_eqv (eq : 'a -> 'a -> bool)
  (on_err : string) (expected : 'a) (test_val : 'a) : t :=
  value_eq eq (fun () => expected) (fun () => test_val) on_err.

(* Tests two optional values for equality *)
Ltac2 opt_eq (eq : 'a -> 'a -> bool)
  (on_err : string)
  (expected : unit -> 'a option) (test_val : unit -> 'a option) : t :=
  value_eq (Option.equal eq) test_val expected on_err.

(* Tests two optional values for equality, using a printer for better info/error messages *)
Ltac2 opt_eq_pr (eq : 'a -> 'a -> bool) (pr : 'a -> message) (on_err : string)
  (expected : unit -> 'a option) (test_val : unit -> 'a option) : t :=
  value_eq_pr (Option.equal eq) (Pp.pr_opt pr) test_val expected on_err.

(* Tests two ints for equality *)
Ltac2 int_eq 
  (on_err : string)
  (expected : unit -> int) (test_val : unit -> int) : t :=
  value_eq_pr Int.equal Message.of_int test_val expected on_err.

(* Tests two bools for equality *)
Ltac2 bool_eq 
  (on_err : string)
  (expected : unit -> bool) (test_val : unit -> bool) : t :=
  value_eq_pr Bool.equal of_bool test_val expected on_err.

(* Tests two strings for equality *)
Ltac2 string_eq 
  (on_err : string)
  (expected : unit -> string) (test_val : unit -> string) : t :=
  value_eq_pr String.equal Message.of_string test_val expected on_err.

(* Tests two lists of ints for equality *)
Ltac2 int_list_eq 
  (on_err : string)
  (expected : unit -> int list) (test_val : unit -> int list) : t :=
  value_eq_pr (List.equal Int.equal)
  (of_list Message.of_int) test_val expected on_err.

(* Tests two unthunked optional values for equality *)
Ltac2 opt_eqv (eq : 'a -> 'a -> bool)
  (on_err : string)
  (expected : 'a option) (test_val : 'a option) : t :=
  value_eq (Option.equal eq) (fun () => test_val) (fun () => expected) on_err.

(* Tests two unthunked optional values for equality, using a printer for better info/error messages *)
Ltac2 opt_eqv_pr (eq : 'a -> 'a -> bool) (pr : 'a -> message) (on_err : string)
  (expected : 'a option) (test_val : 'a option) : t :=
  value_eq_pr (Option.equal eq) (Pp.pr_opt pr) (fun () => test_val) (fun () => expected) on_err.

(* Tests two unthunked optional ints for equality *)
Ltac2 int_opt_eqv 
  (on_err : string)
  (expected : int option) (test_val : int option) : t :=
  opt_eqv_pr Int.equal Pp.int on_err expected test_val.

(* Tests two unthunked ints for equality *)
Ltac2 int_eqv 
  (on_err : string)
  (expected : int) (test_val : int) : t :=
  value_eq_pr Int.equal Message.of_int 
    (fun () => test_val) (fun () => expected) on_err.

(* Tests two unthunked bools for equality *)
Ltac2 bool_eqv 
  (on_err : string)
  (expected : bool) (test_val : bool) : t :=
  value_eq_pr Bool.equal of_bool 
    (fun () => test_val) (fun () => expected) on_err.

(* Tests two unthunked strings for equality *)
Ltac2 string_eqv 
  (on_err : string)
  (expected : string) (test_val : string) : t :=
  value_eq_pr String.equal Message.of_string 
  (fun () => test_val) (fun () => expected) on_err.

(* Tests two unthunked lists of ints for equality *)
Ltac2 int_list_eqv 
  (on_err : string)
  (expected : int list) (test_val : int list) : t :=
  value_eq_pr (List.equal Int.equal)
  (of_list Message.of_int) 
  (fun () => test_val) (fun () => expected) on_err.

(* Ltac2 example () : t := 
  bool_eq "Equality should be reflexive" 
    (fun () => true) (fun () => true).
Ltac2 examplev () : t := 
  bool_eqv "Equality should be reflexive" true true. *)
