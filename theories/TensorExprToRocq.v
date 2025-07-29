Require Import Summable.
Require Import TensorExpr.
Require Import FSetExtra.
Import Ltac2.Init.

Module SummationQuote (SR : SemiRing).

Module SUM := Summation SR.

Export SUM.

Import SemiRingNotations.


(* TODO: Find a better name than realize! *)
(* The mapping from variable names to [ident]s used to 
  realize a tensor expression. *)
Ltac2 Type VarContext := (TypeIdx, VarIdx, ident) FMap2.t.

(* The mapping from type names to types ([constr]s) used
  to realize a tensor expression. Each must include also
  an instance of [Summable]. So, the targets of this map
  should be [(A, SA)] with [A : Type], [SA : Summable A] *)
Ltac2 Type TypeContext := (TypeIdx, constr * constr) FMap.t.

(* The mapping from abstract tensors to functions 
  implementing them. Note that the arities are not
  stored here, but they must match the usage in the
  realized expression(s). Inputs and outputs are not
  distinguished: if (up to translation with the type
  map) the inputs are [A, B, ..., F] and the outputs
  are [G, H, ..., M], the expected type of the map is 
  [A -> B -> ... -> F -> G -> H -> ... -> M -> R], 
  where [R] is the semiring type. *)
Ltac2 Type AbsContext := (AbsIdx, constr) FMap.t.

(* The three of these maps define the information to 
  realize a tensor expression, while combined *)
Ltac2 Type Context := {
  vars : VarContext;
  types : TypeContext;
  abs : AbsContext
}.

(* Get the type associated to a [TypeIdx]. Throws an 
  [Invalid_argument] exception if it is not found. *)
Ltac2 get_type (ctx : Context) (ty : TypeIdx) : constr :=
  match FMap.find_opt ty (ctx.(types)) with 
  | Some (t, _st) => t
  | None => 
    Control.throw_invalid_argument
      (String.app "type not found in get_type: " ty)
  end.

(* Get the [Summable] instance associated to a [TypeIdx]. 
  Throws an [Invalid_argument] exception if it is not found. *)
Ltac2 get_summable (ctx : Context) (ty : TypeIdx) : constr :=
  match FMap.find_opt ty (ctx.(types)) with 
  | Some (_t, st) => st
  | None => 
    Control.throw_invalid_argument
      (String.app "type not found in get_summable: " ty)
  end.

(* Get the type and [Summable] instance associated to a 
  [TypeIdx]. Throws an [Invalid_argument] exception if 
  it is not found. *)
Ltac2 get_summable_type (ctx : Context) (ty : TypeIdx) : constr * constr :=
  match FMap.find_opt ty (ctx.(types)) with 
  | Some (t, st) => (t, st)
  | None => 
    Control.throw_invalid_argument
      (String.app "type not found in get_summable_type: " ty)
  end.

(* Gets the identifier associated to a variable. Throws
  an [Invalid_argument] exception if it is not found. *)
Ltac2 get_var (ctx : Context) (ty : TypeIdx) (var : VarIdx) : ident := 
  match FMap2.find_opt ty var (ctx.(vars)) with 
  | Some name => name
  | None => 
    Control.throw_invalid_argument
      (String.concat "" ["variable not found in get_var: ";
        "("; var; " : "; ty; ")"])
  end.


(* Gets the identifier associated to a typed variable. Throws
  an [Invalid_argument] exception if it is not found. *)
Ltac2 get_tyvar (ctx : Context) ((ty, var) : TypedVar) : ident := 
  match FMap2.find_opt ty var (ctx.(vars)) with 
  | Some name => name
  | None => 
    Control.throw_invalid_argument
      (String.concat "" ["variable not found in get_tyvar: ";
        "("; var; " : "; ty; ")"])
  end.

(* Gets the function ([constr]) associated to an abstract
  tensor. Throws an [Invalid_argument] exception if it is 
  not found. *)
Ltac2 get_abs (ctx : Context) (name : AbsIdx) : constr := 
  match FMap.find_opt name (ctx.(abs)) with 
  | Some f => f
  | None => 
    Control.throw_invalid_argument
      (String.concat "" ["abstract tensor not found in get_abs: ";
        name])
  end.



(* Given a list of types over which to sum, construct 
  the type [T] and instance [ST : SummableTy T] 
  corresponding thereto. *)
Ltac2 rec make_summablety (ctx : Context) (sum_types : TypeIdx list) : 
  constr * constr := 
  match sum_types with 
  | [] => ('R, '(@STnil R))
  | ty_name :: sum_types' => 
    let (t', st') := make_summablety ctx sum_types' in 
    let (ty, sblty) := get_summable_type ctx ty_name in 
    ('($ty -> $t'), '(@STcons R $ty $sblty $t' $st'))
  end.

Import Constr.

(* Low-level helper function to create a function application *)
Ltac2 mkApp (f : constr) (args : constr list) : constr :=
  Unsafe.make (Unsafe.App f (Array.of_list args)).

(* Convert a variable index into a [constr], as a named [Var]. *)
Ltac2 make_var (ctx : Context) (ty : TypeIdx) (var : VarIdx) : constr :=
  let name := get_var ctx ty var in 
  Unsafe.make (Unsafe.Var name).

(* Convert a variable index into a [constr], as a named [Var]. *)
Ltac2 make_tyvar (ctx : Context) (tyvar : TypedVar) : constr :=
  make_var ctx (fst tyvar) (snd tyvar).

(* Converts the data of an abstract tensor expression into 
  a [constr], using [Var] for the variables. *)
Ltac2 make_abstens (ctx : Context) (abs_data : AbsData) : constr :=
  let (name, lower, upper) := abs_data in 
  let args := List.map (make_tyvar ctx) (List.append lower upper) in 
  mkApp (get_abs ctx name) args.

(* Multiply two [constr]s using the semiring *)
Ltac2 make_prod (l : constr) (r : constr) :=
  '(rmul $l $r).

(* The [1] value of the semiring *)
Ltac2 make_one () : constr :=
  '(rI).

(* Construct the [constr] corresponding to a product of
  [constr]s, left associated. If the list is empty, 
  returns the [1] of the semiring. *)
Ltac2 make_product (cs : constr list) : constr :=
  let may_prod := List.fold_left (fun may_c cstr => 
    match may_c with 
    | None => Some cstr
    | Some t => Some (make_prod t cstr)
    end) None cs in 
  match may_prod with 
  | Some t => t
  | None => make_one()
  end.

(* Construct the [constr] corresponding to a product of 
  abstract tensors, left associated. If the list is empty, 
  returns the [1] of the semiring. *)
Ltac2 make_abstracts (ctx : Context) (abs : AbsData list) : constr :=
  make_product (List.map (make_abstens ctx) abs).

(* Wraps a term in a function, abstracting over the given 
  list of variables. Assumes the term has no [Rel] subterms. *)
Ltac2 make_fun (ctx : Context) (vars : TypedVar list) (body : constr) : constr :=
  (* We need the _innermost_ function call to be the _lowest_ relative index, 
    so we need to reverse before we substitute [Rel]s for the [Var]s.  *)
  let var_idents := List.map 
    (fun tyvar => (get_type ctx (fst tyvar), get_tyvar ctx tyvar)) vars in 
  let closed_body := Unsafe.closenl (List.rev_map snd var_idents) 1 body in 
  (* Then, we wrap it in the appropriate [Lambda] calls *)
  List.fold_right (fun (type, var_name) body => 
    Unsafe.make (Unsafe.Lambda (Binder.make (Some var_name) type) body))
    var_idents closed_body.


(* Convert a [TensorList] to a term, using the given [Context], 
  of the form [sum_summable _ _]. *)
Ltac2 make_tensorlist (ctx : Context) (tl : TensorList) : constr :=
  let body := make_abstracts ctx (tl.(abstracts)) in 
  let sum_fun := make_fun ctx (tl.(sums)) body in 
  let (funty, summable) := make_summablety ctx (List.map fst (tl.(sums))) in 
  '(@sum_summable $funty $summable $sum_fun).


(* Convert a [TensorExpr] to a term, using the given [Context], 
  as a nested expression of sums. *)
Ltac2 rec make_tensorexpr (ctx : Context) (t : TensorExpr) : constr :=
  match t with 
  | Abstract name lower upper => make_abstens ctx (name, lower, upper)
  | Product ts => 
    make_product (List.map (make_tensorexpr ctx) ts)
  | Sum (ty, var) t => 
    let tconstr := make_tensorexpr ctx t in 
    let body := make_fun ctx [(ty, var)] tconstr in 
    let (ty, summable) := get_summable_type ctx ty in 
    '(@sum_of $ty $summable $body)
  end.













(* Add a typed variable binding to a [Context] *)
Ltac2 add_tyvar (ty : TypeIdx) (var : VarIdx) (name : ident) 
  (ctx : Context) : Context :=
  {ctx with vars := FMap2.add ty var name (ctx.(vars))}.

(* Add a type binding to a [Context] *)
Ltac2 add_type (ty : TypeIdx) (rty : constr) (summable : constr) 
  (ctx : Context) : Context :=
  {ctx with types := FMap.add ty (rty, summable) (ctx.(types))}.

(* Add a type binding to a [Context] *)
Ltac2 add_abstract (name : AbsIdx) (func : constr)
  (ctx : Context) : Context :=
  {ctx with abs := FMap.add name func (ctx.(abs))}.


(* The set of variable names used for a given type *)
Ltac2 used_vars (ctx : Context) (ty : TypeIdx) : VarIdx FSet.t :=
  FMap.domain (FMap2.fix_fst ty (ctx.(vars))).

(* The set of variable names used for _any_ type *)
Ltac2 all_used_vars (ctx : Context) : VarIdx FSet.t :=
  FSet.of_list string_tag 
    (List.map (fun (_,var,_) => var) (FMap2.bindings (ctx.(vars)))).

(* The set of used type names *)
Ltac2 used_tys (ctx : Context) : TypeIdx FSet.t :=
  FMap.domain (ctx.(types)).

(* The set of used abstract tensor names *)
Ltac2 used_abs (ctx : Context) : AbsIdx FSet.t :=
  FMap.domain (ctx.(abs)).

(* Get the name associated to a type, returning None if it is
  not found. Considers types only up to strict 
  alpha-equivalence, not full conversion. *)
Ltac2 find_type_idx (ctx : Context) (c : constr) : TypeIdx option :=
  List.fold_right (fun (name, (ty, _summable)) may_t => 
    match may_t with 
    | Some t => Some t
    | None => if Constr.equal ty c then Some name else None
    end
    ) (FMap.bindings (ctx.(types))) None.

(* Test whether two constrs unify with each other. May instantiate evars *)
Ltac2 constrs_unify (c : constr) (c' : constr) : bool :=
  Control.plus 
    (fun () => Std.unify c c'; true)
    (fun _  => false).

(* Get the name associated to a type, returning None if it is
  not found. Considers types up to unification, so will be 
  quite expensive. *)
Ltac2 find_type_idx_unif (ctx : Context) (c : constr) : TypeIdx option :=
  List.fold_right (fun (name, (ty, _summable)) may_t => 
    match may_t with 
    | Some t => Some t
    | None => if constrs_unify ty c then Some name else None
    end
    ) (FMap.bindings (ctx.(types))) None.

(* Get the name associated to an identifier, returning None 
  if it is not found. *)
Ltac2 find_tyvar (ctx : Context) (name : ident) : TypedVar option :=
  let may_tyvarname := 
    List.find_opt (fun (_, _, name') => Ident.equal name name')
      (FMap2.bindings (ctx.(vars))) in 
  Option.map (fun (ty, var, _) => (ty, var)) may_tyvarname.

(* A very restrictive parsing function for variables, working 
  for variables already in the context with known types. *)
Ltac2 parse_var_restrictive (ctx : Context) (c : constr) : TypedVar option :=
  match Unsafe.kind c with 
  | Unsafe.Var name => 
      (* Look for the variable and type *)
      find_tyvar ctx name
  | _ => None
  end.

(* A very restrictive parsing function for abstract tensors, 
  working for functions applied directly to a list of [Var]s. 
  If this is the case, and if the function is already in the
  context (along with all variables), returns the parsed data.
  for variables already in the context with known types.
  Makes the first [n] of them lower, and the rest upper. *)
Ltac2 parse_abs_restrictive (ctx : Context) (c : constr) (n : int) 
  : AbsData option :=
  let (hd, args) := match Unsafe.kind c with 
    | Unsafe.App f cl => (f, Array.to_list cl)
    | _ => (c, [])
    end in 
  let may_f := List.find_opt (fun (_, f') => Constr.equal hd f')
    (FMap.bindings (ctx.(abs))) in
  Option.bind may_f (fun (f, _) => 
  let may_argvars : (TypedVar list option) 
    := List.fold_right (fun arg may_varargs =>
    Option.bind may_varargs (fun varargs =>
    Option.map (fun vararg => vararg :: varargs) 
      (parse_var_restrictive ctx arg))) args (Some []) in
  Option.bind may_argvars (fun (argvars : TypedVar list) => 
  Some (f, (List.firstn n argvars), (List.skipn n argvars))
  )).

(* Take the product of two tensor expressions, biasing towards
  left associativity (Specifically, if the left argument is a
  product, append the right argument to that product; otherwise,
  wrap both in a new binary product) *)
Ltac2 tensor_prod (l : TensorExpr) (r : TensorExpr) : TensorExpr :=
  match l with 
  | Product ts => Product (List.append ts [r])
  | _ => Product [l; r]
  end.

Import Ltac2.Notations.

(* Restrictive form of parsing tensor expressions, within a
  given context. Requires all arguments to be literally
  variables and all functions to be pre-identified. Makes 
  all arguments outputs/upper, and none lower. *)
Ltac2 rec parse_tensorexpr_restrictive (ctx : Context) 
  (c : constr) : TensorExpr option :=
  match! c with 
  | rmul ?l ?r => 
    Option.bind (parse_tensorexpr_restrictive ctx l) (fun lexpr => 
    Option.bind (parse_tensorexpr_restrictive ctx r) (fun rexpr => 
    Some (tensor_prod lexpr rexpr)
    ))
  | @sum_of ?_a ?_sA ?body => 
    match Unsafe.kind body with
    | Unsafe.Lambda bdr abs => 
      Option.bind (Binder.name bdr) (fun name => 
      let body := Unsafe.substnl [Unsafe.make (Unsafe.Var name)] 0 abs in 
      Option.bind (parse_tensorexpr_restrictive ctx body) (fun bodyexpr => 
      Option.bind (find_tyvar ctx name) (fun tyvar => 
        Some (Sum tyvar bodyexpr)
      )))
    | _ => None
    end
  | _ => Option.map (fun (name, lower, upper) => 
    Abstract name lower upper) (parse_abs_restrictive ctx c 0)
  end.




(* Parse a variable and add it to the context, also determining
  the [TypeIdx] associated to it. If a type is given, looks for 
  an exact match of types. If no type is given, looks for a type 
  that unifies with the term's infered type. *)
Ltac2 var_of_constr (_ctx : Context) (_c : constr) (_type : constr option) : 
  (Context * TypedVar) option :=
  (* let type' := match type with | Some t => t | None => type c end in *)
  None.

(* TODO: Make this more flexible. How? What semantics? 
  How do we decide inputs vs outputs? *)
(* Parse a constr as an abstract tensor. The constr should be of the 
  form [f ins outs], i.e. an application to two arguments, and each
  of [ins] and [outs] should be tuples (nested pairs, of any 
  associativity). Each element of the tuples should be a variable
  (so, section variable or hypothesis). In this case, the variables 
  of [ins] and [outs] are used as the arguments to the abstract 
  tensor. *)
(* Ltac2 abstensor_of_constr_restrictive (ctx : Context) (c : constr) : 
  Context * AbsData :=
  match  *)

(* Convert a [constr] to a [TensorExpr], building up a [Context] 
  along the way. *)
(* Ltac2 tensorexpr_of_constr_aux (ctx : Context) (c : constr) : 
  (Context * TensorExpr) option :=
  match! c with 
  |  *)




(* Test that a [constr] is a sort (SProp, Prop, Set, Type) *)
Ltac2 is_sort (c : constr) : bool :=
  match Unsafe.kind c with
  | Unsafe.Sort _ => true
  | _ => false
  end.

(* Test that a constr has a sort as its type *)
Ltac2 is_type (c : constr) : bool :=
  is_sort (type c).

(* Check that a given pair of [constr]s are a valid summable type
  description, i.e. that the first is a [Type] and the second is
  a [Summable] instance of the first *)
Ltac2 check_summable_ty (ty : constr) (summable : constr) : bool :=
  match is_type ty with 
  | false => false
  | true =>
    constrs_unify (type summable) ('(Summable $ty))
  end.






(*
Module Testing.

Parameter (A : Type).
Parameter (SA : Summable A).

Parameter (B : Type).
Parameter (SB : Summable B).

(* Convertible non-semantically-equal type *)
Definition C := A.
Definition SC : Summable C := SA.

Existing Instance SA.
Existing Instance SB.
Existing Instance SC.

Parameter (faaa : A -> A -> A -> R).
Parameter (faab : A -> A -> B -> R).
Parameter (faba : A -> B -> A -> R).
Parameter (fabb : A -> B -> B -> R).
Parameter (fbaa : B -> A -> A -> R).
Parameter (fbab : B -> A -> B -> R).
Parameter (fbba : B -> B -> A -> R).
Parameter (fbbb : B -> B -> B -> R).

Import MapNotations.

Ltac2 base_tyctx () : TypeContext := !Map(string_tag)
  {"A" : 'A, 'SA; "B" : 'B, 'SB; "C" : 'C, 'SC}.

Ltac2 base_varctx () : VarContext := !Map2(string_tag,string_tag)
  {"A", "a" : @a; "A", "a'" : @a'; "A", "a''" : @a'';
  "B", "b" : @b; "B", "b'" : @b'; "B", "b''" : @b'';
  "C", "c" : @c; "C", "c'" : @c'; "C", "c''" : @c''
  }.

Ltac2 base_absctx () : AbsContext := !Map(string_tag) {
  "faaa" : 'faaa; "faab" : 'faab;
  "faba" : 'faba; "fabb" : 'fabb;
  "fbaa" : 'fbaa; "fbab" : 'fbab;
  "fbba" : 'fbba; "fbbb" : 'fbbb
}.

Ltac2 base_ctx () : Context := {
  vars := base_varctx(); types := base_tyctx(); abs := base_absctx()
}.






Ltac2 testexpr () := @faaa _[a : A, a' : A]^[a : A] * 
  @faab _[a : A, a' : A]^[b : B] * @fbba _[]^[b' : B, b'' : B, a : A].

Ltac2 Eval make_tensorexpr (base_ctx()) (testexpr()).

Ltac2 Eval parse_tensorexpr_restrictive (base_ctx()) 
  (make_tensorexpr (base_ctx()) (testexpr())).

Ltac2 testexpr' () := ∑ a : A , @faaa _[a : A, a' : A]^[a : A] * 
  @faab _[a : A, a' : A]^[b : B] * @fbba _[]^[b' : B, b'' : B, a : A].

Ltac2 Eval make_tensorexpr (base_ctx()) (testexpr'()).

Ltac2 Eval parse_tensorexpr_restrictive (base_ctx()) 
  (make_tensorexpr (base_ctx()) (testexpr'())).

Ltac2 testexpr'' () := ∑ a : A , ∑ a' : A , @faaa _[a : A, a' : A]^[a : A] * 
  @faab _[a : A, a' : A]^[b : B] * @fbba _[]^[b' : B, b'' : B, a : A].

Ltac2 Eval make_tensorexpr (base_ctx()) (testexpr''()).

Ltac2 Eval parse_tensorexpr_restrictive (base_ctx()) 
  (make_tensorexpr (base_ctx()) (testexpr''())).

Ltac2 Eval 
  let ctx := (base_ctx()) in 
  let vars := ([("A", "a")]) in 
  let body := make_tensorexpr (base_ctx()) (testexpr()) in 
  (* We need the _innermost_ function call to be the _lowest_ relative index, 
    so we need to reverse before we substitute [Rel]s for the [Var]s.  *)
  let var_idents := List.map 
    (fun tyvar => (get_type ctx (fst tyvar), get_tyvar ctx tyvar)) vars in 
  let closed_body := Unsafe.closenl (List.rev_map snd var_idents) 0 body in
  
  (* Then, we wrap it in the appropriate [Lambda] calls *)
  List.fold_right (fun (type, var_name) body => 
    Unsafe.make (Unsafe.Lambda (Binder.make (Some var_name) type) body))
    var_idents closed_body.

Ltac2 testval () := '(fun a b c : nat => Nat.add a b).

Ltac2 Eval match Unsafe.kind (testval()) with 
  | Unsafe.Lambda _ arg => Unsafe.substnl [Unsafe.make (Unsafe.Var @a)] 0 arg
  | _t => Control.throw_invalid_argument ""
  end.









Ltac2 test_sum_AAB () := '(∑ (a a' : A) (b : B), faab a a' b).
Import ListExtra.Permutations.
Ltac2 Eval perm_reordering_swaps_after Int.equal [1;2;3] [3;2;1].

Set Default Proof Mode "Classic".

Goal 0 == ∑ (a a' : A) (b : B), faab a a' b.
Import List.ListNotations.
Open Scope list_scope.
Open Scope nat_scope.
match goal with 
| |- context [sum_summable ?T] => 
pose
  (swap_summable_with_nths_after_STPerm ([(2, 0); (1, 0); (0, 0)]) T) as H
end.
simpl in H.
rewrite <- (sum_STPerm _ _ H).
simpl.

Eval cbn [Nat.add] in (∑ (a a' : A) (b : B), faab a a' b).

  swap_summable_with_nths_after








End Testing.
*)



End SummationQuote.