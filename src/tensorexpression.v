Require Import HyperOCM.hypergraph.
Require Import FSetExtra.


(* Require ComplexSum. *)
Require Import Ltac2.Init.

Ltac2 fresh_int (s : int FSet.t) : int :=
  Int.add 1 (FSet.fold max s 0). 

Ltac2 least_fresh_int (s : int FSet.t) : int :=
  let rec go i :=
    if FSet.mem i s then 
      go (Int.add 1 i)
    else
      i in 
  go 0.

Ltac2 replace_int (a : int) (b : int) : int -> int :=
  fun c => if Int.equal c a then b else c.

Ltac2 int_tag := FSet.Tags.int_tag.

(** An Ltac2 definition of tensor expressions, parsable from and
  realizable as the associated sum expressions using the ComplexSum class. *)

(* An alias to indicate this is an index variable in a tensor expression *)
Ltac2 Type VarIdx := int.

(* An alias to indicate this is a variable indexing a (summable) Coq type *)
Ltac2 Type TypeIdx := int.

(* The typing map associating to each type index a pair [(A, C)] of a Coq 
  type [A : Type] and an instance [C : ComplexSum A]. *)
Ltac2 Type TypeIdx_map := (TypeIdx, constr * constr) FMap.t.

(* The typing map associating to each variable index the type index whose
  associated type is the type of the variable. *)
Ltac2 Type VarIdx_map := (VarIdx, TypeIdx) FMap.t.

(* The type of (co) arities, expressed as lists of type variables *)
Ltac2 Type Arity := TypeIdx list.

(* The type of indexes, i.e. the name of a (co)arity of a tensor expression *)
Ltac2 Type Indices := VarIdx list.

(* An alias to indicate this variable indexes an abstract tensor expression 
  (of an unspecified arity and coarity) *)
Ltac2 Type AbsIdx := int.

(* The map from indices of abstract tensor expressions to their Coq 
  function realizations, as well as their arities / coarities. The 
  function should have type [<arity-type> -> <coarity-type> -> C], 
  where the former types are the types corresponding, respectfully,
  to the arity of their lower indices and the arity of their upper 
  indices. *)
Ltac2 Type AbsIdx_map := (AbsIdx, constr * Arity * Arity) FMap.t.

Ltac2 Type TypedPair := TypeIdx * VarIdx * VarIdx.

Ltac2 Type TypedVar := TypeIdx * VarIdx.

Ltac2 Type AbsData := AbsIdx * TypedVar list * TypedVar list. 

Ltac2 Type TypedVarSet := (TypeIdx, VarIdx) FSet2.t.

(* Ltac2 Type TypedPairSet := (TypeIdx, VarIdx, VarIdx) FSet3.t. *)

Ltac2 equal_pair (f : 'a -> 'b -> bool) (g : 'c -> 'd -> bool) : 
  'a * 'c -> 'b * 'd -> bool :=
  fun (a, c) (b, d) => 
  Bool.and (f a b) (g c d).

Ltac2 equal_triple (eq_1 : 'a -> 'b -> bool) (eq_2 : 'c -> 'd -> bool) 
  (eq_3 : 'e -> 'f -> bool) : 'a * 'c * 'e -> 'b * 'd * 'f -> bool :=
  fun (a, c, e) (b, d, f) => 
  Bool.and (eq_1 a b) (Bool.and (eq_2 c d) (eq_3 e f)).

Ltac2 equal_typedvar (x : TypedVar) (y : TypedVar) : bool :=
  equal_pair Int.equal Int.equal x y.

Ltac2 equal_typedpair (x : TypedPair) (y : TypedPair) : bool :=
  equal_triple Int.equal Int.equal Int.equal x y.

Ltac2 equal_absdata (x : AbsData) (y : AbsData) : bool :=
  let l_eq := List.equal equal_typedvar in 
  equal_triple Int.equal l_eq l_eq x y.

(* The type of formal tensor expressions, as abstract objects. 
  They are semi-typed, in that each time a VarIdx is used, a TypeIdx
  is used too to indicate the type of that VarIdx. In this way, VarIdx
  collisions can only occur within a type, and even more importantly
  variables can be freely relabeled.
  With appropriate maps, they can be realized as Coq expressions. *)
Ltac2 Type rec TensorExpr := [
  AbstractTensor (AbsIdx, TypedVar list, TypedVar list) 
    (* An abstract tensor, along with the indices to which it is applied. 
      Each index is stored along with its type. *)
| ProductTensor (TensorExpr, TensorExpr)
    (* The product of two tensor expressions *)
| Contraction (TypeIdx, VarIdx, VarIdx, TensorExpr) 
    (* The contraction of a tensor expression, with 
      [Contraction t a b φ] meaning [Kₐᵇ φ] 
      with [a], [b] of type (indexed by) [t] *)
| Delta (TypeIdx, VarIdx, VarIdx) 
    (* A delta element, with [Delta a b] meaning [δₐᵇ] 
      with [a], [b] of type (indexed by) [t] *)
| One 
    (* The tensor 1 *)
].

(* A simplified form of a tensor expresion which extracts the contractions
  (which must be outermost), the deltas, and abstract tensors *)
Ltac2 Type TensorList := {
  contractions : TypedPair list;
  deltas : TypedPair list;
  abstracts : AbsData list
}.

Module Printing.
Export hypergraph.Printing.

Ltac2 rec print_tensorexpr (t : TensorExpr) : message :=
  (* TODO: Make better with spacing, and pretty-printing with a context *)
  match t with 
  | AbstractTensor abs_idx lower upper => 
    let pr_typair := (fun (_ty, var) => Message.to_string (fprintf "%i" var)) in
    fprintf "φ[%i]_[%s]^[%s]" abs_idx
      (print_cs_list lower pr_typair) (print_cs_list upper pr_typair)
  | ProductTensor l r => 
    fprintf "(%s) ⋅ (%s)"
    (Message.to_string (print_tensorexpr l))
    (Message.to_string (print_tensorexpr r))
  | Contraction _ty a b t => 
    Message.concat (fprintf "K_[%i]^[%i] " a b)
      (print_tensorexpr t)
  | Delta _ty a b => 
    fprintf "δ_[%i]^[%i]" a b 
  | One => fprintf "1"
  end.

Ltac2 rec print_tensorlist (t : TensorList) : message :=
  vbox 2 (List.fold_right (fun (_ty, a, b) m => 
    concats [fprintf "K_[%i]^[%i]" a b; break 1 0; m]) (t.(contractions)) (
  List.fold_right (fun (_ty, a, b) m => 
    concats [fprintf "δ_[%i]^[%i] ⋅ " a b; break 0 0; m]) (t.(deltas)) (
  (print_sep_list' (concat (of_string " ⋅") (break 1 0)) (t.(abstracts))
    (fun (abs_idx, lower, upper) => 
      let pr_typair := (fun (_ty, var) => Message.to_string (fprintf "%i" var)) in
      fprintf "φ[%i]_[%s]^[%s]" abs_idx
        (print_cs_list lower pr_typair) (print_cs_list upper pr_typair)
    ))
  ))).

End Printing.

(* The context for a tensor expression, comprising the various maps *)
Ltac2 Type TensorContext := {
  var_map : VarIdx_map;
  type_map : TypeIdx_map;
  abs_map : AbsIdx_map
}.

(* The lower indices present in the tensor expression, ignoring 
  shadowing by binders (i.e. contractions). Note that indices 
  appearing in binders but no other terms _do_ appear. *)
Ltac2 lower_index_set_full (t : TensorExpr) : TypedVarSet :=
  let rec go t :=
    match t with 
    | AbstractTensor _ lower _upper => 
      FSet2.of_list int_tag int_tag lower
    | ProductTensor l r => 
      FSet2.union (go l) (go r)
    | Contraction ty a _b t => 
      FSet2.add ty a (go t)
    | Delta ty a _b => 
      FSet2.of_list int_tag int_tag [(ty, a)]
    | One => 
      FSet2.empty int_tag int_tag
    end in 
  go t.

(* The upper indices present in the tensor expression, ignoring 
  shadowing by binders (i.e. contractions). Note that indices 
  appearing in binders but no other terms _do_ appear. *)
Ltac2 upper_index_set_full (t : TensorExpr) : TypedVarSet :=
  let rec go t :=
    match t with 
    | AbstractTensor _ _lower upper => 
      FSet2.of_list int_tag int_tag upper
    | ProductTensor l r => 
      FSet2.union (go l) (go r)
    | Contraction ty _a b t => 
      FSet2.add ty b (go t)
    | Delta ty _a b => 
      FSet2.of_list int_tag int_tag [(ty, b)]
    | One => 
      FSet2.empty int_tag int_tag
    end in 
  go t.

(* The set of free lower indices in the tensor expression, i.e.
  excluding those shadowed by binders (i.e. contractions). *)
Ltac2 lower_index_set (t : TensorExpr) : TypedVarSet :=
  let rec go t :=
    match t with 
    | AbstractTensor _ lower _upper => 
      FSet2.of_list int_tag int_tag lower
    | ProductTensor l r => 
      FSet2.union (go l) (go r)
    | Contraction ty a _b t => 
      FSet2.remove ty a (go t)
    | Delta ty a _b => 
      FSet2.of_list int_tag int_tag [(ty, a)]
    | One => 
      FSet2.empty int_tag int_tag
    end in 
  go t.

(* The set of free upper indices in the tensor expression, i.e.
  excluding those shadowed by binders (i.e. contractions). *)
Ltac2 upper_index_set (t : TensorExpr) : TypedVarSet :=
  let rec go t :=
    match t with 
    | AbstractTensor _ _lower upper => 
      FSet2.of_list int_tag int_tag upper
    | ProductTensor l r => 
      FSet2.union (go l) (go r)
    | Contraction ty _a b t => 
      FSet2.remove ty b (go t)
    | Delta ty _a b => 
      FSet2.of_list int_tag int_tag [(ty, b)]
    | One => 
      FSet2.empty int_tag int_tag
    end in 
  go t.


(* The set of bound lower indices in the tensor expression, i.e.
  those introduced by binders (i.e. contractions). *)
Ltac2 bound_lower_index_set (t : TensorExpr) : TypedVarSet :=
  let rec go t :=
    match t with 
    | AbstractTensor _ _ _ => 
      FSet2.empty int_tag int_tag
    | ProductTensor l r => 
      FSet2.union (go l) (go r)
    | Contraction ty a _b t => 
      FSet2.add ty a (go t)
    | Delta _ _ _ => 
      FSet2.empty int_tag int_tag
    | One => 
      FSet2.empty int_tag int_tag
    end in 
  go t.

(* The set of bound upper indices in the tensor expression, i.e.
  those introduced by binders (i.e. contractions). *)
Ltac2 bound_upper_index_set (t : TensorExpr) : TypedVarSet :=
  let rec go t :=
    match t with 
    | AbstractTensor _ _ _ => 
      FSet2.empty int_tag int_tag
    | ProductTensor l r => 
      FSet2.union (go l) (go r)
    | Contraction ty _a b t => 
      FSet2.add ty b (go t)
    | Delta _ _ _ => 
      FSet2.empty int_tag int_tag
    | One => 
      FSet2.empty int_tag int_tag
    end in 
  go t.

(* The list of free lower indices in the tensor expression, i.e.
  excluding those shadowed by binders (i.e. contractions). *)
Ltac2 lower_indices (t : TensorExpr) : TypedVar list :=
  let rec go t :=
    match t with 
    | AbstractTensor _ lower _upper => 
      lower
    | ProductTensor l r => 
      List.append (go l) (go r)
    | Contraction ty a _b t => 
      List.remove equal_typedvar (ty, a) (go t)
    | Delta ty a _b => 
      [(ty, a)]
    | One => 
      []
    end in 
  go t.

(* The list of free upper indices in the tensor expression, i.e.
  excluding those shadowed by binders (i.e. contractions). *)
Ltac2 upper_indices (t : TensorExpr) : TypedVar list :=
  let rec go t :=
    match t with 
    | AbstractTensor _ _lower upper => 
      upper
    | ProductTensor l r => 
      List.append (go l) (go r)
    | Contraction ty _a b t => 
      List.remove equal_typedvar (ty, b) (go t)
    | Delta ty _a b => 
      [(ty, b)]
    | One => 
      []
    end in 
  go t.

(*
(* All indices of a tensor expression, both upper and lower, even if 
  shadowed by contraction *)
Ltac2 rec index_set (t : TensorExpr) : VarIdx FSet.t :=
  match t with 
  | AbstractTensor _ lower upper => 
    FSet.of_list int_tag (List.map snd (List.append lower upper))
  | ProductTensor l r => 
    FSet.union (index_set l) (index_set r)
  | Contraction _ a b t => 
    FSet.add a (FSet.add b (index_set t))
  | Delta _ a b => 
    FSet.of_list int_tag [a; b]
  | One => 
    FSet.empty int_tag
  end.

(* The lower indices of a tensor expression, excluding those 
  shadowed by contraction *)
Ltac2 rec lower_indices (t : TensorExpr) : VarIdx list :=
  match t with 
  | AbstractTensor _ lower _ => List.map snd lower
  | ProductTensor l r => 
      List.append (lower_indices l) (lower_indices r) 
  | Contraction _ a _ t => 
      List.remove Int.equal a (lower_indices t)
  | Delta _ a _ => [a]
  | One => []
  end.

(* The lower indices of a tensor expression, excluding those 
  shadowed by contraction *)
Ltac2 rec upper_indices (t : TensorExpr) : VarIdx list :=
  match t with 
  | AbstractTensor _ _ upper => List.map snd upper
  | ProductTensor l r => 
      List.append (upper_indices l) (upper_indices r) 
  | Contraction _ _ b t => 
      List.remove Int.equal b (upper_indices t)
  | Delta _ _ b => [b]
  | One => []
  end.

Ltac2 rec free_indices (t : TensorExpr) : VarIdx FSet.t := 
  match t with 
  | AbstractTensor _ lower upper => 
    FSet.of_list int_tag (List.map snd (List.append lower upper))
  | ProductTensor l r => 
    FSet.union (index_set l) (index_set r)
  | Contraction _ a b t => 
    FSet.remove a (FSet.remove b (index_set t))
  | Delta _ a b => 
    FSet.of_list int_tag [a; b]
  | One => 
    FSet.empty int_tag
  end.
*)

Ltac2 rec abstract_index_set (t : TensorExpr) : AbsIdx FSet.t := 
  match t with 
  | AbstractTensor idx _lower _upper => 
    FSet.add idx (FSet.empty int_tag)
  | ProductTensor l r => 
    FSet.union (abstract_index_set l) (abstract_index_set r)
  | Contraction _ _a _b t => 
    (abstract_index_set t)
  | Delta _ _a _b => FSet.empty int_tag
  | One => FSet.empty int_tag
  end.

(* Relabel a tensor expression, including binders (i.e. contractions) *)
Ltac2 relabel_full 
  (lower_map : TypeIdx -> VarIdx -> VarIdx)
  (upper_map : TypeIdx -> VarIdx -> VarIdx) 
  (t : TensorExpr) : TensorExpr := 
  let rec go t := 
    match t with 
    | AbstractTensor idx lower upper => 
      let lf (ty, a) := (ty, lower_map ty a) in 
      let uf (ty, a) := (ty, upper_map ty a) in 
      AbstractTensor idx (List.map lf lower) (List.map uf upper)
    | ProductTensor l r => 
      ProductTensor (go l) (go r)
    | Contraction ty a b t => 
      Contraction ty (lower_map ty a) (upper_map ty b) (go t)
    | Delta ty a b => 
      Delta ty (lower_map ty a) (upper_map ty b)
    | One => One
    end in 
  go t.

(* Relabel a tensor expression, respecting binders (i.e. contractions), 
  so that only unbound indices are replaced *)
Ltac2 relabel_unbound 
  (lower_map : TypeIdx -> VarIdx -> VarIdx)
  (upper_map : TypeIdx -> VarIdx -> VarIdx) 
  (t : TensorExpr) : TensorExpr := 
  let rec go lower_map upper_map t := 
    match t with 
    | AbstractTensor idx lower upper => 
      let lf (ty, a) := (ty, lower_map ty a) in 
      let uf (ty, a) := (ty, upper_map ty a) in 
      AbstractTensor idx (List.map lf lower) (List.map uf upper)
    | ProductTensor l r => 
      ProductTensor (go lower_map upper_map l) (go lower_map upper_map r)
    | Contraction ty a b t => 
      Contraction ty a b 
      (go 
        (fun ty' a' => if equal_typedvar (ty', a') (ty, a) then a 
          else lower_map ty' a')
        (fun ty' b' => if equal_typedvar (ty', b') (ty, b) then b 
          else upper_map ty' b')
          t)
    | Delta ty a b => 
      Delta ty (lower_map ty a) (upper_map ty b)
    | One => One
    end in 
  go lower_map upper_map t.


Ltac2 relabel_bound_aux
  (lower_map : TypeIdx -> VarIdx -> VarIdx)
  (upper_map : TypeIdx -> VarIdx -> VarIdx) 
  (lower_bound : TypedVarSet) (upper_bound : TypedVarSet)
  (t : TensorExpr) : TensorExpr := 
  let casef f s (ty, a) := 
      (ty, if FSet2.mem ty a s then f ty a else a) in 
  let casef' f s ty a := 
      if FSet2.mem ty a s then f ty a else a in 
  let rec go lower_bound upper_bound t := 
    match t with 
    | AbstractTensor idx lower upper => 
      let lf := casef lower_map lower_bound in 
      let uf := casef upper_map upper_bound in 
      AbstractTensor idx (List.map lf lower) (List.map uf upper)
    | ProductTensor l r => 
      ProductTensor (go lower_bound upper_bound l) 
        (go lower_bound upper_bound r)
    | Contraction ty a b t => 
      let lf := casef' lower_map lower_bound in 
      let uf := casef' upper_map upper_bound in 
      Contraction ty (lf ty a) (uf ty b)
      (go (FSet2.add ty a lower_bound)
        (FSet2.add ty b upper_bound) t)
    | Delta ty a b => 
      let lf := casef' lower_map lower_bound in 
      let uf := casef' upper_map upper_bound in 
      Delta ty (lf ty a) (uf ty b)
    | One => One
    end in 
  go lower_bound upper_bound t.

(* Relabel only the bound variables of a tensor expression. Preserves 
  alpha-equivalence. *)
Ltac2 relabel_bound
  (lower_map : TypeIdx -> VarIdx -> VarIdx)
  (upper_map : TypeIdx -> VarIdx -> VarIdx) 
  (t : TensorExpr) : TensorExpr := 
  relabel_bound_aux lower_map upper_map 
    (FSet2.empty int_tag int_tag) (FSet2.empty int_tag int_tag) t.

(* FIXME: Move *)
Ltac2 replace_typedvar : TypedVar -> TypedVar -> TypedVar -> TypedVar :=
  fun a b c => 
  if equal_typedvar c a then b else c.


Ltac2 replace_typedvar' : TypedVar -> VarIdx -> TypeIdx -> VarIdx -> VarIdx :=
  fun a b ty c => 
  if equal_typedvar (ty, c) a then b else c.

(* Check whether two terms are alpha-convertible, i.e. equal up to 
  renaming variables bound in contractions. *)
Ltac2 rec alpha_convertible (t : TensorExpr) (s : TensorExpr) : bool :=
  match (t, s) with 
  | (AbstractTensor ai low up, AbstractTensor ai' low' up') => 
      equal_absdata (ai, low, up) (ai', low', up')
  | (ProductTensor l r, ProductTensor l' r') => 
    Bool.and (alpha_convertible l l') 
      (alpha_convertible r r')
  | (Delta ty a b, Delta ty' a' b') => 
      equal_typedpair (ty, a, b) (ty', a', b')
  | (One, One) => 
      true
  | (Contraction ty a b t, Contraction ty' a' b' t') =>
      if Bool.neg (Int.equal ty ty') 
        then false (* Contractions on different types; not equal *) 
      else
        (* Relabel the binder in the second term to match the first *)
        let low_fun := replace_typedvar' (ty, a') a in 
        let upp_fun := replace_typedvar' (ty, b') b in 
        let low_bnd := FSet2.add ty a' (FSet2.empty int_tag int_tag) in 
        let upp_bnd := FSet2.add ty b' (FSet2.empty int_tag int_tag) in 
        let t'_renamed := 
          relabel_bound_aux low_fun upp_fun low_bnd upp_bnd t' in 
        alpha_convertible t t'_renamed
  | _ => false
  end.


(* 

Ltac2 rec relabel (f : int -> int) (t : TensorExpr) : TensorExpr := 
  match t with 
  | AbstractTensor idx lower upper => 
    let f' (ty, a) := (ty, f a) in 
    AbstractTensor idx (List.map f' lower) (List.map f' upper)
  | ProductTensor l r => 
    ProductTensor (relabel f l) (relabel f r)
  | Contraction ty a b t => 
    Contraction ty (f a) (f b) (relabel f t)
  | Delta t a b => 
    Delta t (f a) (f b)
  | One => One
  end.

Ltac2 rec relabel_bound (f : int -> int) (t : TensorExpr) : TensorExpr := 
  let rec relabel_bound_aux f t (bound : VarIdx FSet.t) :=
    match t with 
    | AbstractTensor idx lower upper => 
      let f' (ty, v) := (ty, if FSet.mem v bound then f v else v) in 
      AbstractTensor idx (List.map f' lower) (List.map f' upper)
    | ProductTensor l r => 
      ProductTensor (relabel_bound_aux f l bound) (relabel_bound_aux f r bound)
    | Contraction ty a b t => 
      Contraction ty (f a) (f b) (relabel_bound_aux f t (FSet.add a (FSet.add b bound)))
    | Delta t a b => 
      let f' v := if FSet.mem v bound then f v else v in 
      Delta t (f' a) (f' b)
    | One => One
    end in 
  relabel_bound_aux f t (FSet.empty int_tag). *)

(* Ltac2 deltas (idxs : TypedPair list) : TensorExpr :=
  List.fold_right (fun (ty, a, b) t => (ProductTensor (Delta ty a b) t)) idxs One. *)



(* Relabel the bound index (ty, a) in [t] to be free in the set 
  [avoid] of (typed) indices. Returns a tensor expression 
  alpha-equivalent to its input *)
Ltac2 make_lower_bound_idx_free (ty : TypeIdx) (a : VarIdx) 
  (avoid : TypedVarSet) (t : TensorExpr) : TensorExpr :=
  if Bool.neg (FSet2.mem ty a avoid) (* If we can just leave it be, we do! *)
    then t else 
    (* Compute the least allowable index, within this type *)
  let new_a := least_fresh_int 
    (FSet2.fix_fst ty (FSet2.union avoid (lower_index_set_full t))) in 
  let low_fun := replace_typedvar' (ty, a) new_a in 
  let upp_fun _ b := b in 
  (* only relabel if the variable is actually bound!*)
  relabel_bound low_fun upp_fun t.

(* Relabel the bound index (ty, a) in [t] to be free in the set 
  [avoid] of (typed) indices. Returns a tensor expression 
  alpha-equivalent to its input *)
Ltac2 make_upper_bound_idx_free (ty : TypeIdx) (b : VarIdx) 
  (avoid : TypedVarSet) (t : TensorExpr) : TensorExpr :=
  if Bool.neg (FSet2.mem ty b avoid) (* If we can just leave it be, we do! *)
    then t else 
    (* Compute the least allowable index, within this type *)
  let new_b := least_fresh_int 
    (FSet2.fix_fst ty (FSet2.union avoid (upper_index_set_full t))) in 
  let low_fun _ a := a in 
  let upp_fun := replace_typedvar' (ty, b) new_b in 
  (* only relabel if the variable is actually bound!*)
  relabel_bound low_fun upp_fun t.

(* Relabel the bound indices (ty, a, b) in [t] to be free in the sets 
  [avoid_low] and [avoid_upp] of (typed) indices. Returns a tensor 
  expression alpha-equivalent to its input *)
Ltac2 make_bound_pair_free (ty : TypeIdx) (a : VarIdx) (b : VarIdx) 
  (avoid_low : TypedVarSet) (avoid_upp : TypedVarSet) 
  (t : TensorExpr) : TensorExpr :=
  if Bool.neg (Bool.or (FSet2.mem ty a avoid_low) (FSet2.mem ty b avoid_upp)) 
    then t else (* If we can just leave it be, we do! *)
    (* Compute the least allowable indices, within this type *)
  let new_a := least_fresh_int 
    (FSet2.fix_fst ty (FSet2.union avoid_low (lower_index_set_full t))) in 
  let new_b := least_fresh_int 
    (FSet2.fix_fst ty (FSet2.union avoid_upp (upper_index_set_full t))) in 
  let low_fun := replace_typedvar' (ty, a) new_a in 
  let upp_fun := replace_typedvar' (ty, b) new_b in 
  relabel_bound low_fun upp_fun t.


(* Given terms [Kₐᵇ φ] and [ψ], relabels [a] / [b] / [φ] and returns the 
  typed pair [(ty, s, t)] and new value [φ'] so that 
  [(Kₐᵇ φ) ⋅ ψ =[α]= Kₛᵗ (φ' ⋅ ψ)], all while avoiding the 
  given lower / upper indices *)
Ltac2 pull_contraction_from_left (ty : TypeIdx) (a : VarIdx) (b : VarIdx) 
  (avoid_low : TypedVarSet) (avoid_upp : TypedVarSet)
  (φ : TensorExpr) (ψ : TensorExpr) : TypedPair * TensorExpr :=
  let avoid_low := FSet2.union avoid_low (lower_index_set ψ) in 
  let avoid_upp := FSet2.union avoid_upp (upper_index_set ψ) in 
  (* TODO: Avoid this kinda nasty hack. It works, but it's a bit horrible *)
  let (a', b', φ') := match 
    make_bound_pair_free ty a b avoid_low avoid_upp (Contraction ty a b φ) with 
    | Contraction _ty a' b' φ' => (a', b', φ')
    | _ => Control.throw (Tactic_failure (Some (Message.of_string "Non-contraction value in the match of pull_contraction_from_left (in tensorexpression.v); this should never occur!")))
    end in 
  ((ty, a', b'), φ').

(* Move all contractions to the outside of a tensor expression, 
  using axiom T4 and relabeling 
  TODO: Make less janky / more efficient? In particular, move to 
  [TypedPair list * TensorExpr] at some point (I've moved away because 
  it's easier to reason that this logic is correct)*)
Ltac2 pull_out_contractions (t : TensorExpr) : TensorExpr := 
  let rec merge avoid_low avoid_upp l r := 
    (* Give a term with all the contractions of [l] and [r] moved to 
      the outside, performing any necessary renamings *)
    match l, r with 
    | Contraction ty a b l, r => 
      let ((_, a', b'), l') := 
        pull_contraction_from_left ty a b avoid_low avoid_upp l r in 
      (* Could correctly here say (Contraction ty a' b' l' ⋅ r); 
        but we now know we can pull out the contraction so we instead do... *)
      let avoid_low' := FSet2.add ty a' avoid_low in 
      let avoid_upp' := FSet2.add ty b' avoid_upp in 
      let t' := merge avoid_low' avoid_upp' l' r in 
      Contraction ty a' b' t'
    | l, Contraction ty a b r => 
      let ((_, a', b'), r') := 
        pull_contraction_from_left ty a b avoid_low avoid_upp r l in 
      (* Could correctly here say (l ⋅ Contraction ty a' b' r'); 
        but we now know we can pull out the contraction so we instead do... *)
      let avoid_low' := FSet2.add ty a' avoid_low in 
      let avoid_upp' := FSet2.add ty b' avoid_upp in 
      let t' := merge avoid_low' avoid_upp' l r' in 
      Contraction ty a' b' t'
    | l, r => 
      (* No more contractions! *)
      ProductTensor l r
    end in 
  let rec go avoid_low avoid_upp t := 
    match t with 
    | AbstractTensor _ _ _ => t
    | Delta _ _ _ => t
    | One => t
    | Contraction ty a b t => 
      let avoid_low' := FSet2.add ty a avoid_low in 
      let avoid_upp' := FSet2.add ty b avoid_upp in 
      let t' := go avoid_low' avoid_upp' t in 
      Contraction ty a b t'
    | ProductTensor l r => 
        let l' := go avoid_low avoid_upp l in 
        let r' := go avoid_low avoid_upp r in 
        merge avoid_low avoid_upp l' r'
    end in 
  go (FSet2.empty int_tag int_tag) (FSet2.empty int_tag int_tag) t.

(* Parse out any contractions on the outside of [t], returning 
  their data and the remaining internal TensorExpr *)
Ltac2 parse_contractions (t : TensorExpr) : TypedPair list * TensorExpr :=
  let rec go t :=
    match t with 
    | Contraction ty a b t => 
      let (l, t') := go t in 
      (List.cons (ty, a, b) l, t')
    | _ => ([], t)
    end in 
  go t.



(* 

(* Relabel a tensor expression so as to avoid a set [vars] of variable indices *)
Ltac2 make_free (vars : VarIdx FSet.t) (t : TensorExpr) : TensorExpr :=
  let all_vars := FSet.union vars (index_set t) in 
  let lower_bound := Int.add 1 (FSet.fold max all_vars 0) in 
  relabel (fun v => if FSet.mem v vars then Int.add v lower_bound else v) t. *)


(* (* Rename bound variables (respecting shadowing) to make a 
  given set of variables free therein*)
Ltac2 rec make_free_in_bound (s : VarIdx FSet.t) (t : TensorExpr)  *)
(* 
(* Given a list of contractions for a term and a second term, 
  makes the contracted variables free from the variables in 
  the second term, avoiding also the set [avoid] of variables. *)
Ltac2 make_contractions_free
  (cs : TypedPair list) (t : TensorExpr)
  (avoid : VarIdx FSet.t) (other : TensorExpr) :=
  let all_vars := List.fold_right (fun (_, a, b) vars => FSet.add a (FSet.add b vars))
    cs (FSet.union avoid (FSet.union (index_set t) (index_set other))) in 
  let bad_vars := FSet.union avoid (index_set other) in 
  let lower_bound := Int.add 1 (FSet.fold max all_vars 0) in (* TODO: Make more performant by taking maxes individually *)
  let relabel_fun := (fun v => if FSet.mem v bad_vars then Int.add v lower_bound else v) in 
  let t_new := relabel relabel_fun t in 
  let cs_new := List.map (fun (ty, a, b) => (ty, relabel_fun a, relabel_fun b)) cs in 
  (cs_new, t_new). *)







(* (* Rename the variables [bound] within [t] by [f] according to 
  binding rules, i.e. if a variable in [bound] appears in a 
  binder within [t], the internal binding will not be renamed 
  (these variables refer to different bindings). *)
Ltac2 rec alpha_rename (f : int -> int) (bound : VarIdx FSet.t) 
  (t : TensorExpr) : TensorExpr :=
  let rec go bound t := 
    match t with 
    | AbstractTensor abs_idx lower upper =>
      let f' (ty, v) := (ty, if FSet.mem v bound then f v else v) in 
      AbstractTensor abs_idx (List.map f' lower) (List.map f' upper) 
    | ProductTensor l r =>
      ProductTensor (go bound l) (go bound r)
    | Delta ty a b => 
      let f' v := if FSet.mem v bound then f v else v in 
      Delta ty (f' a) (f' b)
    | One => One
    | Contraction ty a b t => 
      Contraction ty a b (go (FSet.remove a (FSet.remove b bound)) t)
    end in 
  go bound t.

(* Check whether two terms are alpha-convertible, i.e. equal up to 
  renaming variables bound in contractions. *)
Ltac2 rec alpha_convertible (t : TensorExpr) (s : TensorExpr) : bool :=
  match (t, s) with 
  | (AbstractTensor ai low up, AbstractTensor ai' low' up') => 
      equal_absdata (ai, low, up) (ai', low', up')
  | (ProductTensor l r, ProductTensor l' r') => 
    Bool.and (alpha_convertible l l') 
      (alpha_convertible r r')
  | (Delta ty a b, Delta ty' a' b') => 
      equal_typedpair (ty, a, b) (ty', a', b')
  | (One, One) => 
      true
  | (Contraction ty a b t, Contraction ty' a' b' t') =>
      let rename_fn := Function.compose (replace_int a' a) (replace_int b' b) in  
      let t'_renamed := 
        alpha_rename rename_fn (FSet.of_list int_tag [a; b]) t' in 
      Bool.and 
        (Int.equal ty ty')
        (alpha_convertible t t'_renamed)
  | _ => false
  end. *)
(* 

(* Pull contractions to the outside of a TensorExpr, one contraction at a time. *)
Ltac2 rec extract_contractions_alt (t : TensorExpr) : 
  match t with 
  | AbstractTensor _ _ _ => t
  | Delta _ _ _ => t
  | One => t
  | Contraction ty a b t => 
    Contraction ty a b (extract_contractions_alt t)
  | ProductTensor (Contraction ty a b l) r =>  *)


(* 


Ltac2 rec extract_contractions_aux (t : TensorExpr) (avoid : VarIdx FSet.t) : 
  TypedPair list * TensorExpr :=
  match t with 
  | AbstractTensor _idx _lower _upper => ([], t)
  | ProductTensor l r => 
    let (lidxs, l') := extract_contractions_aux l avoid in 
    let (lidxs, l') := make_contractions_free lidxs l' avoid r in 
      (* ^ Now, the contractions of l reference no variables free in r *)
    let lvars := List.fold_right FSet.add 
      (List.flat_map (fun (_, a, b) => [a; b]) lidxs) 
      (index_set l') in 
    let (ridxs, r') := extract_contractions_aux r avoid in 
    let (ridxs, r') := make_contractions_free ridxs r' (FSet.union avoid lvars) One in 
    (* ^ Now, the contractions of r reference no variables, free or bound, of l *)
    (* In particular, the contraction variable sets are disjoint, so we can do the following : *)
    (List.append lidxs ridxs, ProductTensor l' r')
  | Contraction ty a b t => 
    let (tidxs, t') := extract_contractions_aux t (FSet.add a (FSet.add b avoid)) in (* TODO: I think we don't actually need to do this and the next thing too?? *) 
    let (tidxs, t') := make_contractions_free tidxs t' 
      (FSet.add a (FSet.add b avoid)) One in 
    (List.cons (ty, a, b) tidxs, t')
  | Delta _ty _a _b => ([], t)
  | One => ([], t)
  end.


(* Pull all contractions to the outside of the tensor, relabeling
  as necessary. Returns the list of pairs of indices by which the
  diagram is contracted. So, maintains the invariant that (up to 
  tensor laws) 
  [ let (idxs, t') := extract_contractions t in 
    t ≡ List.fold_right (fun (ty, a, b) t'' => Contraction ty a b t'') idxs t' ].
  *)
Ltac2 extract_contractions (t : TensorExpr) : 
  TypedPair list * TensorExpr :=
  extract_contractions_aux t (FSet.empty int_tag). *)

(* Given a contraction-free tensor expression [t], decompose
  it into a list of [Delta]s and [AbstractTensor]s, dropping 
  any [One]s. Represents [Delta]s by their labels and keeps 
  [AbstractTensor]s as [TensorExpr]s.
  Note that if [t] has a Contraction, the second component
  will not comprise only [AbstractTensor]s. *)
Ltac2 rec decompose_contraction_free_expr (t : TensorExpr) : 
  TypedPair list * TensorExpr list :=
  match t with 
  | Contraction _ _ _ _ => ([], [t])
  | One => ([], [])
  | Delta ty a b => ([(ty, a, b)], [])
  | AbstractTensor _ _ _ => ([], [t])
  | ProductTensor l r => 
    let (ldel, labs) := decompose_contraction_free_expr l in 
    let (rdel, rabs) := decompose_contraction_free_expr r in 
    (List.append ldel rdel, List.append labs rabs)
  end.

Import ListForEach.

(* Cancel corresponding deltas and contractions (according to axiom T4).
  Returns lists of contractions and deltas, along with the necessary
  renamings. *)
Ltac2 cancel_deltas (cs : TypedPair list) (ds : TypedPair list) : 
  (TypedPair list) * (TypedPair list) * (TypedPair list) :=
  let (res, _) := (* We can discard the 'return value'; we only care about the state *)
  fold_each ds (cs, [], []) 
    (* Incrementally reduce the remaining [cs] (contractions) and build 
    up the list (starting with [[]]) of uncancellable [ds] and list (also
    starting with [[]]) of replacements *)
  (fun (cs, uncancelled_ds, renames) (ty, a, c) => 
    (* First, try to cancel on the lower component ([a]) *)
    let i := for_each (List.enumerate cs) 
      (fun (i, (ty', a', _b)) => 
        if Bool.and (Int.equal ty ty') (Int.equal a a') then 
        for_return (Some i) else continue) (fun _ => None) in 
    match i with | Some i => (* Found a match at index i! *)
      let (_, _, b) := List.nth cs i in 
      let cs' := List.append (List.firstn i cs) (List.skipn (Int.add 1 i) cs) in 
      let renames' := List.append renames [(ty, b, c)] in 
      fold_continue (cs', uncancelled_ds, renames')
    | None => (* No match on lower component*)
    (* Second, try to cancel on the upper component ([c]) *)
    let i := for_each (List.enumerate cs) 
      (fun (i, (ty', _b, c')) => 
        if Bool.and (Int.equal ty ty') (Int.equal c c') then 
        for_return (Some i) else continue) (fun _ => None) in 
    match i with | Some i => (* Found a match at index i! *)
      let (_, b, _) := List.nth cs i in 
      let cs' := List.append (List.firstn i cs) (List.skipn (Int.add 1 i) cs) in 
      let renames' := List.append renames [(ty, b, a)] in 
      fold_continue (cs', uncancelled_ds, renames')
    | None => (* No match on upper component either, so this is unmatched *)
    fold_continue (cs, List.append uncancelled_ds [(ty, a, c)], renames)
    end
    end
  ) (* We never return, so the [or_else] always triggers, and is just the identity *)
  (fun (cs, ds, renames) => (cs, ds, renames))
  in res.



(** Section on tensorlists *)

Ltac2 mk_tensorlist :=
  fun cs ds abs => {
    contractions := cs;
    deltas := ds;
    abstracts := abs
  }.

(* Converts a [TensorList] to a [TensorExpr] in the natural way *)
Ltac2 tensor_expr_of_tensor_list (t : TensorList) : TensorExpr :=
  let core := List.fold_right (fun (idx, lower, upper) t => 
    ProductTensor (AbstractTensor idx lower upper) t) (t.(abstracts)) One in 
  let deltad := List.fold_right (fun (ty, a, b) t => 
    ProductTensor (Delta ty a b) t) (t.(deltas)) core in 
  let contracted := List.fold_right (fun (ty, a, b) t => 
    Contraction ty a b t) (t.(contractions)) deltad in 
  contracted.

(* Extracts from a [TensorExpr] the data of an [AbstractTensor].
  Returns [None] if the input is not an [AbstractTensor]. *)
Ltac2 parse_abstract (t : TensorExpr) : 
  AbsData option :=
  match t with 
  | AbstractTensor idx lower upper => Some (idx, lower, upper)
  | _ => 
    Message.print (Message.of_string "WARNING: Attempt to parse a non-abstract TensorExpr"); 
    None
  end.

Ltac2 tensor_expression_to_simplified (t : TensorExpr) : TensorList :=
  let t' := pull_out_contractions t in 
  let (cs, inner) := parse_contractions t' in 
  let (ds, abs) := decompose_contraction_free_expr inner in 
  let abs := List.map_filter parse_abstract abs in 
  mk_tensorlist cs ds abs.



(* Ltac2 tensor_list_lower (t : TensorList) : TypedVar list :=
   *)

(* Convert a [TensorList] to the corresponding hypergraph. 
  The conversion is, essentially, that contractions become 
  (internal) vertices, abstract tensors become hyperedges,
  deltas become free wires, and any free lower / upper indices
  in the abstract tensors become input / output vertices,
  respectively.

  Vertices are labeled by the [TypeIdx] from the contraction
  or input, while edges are labeled by the [AbsIdx] indexing
  their function. *)
Ltac2 tensor_list_to_hypergraph (t : TensorList) : (TypeIdx, AbsIdx) Graph :=
  (* Start with an empty graph *)
  let g := mk_graph () in 
  (* First, add a vertex for each contraction, recording their indices *)
  let cs_map := List.map (fun (ty, a, b) => 
    let i := add_vertex g (Some ty) (-1) in 
    (i, (ty, a, b))) (t.(contractions)) in 
  (* Then, for each abstract tensor, add a hyperedge, adding vertices for
    each free index, recording them in [in_verts] and [out_verts] as we do
    (they will be marked as appropriately in / out later) *)
  let (in_verts, out_verts, _contr_edges) := (* ([], [], []) *)
    List.fold_right (fun (abs_idx, lower, upper) (ins, outs, contrs) => 
      (* First, get the list of source/lower vertices, adding those we lack *)
      let (new_ins, s) := List.fold_right (fun (ty, a) (ins, s) => (* TODO: Fold left so we can [cons] to [s] rather than appending? *)
        (* Try to find an internal/contraction vertex with the right label, i.e. 
          a contraction with [a] as an _lower_ index (TODO: Check, but I think lower is correct here) *)
        let may_i := List.find_opt (fun (_, (ty', a', _)) =>
          Bool.and (Int.equal ty ty') (Int.equal a a')) cs_map in 
        match may_i with 
        | Some (i, _) => (* Found a matching vertex; add it to the source vertex list *)
          (ins, List.append s [i])
        | None => (* No matching vertex means this is a free index; add it as a vertex marked to be made an input *)
          let i := add_vertex g (Some ty) (-1) in 
          (List.cons i ins, List.append s [i])
        end) lower ([], []) in 
      (* Next, do the same for the target/upper vertices *)
      let (new_outs, t) := List.fold_right (fun (ty, b) (outs, t) => (* TODO: Fold left so we can [cons] to [t] rather than appending? *)
        (* Try to find an internal/contraction vertex with the right label, i.e. 
          a contraction with [b] as an _upper_ index (TODO: Check, but I think upper is correct here) *)
        let may_i := List.find_opt (fun (_, (ty', _, b')) =>
          Bool.and (Int.equal ty ty') (Int.equal b b')) cs_map in 
        match may_i with 
        | Some (i, _) => (* Found a matching vertex; add it to the source vertex list *)
          (outs, List.append t [i])
        | None => (* No matching vertex means this is a free index; add it as a vertex marked to be made an input *)
          let i := add_vertex g (Some ty) (-1) in 
          (List.cons i outs, List.append t [i])
        end) upper ([], []) in
      (* Now, we can add the edge to the graph *) 
      let e := add_edge g s t (Some abs_idx) (-1) in
      (* Finally, record the new input / output vertices we'll need to mark, 
      along with the edge index of this edge *)
      (List.append new_ins ins, List.append new_outs outs, 
        List.cons (e, (abs_idx, lower, upper)) contrs) (* TODO: Remove unused lower / upper values here *)
      ) (t.(abstracts)) ([], [], []) in 
  (* Finally, add a vertex and edge for each delta *)
  let (delta_ins, delta_outs, _delta_es) := List.fold_right 
    (fun (ty, _a, _b) (dins, douts, des) => 
    (* Make input and output vertices *)
    let a_idx := add_vertex g (Some ty) (-1) in 
    let b_idx := add_vertex g (Some ty) (-1) in 
    (* Make an edge for the delta with these as source and target *)
    let e_idx := add_edge g [a_idx] [b_idx] None (-1) in 
    (* Record the new values *)
    (List.append dins [a_idx], List.append douts [b_idx], List.append des [e_idx])
    ) (t.(deltas)) ([], [], []) in 
  (* Now, the graph has all the data we need, and we just need to set 
    the inputs and outputs *)
  set_inputs g (List.append in_verts delta_ins);
  set_outputs g (List.append out_verts delta_outs);
  (* Then our graph is ready! *)
  g.

Import Printf.

(* Construct a [TensorList] from a (restricted form of a) hypergraph: 
  specifically, the only edges that will end up in the [TensorList] 
  are those with non-empty value, which will become AbstractTensors,
  and those with empty value and singleton sources and targets, which
  will become Deltas. We use vertex indices as label indexes. All vertices
  must have (non-empty) values, which are used as their types. *)
Ltac2 hypergraph_to_tensor_list (g : (TypeIdx, AbsIdx) Graph) : TensorList :=
  (* Establish the mapping between indices and types *)
  let vertex_type_map := 
    FMap.mapi (fun v vd => 
    let ty := match vvalue vd with 
    | Some ty => ty 
    | None => printf "WARNING: trying to convert graph to TensorList, but vertex %i has no value (type). Placeholder value -1 will be used" v;
      -1 end in 
    ty) (g.(vdata)) in 
  let vertex_type v := FMap.lookup vertex_type_map v in 
  (* TO DO: Fix this when we properly refactor to understand that upper and 
  lower indices are separate sets, hence can be the same (i.e. einstein 
  notation is valid, up to the lack of contractions Kₐᵃ for each repeated
  label a). For now, this is a nasty hack to make upper and lower indices
  different (simply, lower are even and upper are odd...) *)
  let lower_map v := v in (* Int.lsl v 1 in (* double *) *)
  let upper_map v := v in (* Int.lxor (Int.lsl v 1) 1 in (* double and add 1*) *)
  (* Construct abstract tensors and deltas from the edges *)
  let (abstracts, deltas) := FMap.fold (fun e ed (abs, ds) => 
    (* Look at the value of the edge *)
    match ed.(value) with 
    | None => (* Empty edges must have singleton sources and targets 
      of the same type, in which case they become deltas *)
      if Bool.and (Int.equal (List.length (ed.(s))) 1)
          (Int.equal (List.length (ed.(t))) 1) then 
        (* This is almost a valid delta; test types *)
        let a := List.hd (ed.(s)) in 
        let b := List.hd (ed.(t)) in 
        let ty_a := vertex_type a in 
        let ty_b := vertex_type b in 
        if Int.equal ty_a ty_b  then
        (* This is a valid delta! *)
          (abs, List.cons (ty_a, lower_map a, upper_map b) ds)
        else 
          (printf "WARNING: singleton edge (%i) between vertices %i and %i have different types (%i and %i). Edge will be ignored!" e a b ty_a ty_b;
          (abs, ds))
      else 
        (printf "WARNING: valueless edge %i is not singleton. It will be ignored!" e;
        (abs, ds))
    | Some abs_idx => (* Edge has a value, so will become an AbstractTensor *)
      let lower := List.map (fun v => (vertex_type v, lower_map v)) (ed.(s)) in 
      let upper := List.map (fun v => (vertex_type v, upper_map v)) (ed.(t)) in 
      (List.cons (abs_idx, lower, upper) abs, ds)
    end)
  (g.(edata)) ([], []) in 
  
  (* Now, we use the internal vertices to make our contractions *)
  let contractions := FMap.fold (fun v _vd cs => 
    if is_boundary g v then 
      (* Boundary vertex; do nothing *)
      cs else
    (* Internal vertex; this becomes a contraction *)
    let ty := vertex_type v in 
    List.cons (ty, lower_map v, upper_map v) cs
    ) (g.(vdata)) [] in 
  
  (* Finally, we have all our data *)
  mk_tensorlist contractions deltas abstracts.




Import Printing.

Ltac2 test_graph (ub : int) : (TypeIdx, AbsIdx) Graph :=
  let g := mk_graph () in 
  let rnge := List.range 0 ub in 
  let _verts := List.map (fun i => 
    add_vertex g (Some (Int.div i 2)) (-1)) rnge in
  let _edges := List.map (fun i => 
    add_edge g (List.firstn i rnge) (List.skipn i rnge) (Some i) (-1)) rnge in
  g.

Ltac2 test_tensorlist (ub : int) : TensorList :=
  hypergraph_to_tensor_list (test_graph ub).

Ltac2 test_tensorexpr (ub : int) : TensorExpr :=
  tensor_expr_of_tensor_list (hypergraph_to_tensor_list (test_graph ub)).

(* Testing tensor_expression_to_simplified: *)
  (* First, the initial tensorlist: *)
  Ltac2 Eval Message.print (print_tensorlist (
            (test_tensorlist 5))).
  (* Then, the tensorlist having been made an expression: *)
  Ltac2 Eval Message.print (print_tensorlist (
    tensor_expression_to_simplified (
          tensor_expr_of_tensor_list
          (test_tensorlist 5)))).



Ltac2 Eval Message.print (print_tensorexpr (
    tensor_expr_of_tensor_list
    (hypergraph_to_tensor_list (test_graph 5)))).



Ltac2 Eval 
  Message.print (print_int_graph (test_graph 5)).

Ltac2 Eval Message.print (print_int_graph
    (tensor_list_to_hypergraph 
    (hypergraph_to_tensor_list (test_graph 5)))).

(* Set Ltac2 Backtrace.


Ltac2 Set debug_match := true.

(* Ltac2 Eval 
  let m := (mk_match (test_graph 2) (test_graph 2) Int.equal) in
  Message.print (print_sep_list' (Message.concat (fprintf ", ") (Message.break 1 0)) 
    (List.cons m (List.flat_map more (more m))) print_match).
  let _ := try_add_vertex m 0 0 in 
  Message.print (print_match m).
 *)

Ltac2 Eval 
  let m := (mk_match (test_graph 2) (test_graph 2) Int.equal ) in
  let _ := try_add_vertex m 0 0 in 
  Message.print (print_match m).

Ltac2 Eval 
  Message.print (print_tensorlist 
    (hypergraph_to_tensor_list (test_graph 3))).

Ltac2 Eval Message.print (print_int_graph
    (tensor_list_to_hypergraph 
    (hypergraph_to_tensor_list (test_graph 3)))).


Ltac2 Eval hypergraph_to_tensor_list (test_graph 3).

Ltac2 Eval Message.print (print_int_graph
    (tensor_list_to_hypergraph 
    (hypergraph_to_tensor_list (test_graph 5)))).


Ltac2 Eval Message.print (print_tensorlist (
  tensor_expression_to_simplified (
        tensor_expr_of_tensor_list
        (hypergraph_to_tensor_list (test_graph 5))))).


    Ltac2 Eval Message.print (print_tensorexpr (
        tensor_expr_of_tensor_list
        (hypergraph_to_tensor_list (test_graph 5)))).

Ltac2 Eval tensor_expr_of_tensor_list
        (hypergraph_to_tensor_list (test_graph 3)).

Ltac2 Eval 
  let t := _ in 
  let (cs, inner) := extract_contractions t in 
  let (ds, abs) := decompose_contraction_free_expr inner in 
  let abs := List.map_filter parse_abstract abs in 
  mk_tensorlist cs ds abs.

Ltac2 Eval Message.print (print_tensorlist (
  tensor_expression_to_simplified (
        tensor_expr_of_tensor_list
        (hypergraph_to_tensor_list (test_graph 5))))).

Ltac2 Eval Message.print (print_int_graph
    (tensor_list_to_hypergraph 
    (hypergraph_to_tensor_list (test_graph 5)))).

Ltac2 Eval Message.print (print_int_graph
    (tensor_list_to_hypergraph (
      tensor_expression_to_simplified (
        tensor_expr_of_tensor_list
        (hypergraph_to_tensor_list (test_graph 5))
      )

    )
    )).
  

  
























Module Einstein.

Ltac2 Type EinsteinAtom := [
  EinsteinTensor (AbsIdx, Indices, Indices) | 
    (* A tensor symbol *)
  EinsteinDelta (VarIdx, VarIdx)
    (* A delta expression *)
].

Ltac2 Type EinsteinExpr := EinsteinAtom list.

Ltac2 einstein_labels (e : EinsteinExpr) : VarIdx list :=


Ltac2 relabel_lower_atom : (VarIdx -> VarIdx) -> EinsteinAtom -> EinsteinAtom :=
  fun f ea => match ea with 
  | EinsteinTensor idx lower upper => EinsteinTensor idx (List.map f lower) upper
  | EinsteinDelta a b => EinsteinDelta (f a) b
  end.

Ltac2 relabel_upper_atom : (VarIdx -> VarIdx) -> EinsteinAtom -> EinsteinAtom :=
  fun f ea => match ea with 
  | EinsteinTensor idx lower upper => EinsteinTensor idx lower (List.map f upper)
  | EinsteinDelta a b => EinsteinDelta a (f b)
  end.

Ltac2 relabel_lower : (VarIdx -> VarIdx) -> EinsteinExpr -> EinsteinExpr :=
  fun f => List.map (relabel_lower_atom f).

Ltac2 relabel_upper : (VarIdx -> VarIdx) -> EinsteinExpr -> EinsteinExpr :=
  fun f => List.map (relabel_upper_atom f).

Ltac2 replace_upper : VarIdx -> VarIdx -> EinsteinExpr -> EinsteinExpr :=
  fun a a' => relabel_upper (replace_int a a').

Ltac2 replace_lower : VarIdx -> VarIdx -> EinsteinExpr -> EinsteinExpr :=
  fun a a' => relabel_upper (replace_int a a').

Ltac2 atom_labels

End Einstein. *)