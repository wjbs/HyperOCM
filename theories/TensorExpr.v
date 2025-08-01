(* Require Import HyperOCM.hypergraph. *)
Require Import FSetExtra.
Require Import ListExtra.
Require PrintingExtra.


(* Require ComplexSum. *)
Require Import Ltac2.Init.

(* Convert an int to its decimal representation, as a string *)
Ltac2 string_of_int (n : int) : string := 
  Message.to_string (Message.of_int n).

(* Finds a string not in the given set [s] of identifiers. For a
  base string [b] (using "" if None is given), it returns [bn], 
  the concatenation of [b] with the (string representation of the)
  least (non-negative) integer [n] such that [bn] is not in the 
  set of identifiers. If [b] is not in [s], [b] is returned. *)
Ltac2 fresh_string (s : string FSet.t) (base : string option) : string :=
  let base := Option.default "" base in 
  let mk n := String.app base (string_of_int n) in 
  let rec go i :=
    if FSet.mem (mk i) s then 
      go (Int.add 1 i)
    else
      mk i in 
  if FSet.mem base s then 
    go 0
  else base.

(* A helper function to replace a given string with another *)
Ltac2 replace_str (a : string) (b : string) : string -> string :=
  fun c => if String.equal c a then b else c.

Ltac2 string_tag := FSet.Tags.string_tag.


(** An Ltac2 definition of semantic abstract tensor expressions. *)

(* An alias to indicate this is an index variable in a tensor expression *)
Ltac2 Type VarIdx := string.

(* An alias to indicate this is a variable indexing a (summable) Coq type *)
Ltac2 Type TypeIdx := string.

(* An alias to indicate this variable indexes an abstract tensor expression 
  (of an unspecified arity) *)
Ltac2 Type AbsIdx := string.

(* The information of a register, comprising a variable and its 
  associated type *)
Ltac2 Type TypedVar := TypeIdx * VarIdx.

(* The data associated to a fully abstract tensor (e.g. a generator), 
  comprising the name of the tensor, the registers it connects to as 
  inputs, and the registers it connects to as outputs. *)
Ltac2 Type AbsData := AbsIdx * TypedVar list * TypedVar list. 

(* A set of typed variables, isomorphic to a [TypedVar FSet.t] 
  (due to limitations of how FSet is implemented, this cannot 
  be used directly) *)
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
  equal_pair String.equal String.equal x y.

Ltac2 equal_absdata (x : AbsData) (y : AbsData) : bool :=
  let l_eq := List.equal equal_typedvar in 
  equal_triple String.equal l_eq l_eq x y.

(* The type of formal tensor expressions, as abstract objects. 
  They are semi-typed, in that each time a VarIdx is used, a TypeIdx
  is used too to indicate the type of that VarIdx. In this way, VarIdx
  collisions can only occur within a type, and even more importantly
  variables can be freely relabeled. *)
Ltac2 Type rec TensorExpr := [
  Abstract (AbsIdx, TypedVar list, TypedVar list) 
    (* An abstract tensor, along with the registers to which it is 
      applied as inputs and as outputs, respectively.
      Each index is stored along with its type. *)
| Product (TensorExpr list)
    (* The product of a list of tensor expressions, 
      conventionally left-associated *)
| Sum (TypedVar, TensorExpr) 
    (* The sum/contraction of a tensor expression with respect to a
      given variable *)
(* Old, removed constructors:
| Delta (TypeIdx, VarIdx, VarIdx) 
    (* A element, with [Delta a b] meaning [δₐᵇ] 
      with [a], [b] of type (indexed by) [t] *)
| One 
    (* The tensor 1 *) *)
].

(* A simplified/semi-normal form of a tensor expresion which extracts 
  the sums (which are outermost) and concatenates the product tensors *)
Ltac2 Type TensorList := {
  sums : TypedVar list;
  abstracts : AbsData list
}.

(* Convert a TensorList to a TensorExpr in the natural way*)
Ltac2 tensorexpr_of_tensorlist (t : TensorList) : TensorExpr :=
  List.fold_right (fun register t => Sum register t) (t.(sums))
    (let l := List.map (fun (name, lower, upper) => Abstract name lower upper) 
      (t.(abstracts)) in 
    if Int.equal (List.length l) 1 then List.hd l else Product l).

Module Printing.
Export PrintingExtra.
Import PpExtra.

(* Test if a tensor is a Sum *)
Local Ltac2 is_sum (t : TensorExpr) : bool :=
  match t with 
  | Sum _ _ => true
  | _ => false
  end.

(* Test if a tensor is a Product *)
Local Ltac2 is_product (t : TensorExpr) : bool :=
  match t with 
  | Product _ => true
  | _ => false
  end.

(* Test if a tensor is an Abstract *)
Local Ltac2 is_abstract (t : TensorExpr) : bool :=
  match t with 
  | Abstract _ _ _ => true
  | _ => false
  end.

Ltac2 pr_abs_data pr_tyvar name (lower : TypedVar list) 
  (upper : TypedVar list) : message :=
  str name ++ brk 0 2 ++ str "_" ++ str "[" 
  ++ prlist_with_sep pr_comma pr_tyvar lower ++ str "]" 
  ++ brk 0 2 ++ str "^" ++ str "[" 
  ++ prlist_with_sep pr_comma pr_tyvar upper ++ str "]".

(* Prints a tensor expression, marking the types of any 
  variables _not_ in the given set of bound variables explicitly *)
Ltac2 rec pr_tensorexpr_with_varlist (bound_vars : TypedVarSet) 
  (t : TensorExpr) : message := 
  let pr_type_var ty var := str var ++ spc() ++ pr_colon() ++ str ty in
  let pr_typedvar (paren : bool)
    ((ty, var) : TypedVar) : message := 
    if FSet2.mem ty var bound_vars then 
      (* The type is implicit as the variable is bound; don't label *) 
      str var
    else 
      (* The type is not implicit; label *)
      let msg := pr_type_var ty var in 
      if paren then (* Surround with parens *) surround msg 
        else (* Leave alone *) msg
    in 
  match t with 
  | Abstract name lower upper => 
    (* Print the abstract tensor and the registers it references *)
    pr_abs_data (pr_typedvar false) name lower upper
  | Product ts => 
    (* Print the tensors separated by "⋅", parenthesizing as necessary to 
    close summations and indicate association *)
    if Int.equal (List.length ts) 0 then 
      (* Special case; the empty product is "(1)" *)
      str "(1)" else
    if Int.equal (List.length ts) 1 then 
      (* Special case; just parenthesize whatever's inside *)
      surround (pr_tensorexpr_with_varlist bound_vars (List.hd ts)) else
    (* Length >= 2 *)
    let pr_dot () := str " ⋅" ++ spc() in 
    let (msg_base, last_msg, _) :=
      List.fold_left (fun (msg_base, prev_msg, last_was_sum) (idx, t) =>
      let msg_t := pr_tensorexpr_with_varlist bound_vars t in 
      (* If the current term [t] is a product, we need to parenthesize it*)
      let msg_t' := if is_product t then surround msg_t else msg_t in 
      (* If the previous term was a sum ([last_was_sum]), we need to 
        parenthesize it (we put this off so we don't have to parenthesize 
        a sum as the final multiplicand)*)
      let prev_msg' := if last_was_sum then surround prev_msg else prev_msg in
      
      match idx with 
      | 0 => 
        (* If we are the first term, the previous message and 
          base message are both empty, and we just need to set 
          the prev_msg and say whether we are a sum *)
        (mt(), msg_t', is_sum t)
      | 1 => 
        (* If we are the second term, the previous message simply 
          becomes the msg_base, and we pass along ourselves and 
            whether we're a sum *)
        (prev_msg', msg_t', is_sum t)
      | _ => 
      (* In the general case, append the previous message to the 
        accumulating msg_base, pass on our message, and record 
        whether [t] is a sum *)
      (msg_base ++ pr_dot() ++ prev_msg', msg_t', is_sum t)
      end
    ) (mt(), mt(), false) (List.enumerate ts) in
    msg_base ++ pr_dot() ++ last_msg
  
  | Sum (ty, var) t => 
    str "∑" ++ spc() ++ pr_type_var ty var ++ pr_comma() ++ 
    pr_tensorexpr_with_varlist (FSet2.add ty var bound_vars) t
  end.

(* Print a tensor expression, labeling the types of any unbound variables *)
Ltac2 pr_tensorexpr (t : TensorExpr) : message :=
  pr_tensorexpr_with_varlist (FSet2.empty string_tag string_tag) t.

Ltac2 pr_tensorlist_as_tensorexpr (t : TensorList) : message :=
  pr_tensorexpr (tensorexpr_of_tensorlist t).

Ltac2 pr_tensorlist (t : TensorList) : message :=
  let pr_type_var ty var := str var ++ spc() ++ pr_colon() ++ str ty in
  let pr_typedvar (paren : bool)
    ((ty, var) : TypedVar) : message := 
      let msg := pr_type_var ty var in 
      if paren then (* Surround with parens *) surround msg 
        else (* Leave alone *) msg
    in 
  str "!∑" ++ spc() ++ 
    prlist_with_sep (pr_comma) (pr_typedvar false) (t.(sums)) 
    ++ str ";" ++ spc() ++
    hov 2 (
    prlist_with_sep (fun()=> str " *" ++ spc())
      (fun (name, lower, upper) => 
        hov 2 (str "@" ++ pr_abs_data (pr_typedvar false) name lower upper))
      (t.(abstracts))).

End Printing.

(* The registers present in a tensor expression, ignoring 
  shadowing by binders (i.e. sums). Note that registers 
  appearing in binders but no other terms _do_ appear. *)
Ltac2 register_set_full (t : TensorExpr) : TypedVarSet := 
  let rec go t :=
    match t with 
    | Abstract _ lower upper => 
      FSet2.of_list string_tag string_tag (List.append lower upper)
    | Product ts => 
      List.fold_right (fun t vars => FSet2.union (go t) vars) 
        ts (FSet2.empty string_tag string_tag)
    | Sum (ty, var) t => 
      FSet2.add ty var (go t)
    end in 
  go t.

(* The registers present in a tensor expression, omitting 
  those shadowed by binders (i.e. sums). Note that registers 
  appearing in binders but no other terms do not appear. *)
Ltac2 free_register_set (t : TensorExpr) : TypedVarSet := 
  let rec go t :=
    match t with 
    | Abstract _ lower upper => 
      FSet2.of_list string_tag string_tag (List.append lower upper)
    | Product ts => 
      List.fold_right (fun t vars => FSet2.union (go t) vars) 
        ts (FSet2.empty string_tag string_tag)
    | Sum (ty, var) t => 
      FSet2.remove ty var (go t)
    end in 
  go t.

(* The set of names of abstract tensors apearing in the tensor expression *)
Ltac2 rec abstract_index_set (t : TensorExpr) : AbsIdx FSet.t := 
  let rec go t := 
    match t with 
    | Abstract name _lower _upper => 
      FSet.add name (FSet.empty string_tag)
    | Product ts => 
      List.fold_right (fun t names => 
        FSet.union (go t) names) ts (FSet.empty string_tag)
    | Sum _ t => go t
    end
  in go t.

(* Replace one register with another, ignoring occurences of
  that register shadowed by a binder (i.e. sum). Returns the 
  relabeled TensorExpr and a bool indicating if replacements
  occured. *)
Ltac2 relabel_one (old : TypedVar) (new : TypedVar) (t : TensorExpr) 
  : TensorExpr * bool :=
  let replace reg := 
    if equal_typedvar reg old then (new, true) else (reg, false) in 
  let rec go t :=
    match t with 
    | Abstract name lower upper => 
      let replaces l := 
        List.fold_right (fun reg (acc, b) => 
          let (reg', changed) := replace reg in 
          (reg' :: acc, Bool.or changed b)) l ([], false) in 
      let (lower', lower_changed) := replaces lower in 
      let (upper', upper_changed) := replaces upper in 
      (Abstract name lower' upper', Bool.or lower_changed upper_changed)
    | Product ts => 
      let (ts', changed) := 
        List.fold_right (fun t (ts', b) =>
          let (t', changed) := go t in 
          (t' :: ts', Bool.or changed b)) ts ([], false) in 
      (Product ts', changed)
    | Sum reg' t => 
      if equal_typedvar reg' old then 
        (Sum reg' t, false) else
      let (t', changed) := go t in 
      (Sum reg' t', changed)
    end in 
  go t.

Local Ltac2 replace_list (f : 'a -> 'a * bool) (l : 'a list) : 'a list * bool :=
  List.fold_right (fun a (acc, b) => 
    let (a', changed) := f a in 
    (a' :: acc, Bool.or changed b)) l ([], false).

(* Replace one register with another, including under binders,
  in a [TensorList]. Returns the relabeled [TensorList] and a 
  bool indicating if replacements occured. *)
Ltac2 relabel_one_tensorlist 
  (old : TypedVar) (new : TypedVar) (t : TensorList)
  : TensorList * bool :=
  let replace reg := 
    if equal_typedvar reg old then (new, true) else (reg, false) in 
  let replace_abs (name, lower, upper) : AbsData * bool :=
    let replaces l := replace_list replace l in 
    let (lower', lower_changed) := replaces lower in 
    let (upper', upper_changed) := replaces upper in 
    ((name, lower', upper'), Bool.or lower_changed upper_changed) in 
  
  let (sums', sums_changed) := replace_list replace (t.(sums)) in 
  let (abstracts', abs_changed) := replace_list replace_abs (t.(abstracts)) in 

  {sums := sums'; abstracts := abstracts'}, Bool.or sums_changed abs_changed.

(* Remove the first occurance of a summation over a given register from 
  a list of [TensorList]s. "first" means first in the list, and after that
  first in the list of sums within the [TensorList].  *)
Ltac2 remove_one_sum (reg : TypedVar) (tls : TensorList list) : 
  TensorList list :=
  let rec removes (sums : TypedVar list) : TypedVar list * bool :=
    match sums with 
    | [] => ([], false)
    | reg' :: sums' => 
      if equal_typedvar reg' reg then 
        (sums, true) else
      let (sums'', changed) := removes sums' in 
      (reg :: sums'', changed)
    end in 
  let rec go tls :=
    match tls with 
    | [] => []
    | tl :: tls => 
      let (sums', changed) := removes (tl.(sums)) in 
      if changed then
        {tl with sums := sums'} :: tls
      else 
        tl :: go tls
    end in 
  go tls.

(* The set of registers appearing in a [TensorList], whether bound or free *)
Ltac2 tensorlist_register_set (t : TensorList) : TypedVarSet :=
  FSet2.of_list string_tag string_tag 
    (List.append (t.(sums))
    (List.flat_map (fun (_, lower, upper) => List.append lower upper) 
      (t.(abstracts)))).

(* The set of registers appearing in a [TensorList] under binders
  (i.e., the set of registers bound by summation in a [TensorList]) *)
Ltac2 tensorlist_bound_set (t : TensorList) : TypedVarSet :=
  FSet2.of_list string_tag string_tag (t.(sums)).

(* The set of free registers appearing in a [TensorList], so not
  under binders *)
Ltac2 tensorlist_free_set (t : TensorList) : TypedVarSet :=
  FSet2.diff (tensorlist_register_set t) (tensorlist_bound_set t).

(* Find a fresh name for the given offending identifier among a 
  given set of registers by appending the least (non-negative) 
  integer to the variable which makes it free *)
Ltac2 fresh_register (reg : TypedVar) (avoid : TypedVarSet) : TypedVar :=
  let (ty, var) := reg in 
  let used := FSet2.fix_fst ty avoid in (* The set of variable names to be avoided associated to this type *)
  let fresh_var := 
    fresh_string used (Some var) in 
  (ty, fresh_var).

(* Replace one register name with another, if it is unbound, in the 
  data representing a [TensorList]. If the register appears in the 
  sums, no change is made. Returns the new data, and whether any 
  change was made. *)
Ltac2 relabel_one_in_tensorlist_data (old : TypedVar) (new : TypedVar) 
  (sums : TypedVar list) (abs : AbsData list) : 
    TypedVar list * AbsData list * bool :=
  if List.mem equal_typedvar old sums then
    (sums, abs, false) 
    else
  let replace reg := 
    if equal_typedvar reg old then (new, true) else (reg, false) in 
  let replace_abs (name, lower, upper) : AbsData * bool :=
    let replaces l := replace_list replace l in 
    let (lower', lower_changed) := replaces lower in 
    let (upper', upper_changed) := replaces upper in 
    ((name, lower', upper'), Bool.or lower_changed upper_changed) in 
  let (abs', changed) := replace_list replace_abs abs in 
  (sums, abs', changed).


(* Take the product of two [TensorList]s, with the sums of the left
  term appearing before the sums of the right. Bound variables are 
  relabeled as necessary, avoiding the set [avoids] of variables.
  Returns the combined list. *)
Ltac2 tensorlist_times (avoids : TypedVarSet) 
  (l : TensorList) (r : TensorList) : TensorList :=
  (* Helper functions unpacking values. *)
  let rec go (avoid : TypedVarSet) 
    (lsums : TypedVar list) (labs : AbsData list) 
    (rsums : TypedVar list) (rabs : AbsData list) : (TypedVar list * AbsData list) :=
    (* INVARIANT: [avoid] includes all free variables of the [TensorList]s 
    represented by [lsums, labs] and [rsums, rabs]. *)
    match lsums with 
    | [] => 
      match rsums with 
      | [] => (* No binders left! Just concatenate the abstracts *)
        ([], List.append labs rabs)
      | (ty, var) :: rsums' => 
        (* Need to make sure the register is free, or else make it so *)
        if FSet2.mem ty var avoid then 
          let (ty', var') := fresh_register (ty, var) avoid in 
          (* Relabel the data of the RHS *)
          let (rsums'', rabs', changed) :=
            relabel_one_in_tensorlist_data (ty, var) (ty', var')
              rsums' rabs in 
          if changed then 
            (* We used the variable, so need to avoid it 
              in the recursive call *)
            let (sums, abs) :=
              go (FSet2.add ty var avoid) lsums labs rsums'' rabs' in 
            (* Add our sum to the outside *)
            ((ty', var') :: sums, abs)
          else
            (* No change was made; this sum is actually trivial! 
              TODO: I'm not sure the logic works; here we should be able
              to cut down on the number of identifiers we use. However, 
              for safety, we can just make sure all identifiers are unique. *)
            let (sums, abs) := 
              go (FSet2.add ty' var' avoid) lsums labs rsums'' rabs' in 
            ((ty', var') :: sums, abs)
        else (* This sum is non-conflicting; we can just add it *)
          let (sums, abs) := 
            go (FSet2.add ty var avoid) lsums labs rsums' rabs in 
          ((ty, var) :: sums, abs)
      end
    | (ty, var) :: lsums' => 
      (* Need to make sure the register is free, or else make it so *)
      if FSet2.mem ty var avoid then 
        let (ty', var') := fresh_register (ty, var) avoid in 
        (* Relabel the data of the RHS *)
        let (lsums'', labs', changed) :=
          relabel_one_in_tensorlist_data (ty, var) (ty', var')
            lsums' labs in 
        if changed then 
          (* We used the variable, so need to avoid it 
            in the recursive call *)
          let (sums, abs) :=
            go (FSet2.add ty var avoid) lsums'' labs' rsums rabs in 
          (* Add our sum to the outside *)
          ((ty', var') :: sums, abs)
        else
          (* No change was made; this sum is actually trivial! 
            TODO: I'm not sure the logic works; here we should be able
            to cut down on the number of identifiers we use. However, 
            for safety, we can just make sure all identifiers are unique. *)
          let (sums, abs) := 
            go (FSet2.add ty' var' avoid) lsums'' labs' rsums rabs in 
          ((ty', var') :: sums, abs)
      else (* This sum is non-conflicting; we can just add it *)
        let (sums, abs) := 
          go (FSet2.add ty var avoid) lsums' labs rsums rabs in 
        ((ty, var) :: sums, abs)
      end in 

  let avoid_vars := FSet2.union avoids 
    (FSet2.union (tensorlist_free_set l) (tensorlist_free_set r)) in 
  
  let (sums, abs) := 
    go avoid_vars (l.(sums)) (l.(abstracts)) 
      (r.(sums)) (r.(abstracts)) in 
  {sums := sums; abstracts := abs}.

Ltac2 empty_tensorlist := {sums := []; abstracts := []}.

(* Take the product of a list of [TensorList]s, relabeling bound variables 
  as necessary, avoiding a given set of variables. *)
Ltac2 tensorlist_product (avoids : TypedVarSet) (tls : TensorList list) : 
  TensorList :=
  List.fold_right (tensorlist_times avoids) tls empty_tensorlist.

(* Convert a [TensorExpr] to a [TensorList] by extracting summations, 
  renaming variables as necessary, and combining the products *)
Ltac2 tensorlist_of_tensorexpr (t : TensorExpr) : TensorList :=
  let rec go (avoid : TypedVarSet) t :=
    match t with 
    | Abstract name lower upper => 
      {sums := []; abstracts := [(name, lower, upper)]}
    | Product ts => 
      tensorlist_product avoid (List.map (go avoid) ts)
    | Sum (ty, var) t => 
      let tl := go (FSet2.add ty var avoid) t in 
      {tl with sums := ((ty, var) :: tl.(sums))}
    end in 
  let used_vars := free_register_set t in 
  go (used_vars) t.

Import Printing.
Import PrintingExtra.
Import Message.
Import PpExtra.

(* Check whether two terms are alpha-convertible, i.e. equal up to 
  renaming variables bound in contractions. *)
Ltac2 rec alpha_convertible (t : TensorExpr) (s : TensorExpr) : bool :=
  match (t, s) with 
  | Abstract name low up, Abstract name' low' up' => 
    equal_absdata (name, low, up) (name', low', up')
  | Product ts, Product ss => 
    List.equal alpha_convertible ts ss
  | Sum (ty, var) t', Sum (ty', var') s' => 
    (* Shortcut for equal identifiers *)
    if equal_typedvar (ty, var) (ty', var') then 
      alpha_convertible t' s' else
    if String.equal ty ty' then 
      (* TODO: This is a real hack to avoid issues where binders
        bind multiple values (e.g. 
          ∑ a : A, ∑ a : A, f a a is not convertible to
          ∑ b : A, ∑ c : A, f b c). Can we do better, or be more 
        sure of correctness? Maybe find an existing algorithm to implement? *)
      let new_tyvar := fresh_register (ty, var) 
        (FSet2.union 
          (register_set_full t')
          (register_set_full s')) in 
      let (s'_renamed, _) := relabel_one (ty', var') new_tyvar s' in 
      let (t'_renamed, _) := relabel_one (ty, var) new_tyvar t' in
      (* Std.assert_true *)

      
      (* let pr_tyvar t v := surround (str v ++ spc()
        ++ pr_colon() ++ str t) in
      let conv_l := alpha_convertible t' s'_renamed in 
      let conv_r := alpha_convertible t'_renamed s' in 
      print (str "Old reg" ++ pr_colon() ++ pr_tyvar ty var ++ pr_semicolon()
        ++ fnl() ++ str "New reg" ++ pr_colon() ++ pr_tyvar ty' var'
        ++ fnl() ++ str "t' = " ++ pr_tensorexpr t' ++ pr_semicolon()
        ++ fnl() ++ str "s' = " ++ pr_tensorexpr s' ++ pr_semicolon()
        ++ fnl() ++ str "t'_renamed = " ++ pr_tensorexpr t'_renamed ++ pr_semicolon()
        ++ fnl() ++ str "s'_renamed = " ++ pr_tensorexpr s'_renamed ++ pr_semicolon()
        ++ fnl() ++ str "t' ~ s'_renamed = " ++ bool conv_l ++ pr_semicolon()
        ++ fnl() ++ str "t'_renamed ~ s' = " ++ bool conv_r ++ pr_semicolon()
        ++ fnl() ++ str "equiv = " ++ bool (Bool.and conv_l conv_r)
        ); *)
      alpha_convertible t'_renamed s'_renamed
    else
      false
  | _ => false
  end.

(* Test whether two [TensorList]s are equal up to permutation *)
Ltac2 tensorlist_perm_eq (t : TensorList) (s : TensorList) : bool :=
  Bool.and 
    (Permutations.perm_eq equal_typedvar (t.(sums)) (s.(sums)))
    (Permutations.perm_eq equal_absdata (t.(abstracts)) (s.(abstracts))).

(* Auxiliary function to test whether the data comprising two 
  [TensorList]s are equal up to permutation and alpha-equivalence. 
  If they are, returns the swap list of the abstract tensors
  and the relabeling of the sums necessary to turn the 
  _left_ argument(s) into the _right_, _up to permutation of sums_. *)
Ltac2 tensorlist_data_alpha_perm_eq
  (lsums : TypedVar list) (labs : AbsData list)
  (rsums : TypedVar list) (rabs : AbsData list) : 
  ( (int * int) list * (* Abstracts swap list *)
    (TypeIdx, VarIdx, VarIdx) FMap2.t (* Relabeling *)
    ) option :=
  let relabel_sums (old : TypedVar) (new : TypedVar) (l : TypedVar list) :=
    List.map (fun reg => if equal_typedvar reg old then new else reg)
      l in 
  let relabel_abs (old : TypedVar) (new : TypedVar) (abs : AbsData list) :=
    let rel_sums := relabel_sums old new in 
    List.map (fun (name, lower, upper) => 
      (name, rel_sums lower, rel_sums upper))
      abs in 
  (* NOTE: [avoid] contains all the variables, free or bound, 
     of all the data *)
  let avoid_list := List.concat [lsums; rsums;
    List.flat_map (fun (_, l, u) => List.append l u) 
      (List.append labs rabs)] in 
  let avoid := FSet2.of_list string_tag string_tag avoid_list in

  let rec go avoid lsums labs rsums rabs :
      ((int * int) list * (TypeIdx, VarIdx, VarIdx) FMap2.t) option 
      := 
    (* INVARIANT: [avoid] contains all the variables, 
       free or bound, of all the data *)
    match lsums with 
    | [] => 
      (* If no sums on LHS, must have no sums on RHS*)
      if Bool.neg (List.is_empty rsums) then 
        None else 
      (* Now, no sums on either side, so we need only test 
        equality up to permutations, no alpha-equivalence *)
      Option.bind (Permutations.perm_reordering_swaps_after 
        equal_absdata labs rabs)
        (fun swaps => 
        Some (swaps, FMap2.empty string_tag string_tag))
    | (ty, var) :: lsums' => 
      (* If we have a sum to deal with, find the indices in [rsums] 
        with variables of matching types, hence that we can possibly
        rename into.  *)
      let relabeling_opts := 
        List.filter (fun (_idx, (ty', _var)) => String.equal ty ty')
          (List.enumerate rsums) in
      (* Now, get the first of these that works, i.e. for which 
        the recursive call succeeds. (For efficiency reasons on 
        the proof generation side, we search in reverse, i.e. 
        with fold_right) *)
      fst (List.fold_right 
        (fun (idx, (_ty, var')) (may_match, avoid) => 
          (* For each matching index... *)
          match may_match with
          | Some t => 
            (* If a previous match worked out, use that *)
            (Some t, avoid)
          | None => 
            (* Otherwise, set up the recursive call *)
            
            (* Set up the relabelings *)
            let lold := (ty, var) in let rold := (ty, var') in 
            (* Get a fresh identifier, for robust alpha-equivlance testing *)
            let newreg := fresh_register lold avoid in 
            let avoid' := FSet2.add (fst newreg) (snd newreg) avoid in 
            
            
            (* Note: Relabeling the LHS sums is only necessary 
              if they are redundant (which is officially unsupported), 
              but for safety we may as well *)
            let lsums'_rel := 
              relabel_sums lold newreg lsums' in 
            let rsums'_rel := 
              relabel_sums rold newreg (remove_nth idx rsums) in 
            let labs_rel := relabel_abs lold newreg labs in 
            let rabs_rel := relabel_abs rold newreg rabs in 
            

            (* Now, try the recursive call *)
            (Option.bind 
              (go avoid' lsums'_rel labs_rel rsums'_rel rabs_rel)
              (fun (swaps, relabelings) => 
              (Some (swaps, FMap2.add ty var var' relabelings))), avoid')
          end)
        relabeling_opts (None, avoid))
    end
  in 
  go avoid lsums labs rsums rabs.
        



(* Test whether two [TensorList]s are equal up to permutation
  and alpha-equivalence (though preserving free variables).
  If they are, returns the swap list of the sums, the swap list 
  of the abstract tensors, and the relabeling of the sums 
  necessary to turn the  _left_ argument(s) into the _right_. *)
Ltac2 tensorlist_alpha_perm_eq_data (l : TensorList) (r : TensorList) :
  ( (int * int) list * (* Sums swap list *)
    (int * int) list * (* Abstracts swap list *)
    (TypeIdx, VarIdx, VarIdx) FMap2.t (* Relabeling *)
    ) option :=
  Option.bind (tensorlist_data_alpha_perm_eq 
    (l.(sums)) (l.(abstracts)) (r.(sums)) (r.(abstracts)))
  (fun (abs_swaps, relabelings) => 
    (* Now, just need to compute the swaps for the sums *)
    Option.bind (Permutations.perm_reordering_swaps_after equal_typedvar
      (List.map (fun (ty, var) => 
          (ty, Option.default var 
            (FMap2.find_opt ty var relabelings)))
        (l.(sums)))
      (r.(sums))) 
  (fun sum_swaps => 
    Some (sum_swaps, abs_swaps, relabelings))).

(* Test whether two [TensorList]s are equal up to permutation
  and alpha-equivalence (though preserving free variables). *)
Ltac2 tensorlist_alpha_perm_eq (l : TensorList) (r : TensorList) : bool :=
  match tensorlist_alpha_perm_eq_data l r with 
  | Some _ => true
  | None => false
  end.


(* Test whether two [TensorExpr]s are semantically equal, i.e.
  up to renaming of bound variales, distributivity, and 
  commutativity. In particular, convert them to [TensorList]s 
  and test for the same. *)
Ltac2 tensorexpr_semantically_equal (t : TensorExpr) (s : TensorExpr) : bool :=
  tensorlist_alpha_perm_eq 
    (tensorlist_of_tensorexpr t)
    (tensorlist_of_tensorexpr s).

(* Test whether two tensor expressions are literally equal *)
Ltac2 rec equal_tensorexpr (t : TensorExpr) (s : TensorExpr) : bool :=
  match t, s with 
  | Product ts, Product ss => 
    List.equal equal_tensorexpr ts ss
  | Sum treg t, Sum sreg s => 
    match equal_typedvar treg sreg with 
    | false => false
    | true => equal_tensorexpr t s
    end
  | Abstract tname tlow tup, Abstract sname slow sup => 
    equal_absdata (tname, tlow, tup) (sname, slow, sup)
  | _, _ => false
  end.

(* Test whether two [TensorList]s are literally equal *)
Ltac2 equal_tensorlist (t : TensorList) (s : TensorList) : bool :=
  Bool.and 
    (List.equal equal_typedvar (t.(sums)) (s.(sums)))
    (List.equal equal_absdata (t.(abstracts)) (s.(abstracts))).

Module TensorExprNotation.

Ltac2 Notation "@" fnc(ident)
  "_[" lower(list0(seq(ident, ":", ident), ",")) "]"
  "^[" upper(list0(seq(ident, ":", ident), ",")) "]" : 2 :=
  Abstract (Ident.to_string fnc)
    (List.map (fun (v, t) => 
      (Ident.to_string t, Ident.to_string v)) lower)
    (List.map (fun (v, t) => 
      (Ident.to_string t, Ident.to_string v)) upper).


Ltac2 Notation "∑" var(ident) ":" type(ident) "," body(next) : 4 :=
  Sum (Ident.to_string type, Ident.to_string var) body.

(* Multiply two [TensorExpr]s, with left associativity *)
Ltac2 tprod2 (l : TensorExpr) (r : TensorExpr) : TensorExpr :=
  match l with 
  | Product ts => Product (List.append ts [r])
  | _ => Product [l; r]
  end.

Ltac2 Notation l(self) "*" r(self) : 3 :=
  tprod2 l r.


(* Notation for [TensorList]s *)


Ltac2 Notation "!∑" 
  registers(list0 (seq(ident,":",ident), ","))
  ";"
  abstracts(list0(
    seq(
      "@", ident,
      "_[", list0(seq(ident, ":", ident), ","), "]",
      "^[", list0(seq(ident, ":", ident), ","), "]"
    ),
    "*"
  )) : 4 :=
  let of := Ident.to_string in 
  let ofs := List.map (fun (var, ty) => (of ty, of var)) in 
  {sums := ofs registers;
  abstracts := List.map (fun (name, lower, upper) => 
      (of name, ofs lower, ofs upper)) abstracts}.

End TensorExprNotation.

Module Testing.

(* TODO: Testing *)


Import TensorExprNotation.
Import Printing.



(* FIXME: Move *)
Ltac2 uncurry (f : 'a -> 'b -> 'c) : 'a * 'b -> 'c :=
  fun (a, b) => f a b.
(* FIXME: Move *)
Ltac2 curry (f : 'a * 'b -> 'c) : 'a -> 'b -> 'c :=
  fun a b => f (a, b).
(* FIXME: Move *)
Ltac2 neg_rel (f : 'a -> 'b -> bool) : 'a -> 'b -> bool :=
  fun a b => Bool.neg (f a b).

(* Test that a [TensorExpr] is literally equal to itself 
  after being converted to and from a [TensorList] *)
Ltac2 test_tensorexpr_eq_to_from_tensorlist (t : TensorExpr) : UTest.t :=
  UTest.value_eqv_pr 
    (equal_tensorexpr)
    (Printing.pr_tensorexpr) 
    "TensorExpr should be equal to itself after conversion to and from a TensorList"
    t
    (tensorexpr_of_tensorlist (tensorlist_of_tensorexpr t)).

(* Test that a [TensorList] is literally equal to itself
  after being converted to and from a [TensorExpr] *)
Ltac2 test_tensorlist_eq_to_from_tensorexpr (t : TensorList) : UTest.t :=
  UTest.value_eqv_pr 
    (equal_tensorlist)
    (Printing.pr_tensorlist) 
    "TensorList should be equal to itself after conversion to and from a TensorExpr"
    t
    (tensorlist_of_tensorexpr (tensorexpr_of_tensorlist t)).

(* Test the value of a [TensorExpr] after being converted to 
  a [TensorList], up to alpha equivlance*)
Ltac2 test_tensorexpr_to_tensorlist_val (t : TensorExpr) (tl : TensorList) : UTest.t :=
  UTest.value_eqv_pr 
    (fun tl tl' => 
      (alpha_convertible (tensorexpr_of_tensorlist tl) (tensorexpr_of_tensorlist tl')))
    (Printing.pr_tensorlist)
    "TensorExpr should have the given value after conversion to a TensorList, up to alpha-equivalence"
    tl
    (tensorlist_of_tensorexpr t).

(* Test the notation for tensor expressions *)
Ltac2 test_tensorexpr_notation_value (exp : TensorExpr) (test_val : TensorExpr) : UTest.t :=
  UTest.value_eqv_pr 
    (equal_tensorexpr)
    (Printing.pr_tensorexpr) 
    "TensorExpr notation test"
    exp
    (test_val).

(* Test the notation for tensor lists *)
Ltac2 test_tensorlist_notation_value (exp : TensorList) (test_val : TensorList) : UTest.t :=
  UTest.value_eqv_pr 
    (equal_tensorlist)
    (Printing.pr_tensorlist) 
    "TensorList notation test"
    exp
    (test_val).

(* Test two tensors are equal up to alpha-equivalence *)
Ltac2 test_tensors_alpha_equiv on_err (exp : TensorExpr) (test_val : TensorExpr) : UTest.t :=
  UTest.value_eqv_pr 
    (alpha_convertible)
    (Printing.pr_tensorexpr) 
    (String.concat "" ["tensors were not alpha equivalent! Message: "; on_err])
    exp
    (test_val).


(* Test two tensors are _not_ equal up to alpha-equivalence *)
Ltac2 test_tensors_non_alpha_equiv on_err 
  (exp : TensorExpr) (test_val : TensorExpr) : UTest.t :=
  UTest.value_eqv_pr 
    (neg_rel alpha_convertible)
    (Printing.pr_tensorexpr) 
    (String.concat "" ["tensors were alpha equivalent and should not ";
      "have been! Message: "; on_err])
    exp
    (test_val).

(* Test two [TensorList]s are equal up to permutation, but not alpha-equivalence *)
Ltac2 test_tensorlists_are_perm_eq (exp : TensorList) (test_val : TensorList) : UTest.t :=
  UTest.value_eqv_pr
    (tensorlist_perm_eq)
    (pr_tensorlist) 
    "TensorLists should be equal up to permutation"
    exp
    test_val.

(* Test two [TensorList]s are equal up to permutation and alpha-equivalence *)
Ltac2 test_tensorlists_are_alpha_perm_eq (exp : TensorList) (test_val : TensorList) : UTest.t :=
  UTest.value_eqv_pr
    (tensorlist_alpha_perm_eq)
    (pr_tensorlist) 
    "TensorLists should be equal up to permutation and alpha-equivalence"
    exp
    test_val.

(* Test two [TensorExpr]s are equal up to semantic *)
Ltac2 test_tensorexprs_are_sem_eq (exp : TensorExpr) (test_val : TensorExpr) : UTest.t :=
  UTest.value_eqv_pr
    (tensorexpr_semantically_equal)
    (pr_tensorexpr) 
    "TensorExprs should be equal up to permutation and alpha-equivalence"
    exp
    test_val.

(* Test two [TensorList]s are not equal up to permutation, but not alpha-equivalence *)
Ltac2 test_tensorlists_not_perm_eq (exp : TensorList) (test_val : TensorList) : UTest.t :=
  UTest.value_eqv_pr
    (neg_rel tensorlist_perm_eq)
    (pr_tensorlist) 
    "TensorLists should be equal up to permutation"
    exp
    test_val.

(* Test two [TensorList]s are not equal up to permutation and alpha-equivalence *)
Ltac2 test_tensorlists_not_alpha_perm_eq (exp : TensorList) (test_val : TensorList) : UTest.t :=
  UTest.value_eqv_pr
    (neg_rel tensorlist_alpha_perm_eq)
    (pr_tensorlist) 
    "TensorLists should be equal up to permutation and alpha-equivalence"
    exp
    test_val.

(* Test two [TensorExpr]s are not equal up to semantic *)
Ltac2 test_tensorexprs_not_sem_eq (exp : TensorExpr) (test_val : TensorExpr) : UTest.t :=
  UTest.value_eqv_pr
    (neg_rel tensorexpr_semantically_equal)
    (pr_tensorexpr) 
    "TensorExprs should be equal up to permutation and alpha-equivalence"
    exp
    test_val.

(* Values on which to test the functions *)

Ltac2 _tensorexpr_notation () :=
  [ 
    (Abstract "f" [("A", "a")] [("B", "b")], @f _[a : A]^[b : B]);
    (Product [Abstract "f" [("A", "a")] ["B", "b"]; Abstract "g" [] ["C", "c"]],
      (@f _[a : A]^[b : B] * @g _[]^[c : C]));
    (Product [(Sum ("A", "a") (Sum ("A", "a'") 
      (Abstract "f" [("A", "a")] ["A", "a'"])));
      Sum ("B", "b") (Abstract "g" [] ["B", "b"])],
      ((∑ a : A, ∑a' : A, @ f _[a : A]^[a' : A]) * 
        ∑b : B, @ g _[]^[b : B]));
    ((Sum ("A", "a") (Sum ("A", "a'") (Product [
      (Abstract "f" [("A", "a")] ["A", "a'"]);
      Sum ("B", "b") (Abstract "g" [] ["B", "b"])]))),
      ∑ a : A, ∑a' : A, @ f _[a : A]^[a' : A] * 
        ∑b : B, @ g _[]^[b : B])
  ].

Ltac2 _tensorlist_notation () := 
  [
    ({sums := [("A", "a"); ("A", "a'"); ("B", "b")];
      abstracts := [("f", [("A", "a")], [("B", "b")]);
        ("g", [], ["C", "c"]); ("h", ["D", "d"], [])]},
      !∑ a : A, a' : A, b : B; @ f _[a : A]^[b : B] * @ g _[]^[c : C] * 
        @h _[d : D]^[])
  ].

Ltac2 _alpha_equiv () := 
  [
    ((∑ a : A, @f _[]^[]), (∑ a' : A, @f _[]^[]));
    ((∑ a : A, @f _[a : A]^[]), (∑ a' : A, @f _[a' : A]^[]));
    ((∑ a : A, @f _[a : A]^[c : C]), (∑ a' : A, @f _[a' : A]^[c : C]));
    ((∑ a : A, ∑ b : B, @f _[a : A]^[] * @ g _[]^[b : B]),
     ∑ a : A, ∑ b' : B, @f _[a : A]^[] * @ g _[]^[b' : B]);
    ((∑ a : A, ∑ a : B, @f _[a : A]^[a : B]), 
     ∑ b : A, ∑ c : B, @f _[b : A]^[c : B]); (* TODO: Remove this if we make types irrelevant for names *)
    ((∑ a : A, ∑ a' : A, ∑ c : C, @f _[a : A, a' : A]^[c : C]),
     (∑ a' : A, ∑ a : A, ∑ c' : C, @f _[a' : A, a : A]^[c' : C]))
  ].

Ltac2 _non_alpha_equiv () := 
  [
    ((∑ a : A, @f _[]^[]), (∑ a' : B, @f _[]^[])); (* Types must match *)
    ((∑ a : A, @f _[a : A]^[a : A]), (∑ a' : A, @f _[a' : A]^[]));
    ((∑ a : A, @f _[a : A]^[c : C]), (∑ a' : A, @f _[a' : A]^[c' : C])); (* Free variables must match *)
    ((∑ a : A, ∑ b : B, @ g _[]^[b : B]) * @f _[a : A]^[],
     ∑ a : A, ∑ b' : B, @f _[a : A]^[] * @ g _[]^[b' : B]);
    ((∑ a : A, ∑ a : A, @f _[a : A]^[a : A]), 
     ∑ b : A, ∑ c : A, @f _[b : A]^[c : A]);
     ((∑ b : A, ∑ c : A, @f _[b : A]^[c : A]),
      (∑ a : A, ∑ a : A, @f _[a : A]^[a : A]))
  ].

Ltac2 _equal_to_from_tensorexprs () : (TensorExpr list) :=
  [
    (∑ a' : A, @f _[a' : A]^[c' : C]);
    (∑ a : A, ∑ b : B, @ g _[]^[b : B] * @f _[a : A]^[]);
    (∑ a : A, ∑ b' : B, @f _[a : A]^[] * @ g _[]^[b' : B])
  ].

Ltac2 _equal_to_from_tensorlists () : (TensorList list) :=
  [
    (!∑ a' : A; @f _[a' : A]^[c' : C]);
    (!∑ a : A, b : B; @ g _[]^[b : B] * @f _[a : A]^[]);
    (!∑ a : A, b' : B; @f _[a : A]^[] * @ g _[]^[b' : B])
  ].


Ltac2 _to_tensorlist_vals () : (TensorExpr* TensorList) list :=
  [
    (((∑ a : A, @f _[a : A]^[]) * (∑ a : A, @g _[a : A]^[])),
      !∑ a : A, a' : A; @f _[a : A]^[] * @g _[a' : A]^[])
  ].


Ltac2 _tensorlist_perm_eq () : (TensorList * TensorList) list :=
  [
    ((!∑ a : A, b : B, c : C; @f _[a : A, b : B]^[c : C]),
     (!∑ b : B, a : A, c : C; @f _[a : A, b : B]^[c : C]));
    ((!∑ a : A, b : B, c : C; @f _[a : A, b : B]^[c : C]),
     (!∑ b : B, c : C, a : A; @f _[a : A, b : B]^[c : C]));
    ((!∑ a : A, b : B, c : C; @f _[a : A, b : B]^[c : C] * @g _[]^[]),
     (!∑ b : B, c : C, a : A; @g _[]^[] * @f _[a : A, b : B]^[c : C]))
  ].


Ltac2 _tensorlist_not_perm_eq () : (TensorList * TensorList) list :=
  [
    ((!∑ a : A, b : B, c : C; @f _[a : A, b : B]^[c : C]),
     (!∑ b : B, a : A, c' : C; @f _[a : A, b : B]^[c' : C]));
    ((!∑ a : A, b : B, c : C; @f _[a : A, b : B]^[c : C]),
     (!∑ b : B, c : C, a : A; @f _[a : A, b : B]^[c : C] * @g _[]^[]));
    ((!∑ a : A, b : B, c : C; @f _[a : A, b : B]^[c : C] * @g _[]^[c : C]),
     (!∑ b : B, c : C, a : A; @g _[]^[] * @f _[a : A, b : B]^[c : C]))
  ].

Ltac2 _tensorlist_alpha_perm_eq () : (TensorList * TensorList) list :=
  List.append (_tensorlist_perm_eq()) [
    ((!∑ a : A, b : B, c : C; @f _[a : A, b : B]^[c : C]),
     (!∑ b : B, a : A, c' : C; @f _[a : A, b : B]^[c' : C]));
    ((!∑ a : A, a' : A, c : C; @f _[a : A, a' : A]^[c : C]),
     (!∑ a' : A, a : A, c' : C; @f _[a' : A, a : A]^[c' : C]));
    ((!∑ a : A, a' : A, c : C; @f _[a : A, a' : A]^[c : C]),
     (!∑ a : A, a' : A, c : C; @f _[a' : A, a : A]^[c : C]))
  ].

Ltac2 _tensorlist_not_alpha_perm_eq () : (TensorList * TensorList) list :=
  [
    ((!∑ a : A, b : B, c : C; @f _[a : A, b : B]^[c : C]),
     (!∑ b : B, c : C, a : A; @f _[a : A, b : B]^[c : C] * @g _[]^[]));
    ((!∑ a : A, b : B, c : C; @f _[a : A, b : B]^[c : C] * @g _[]^[c : C]),
     (!∑ b : B, c : C, a : A; @g _[]^[] * @f _[a : A, b : B]^[c : C]))
  ].

Local Ltac2 _on_both (f : 'a -> 'b) : 'a * 'a -> 'b * 'b :=
  fun (a, a') => (f a, f a').

Ltac2 _tensorexpr_sem_eq () : (TensorExpr * TensorExpr) list :=
  List.append (
    List.append 
      (List.map (_on_both tensorexpr_of_tensorlist)
        (_tensorlist_alpha_perm_eq())) 
      (_alpha_equiv())) [
    ((∑ a : A, ∑ b : B, @f _[a : A]^[b : B] * ∑ c : C, @g _[a : A]^[b : B, c : C]),
     (∑ c : C, ∑ b' : B, ∑ a : A, @g _[a : A]^[b' : B, c : C] * @f _[a : A]^[b' : B]));
    ((∑ a : A, ∑ b : B, @f _[a : A]^[b : B] * ∑ c : C, @g _[a : A]^[c : C]),
     (∑ c : C, ∑ a : A, @g _[a : A]^[c : C] * ∑ b' : B, @f _[a : A]^[b' : B]))
  ].

Ltac2 _tensorexpr_not_sem_eq () : (TensorExpr * TensorExpr) list :=
  List.append (
    (List.map (_on_both tensorexpr_of_tensorlist)
        (_tensorlist_not_alpha_perm_eq())) 
  ) [
    ((∑ a : A, ∑ b : B, @f _[]^[]), (∑ a : A, @f _[]^[]));
    ((∑ a : A, ∑ b : B, @f _[a : A]^[b : B]), (∑ a : A, @f _[a : A]^[b : B]));
    ((∑ a : A, ∑ b : B, @f _[a : A]^[b : B]), 
     (∑ a : A, ∑ b : B, @f _[b : B]^[a : A]));
    ((∑ a : A, @f _[a : A]^[b : A]), 
     (∑ a : A, @f _[b : A]^[a : A]));
    ((∑ a : A, ∑ b : B, @f _[a : A]^[b : B] * ∑ c : C, @g _[a : A]^[c : C]),
     (∑ c : C, ∑ a : A, @g _[a : A]^[b' : B, c : C] * ∑ b' : B, @f _[a : A]^[b' : B]))
  ].



Ltac2 test_tensorexpr_notation () : UTest.t :=
  UTest.foreach (_tensorexpr_notation()) 
    (uncurry test_tensorexpr_notation_value).

Ltac2 test_tensorlist_notation () : UTest.t :=
  UTest.foreach (_tensorlist_notation()) 
    (uncurry test_tensorlist_notation_value).

Ltac2 test_alpha_equivalent () : UTest.t :=
  UTest.foreach (_alpha_equiv()) 
    (uncurry (test_tensors_alpha_equiv "")).

Ltac2 test_non_alpha_equivalent () : UTest.t :=
  UTest.foreach (_non_alpha_equiv()) 
    (uncurry (test_tensors_non_alpha_equiv "")).

Ltac2 test_to_from_tensorlist () : UTest.t :=
  UTest.foreach (_equal_to_from_tensorexprs())
    (test_tensorexpr_eq_to_from_tensorlist).

Ltac2 test_to_from_tensorexpr () : UTest.t :=
  UTest.foreach (_equal_to_from_tensorlists())
    (test_tensorlist_eq_to_from_tensorexpr).

Ltac2 test_tensorexpr_to_tensorlist () : UTest.t :=
  UTest.foreach (_to_tensorlist_vals())
    (uncurry test_tensorexpr_to_tensorlist_val).

Ltac2 test_tensorlist_perm_eq () : UTest.t :=
  UTest.foreach (_tensorlist_perm_eq())
    (uncurry test_tensorlists_are_perm_eq).

Ltac2 test_tensorlist_alpha_perm_eq () : UTest.t :=
  UTest.foreach (_tensorlist_alpha_perm_eq())
    (uncurry test_tensorlists_are_alpha_perm_eq).

Ltac2 test_tensorexpr_sem_eq () : UTest.t :=
  UTest.foreach (_tensorexpr_sem_eq())
    (uncurry test_tensorexprs_are_sem_eq).

Ltac2 test_tensorlist_not_perm_eq () : UTest.t :=
  UTest.foreach (_tensorlist_not_perm_eq())
    (uncurry test_tensorlists_not_perm_eq).

Ltac2 test_tensorlist_not_alpha_perm_eq () : UTest.t :=
  UTest.foreach (_tensorlist_not_alpha_perm_eq())
    (uncurry test_tensorlists_not_alpha_perm_eq).

Ltac2 test_tensorexpr_not_sem_eq () : UTest.t :=
  UTest.foreach (_tensorexpr_not_sem_eq())
    (uncurry test_tensorexprs_not_sem_eq).

Ltac2 tests () := [
  ("TensorExpr notation", test_tensorexpr_notation);
  ("TensorList notation", test_tensorlist_notation);
  ("alpha_convertible", test_alpha_equivalent);
  ("not alpha_convertible", test_non_alpha_equivalent);
  ("to and from TensorList", test_to_from_tensorlist);
  ("to and from TensorExpr", test_to_from_tensorexpr);
  ("TensorExpr to TensorList", test_tensorexpr_to_tensorlist);
  ("TensorList eq up to perm", test_tensorlist_perm_eq);
  ("TensorList not eq up to perm", test_tensorlist_not_perm_eq);
  ("TensorList eq up to perm and alpha", test_tensorlist_alpha_perm_eq);
  ("TensorList not eq up to perm and alpha", test_tensorlist_not_alpha_perm_eq);
  ("TensorExpr eq up to semantic", test_tensorexpr_sem_eq);
  ("TensorExpr not eq up to semantic", test_tensorexpr_not_sem_eq)
].

(* Ltac2 Eval _on_both pr_tensorexpr (_on_both tensorexpr_of_tensorlist
  ((!∑ a : A, a' : A, c : C; @f _[a : A, a' : A]^[c : C]),
     (!∑ a' : A, a : A, c' : C; @f _[a' : A, a : A]^[c' : C]))).

Ltac2 Eval UTest.check test_tensorlist_alpha_perm_eq. *)

Ltac2 Eval 
  UTest.asserts UTest.noprint 
  (* UTest.checks *)
  (tests()).


(* Ltac2 Eval
  {sums := [("A", "a"); ("A", "a'"); ("B", "b")];
  abstracts := [("f", [("A", "a")],[]); ("g",[],[("B", "b")])]}.
Ltac2 Eval
  (!∑ a : A, a' : A, b : B; @ f _[a : A]^[] * @ g _[]^[b : B]).
 *)






End Testing.
