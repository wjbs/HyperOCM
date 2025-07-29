Require Ring_theory.
Require Integral_domain.
Require List.
Require Permutation.
Require SetoidList.
Require Import Ring.


(* The development is parametric over domain, which we require to be 
  a semiring. *)
Module Type SemiRing.

Parameter R : Type.

Parameter rO : R.
Parameter rI : R.
Parameter radd : R -> R -> R.
Parameter rmul : R -> R -> R.
Parameter req : R -> R -> Prop.

Parameter RSRth :
  Ring_theory.semi_ring_theory rO rI radd rmul req.

Import Relation_Definitions.

Parameter Req_ext : Ring_theory.sring_eq_ext radd rmul req.

Parameter Req_equiv : Setoid.Setoid_Theory R req.

End SemiRing.

Module SemiRingFacts (SR : SemiRing).

Import SR.


Import Setoid.

Add Parametric Relation : R req 
  reflexivity proved by ltac:(apply Req_equiv)
  symmetry proved by ltac:(apply Req_equiv)
  transitivity proved by ltac:(apply Req_equiv)
  as req_equiv.

Add Parametric Morphism : radd with signature
  req ==> req ==> req as radd_mor.
Proof. apply Req_ext. Qed.

Add Parametric Morphism : rmul with signature
  req ==> req ==> req as rmul_mor.
Proof. apply Req_ext. Qed.

Module SemiRingNotations.

Notation "0" := rO.
Notation "1" := rI.
Notation "x '==' y" := (req x y) (at level 70). 
Infix "+" := radd. 
Infix "*" := rmul.

End SemiRingNotations.

(* Include the basic facts about semirings, for convenience *)
Import SemiRingNotations Ring_theory.

Lemma radd_0_l r : 0 + r == r.
Proof. apply RSRth. Qed.

Lemma radd_comm r s : r + s == s + r.
Proof. apply RSRth. Qed.

Lemma radd_assoc r s t : r + (s + t) == (r + s) + t.
Proof. apply RSRth. Qed.

Lemma radd_0_r r : r + 0 == r.
Proof. rewrite radd_comm; apply radd_0_l. Qed.

Lemma rmul_1_l r : 1 * r == r.
Proof. apply RSRth. Qed. 

Lemma rmul_0_l r : 0 * r == 0.
Proof. apply RSRth. Qed. 

Lemma rmul_comm r s : r * s == s * r.
Proof. apply RSRth. Qed.

Lemma rmul_assoc r s t : r * (s * t) == (r * s) * t.
Proof. apply RSRth. Qed.

Lemma distr_l r s t : (r + s) * t == r * t + s * t.
Proof. apply RSRth. Qed.

Lemma rmul_1_r r : r * 1 == r.
Proof. rewrite rmul_comm. apply RSRth. Qed. 

Lemma rmul_0_r r : r * 0 == 0.
Proof. rewrite rmul_comm. apply RSRth. Qed. 

Lemma distr_r r s t : r * (s + t) == r * s + r * t.
Proof. rewrite 3(rmul_comm r). apply distr_l. Qed. 

Add Ring R : RSRth
  (setoid Req_equiv Req_ext).

End SemiRingFacts.

(* A typeclass indicating a type can be summed over, hence
  used in tensor expressions. Note that this is in fact just 
  expressing that there are some distinguished elements of the 
  type. It is expected that the types used are finite and that 
  these lists of elements are complete, but this is not enforced 
  as it is not needed for proofs. So, if desirable, infinite types 
  can be used, though only finitely many values will be used. 
  
  The motivation for this definition is that it means multiple
  instances automatically commute with each other, which is not
  enforcable if the summation function is abstract. (In that case,
  a separate compatability typeclass would be required, which would
  make summations over lists of registers highly impractical and
  balloon proof requirements.) *)
Class Summable (A : Type) := {
  sum_elements : list A
}.

(* For a given semiring, the theory of summation and tensor expressions *)
Module Summation (SR : SemiRing).

Import Setoid.

Export SR.
Module SRF := SemiRingFacts SR.
Export SRF.
Import SRF.SemiRingNotations.


Generalizable Variables A B C D.

(* The sum of a function over a summable domain [A] *)
Definition sum_of `{Summable A} (f : A -> R) : R :=
  List.fold_right radd 0 (List.map f sum_elements).

Global Arguments sum_of {_ _} (_)%_function_scope : assert.

(* Lemma to unfold [sum_of]. Should not be to reason about 
  tensor expressions directly, only to reason about their 
  definition, such as in relation to other libraries. *)
Lemma sum_of_defn `{Summable A} (f : A -> R) : 
  sum_of f = List.fold_right radd 0 (List.map f sum_elements).
Proof. reflexivity. Qed.

(* We want to prevent [sum_of] ever being evaluated, as this 
  would be catastrophic in many concrete cases (for example,
  [Vector.t bool 10] has [sum_elements] with length [2^10]). *)
Global Opaque sum_of.

(* Replaces [sum_of] with its definition in all hypotheses and goals *)
Ltac unfold_sum_of :=
  rewrite_strat (bottomup sum_of_defn).

(* Generalizes [sum_elements], introducing the generalized list
  with identifier [l] *)
Ltac gen_sum_elem l :=
  match goal with 
  |- context [@sum_elements ?A ?SA] => 
    generalize (@sum_elements A SA);
    intros l
  end.

(* Replaces [sum_of] with its definition in all hypotheses and goals
  and generalizes [sum_elements], introducing the generalized list
  with identifier [l] *)
Ltac gen_sum_of l :=
  try unfold_sum_of;
  gen_sum_elem l.

(* Tries to solve a goal about [sum_of] by repeatedly unfolding 
  [sum_of], generalizing [sum_elements], and inducting on the 
  resulting goals. Solves goals with [basetac], or 
  [indtac IHl] in the inductive case *)
Ltac solve_sum_of basetac indtac :=
  let l := fresh "l" in 
  let IHl := fresh "IHl" in 
  gen_sum_of l;
  induction l as [|? l IHl]; 
  [basetac | indtac IHl].

(* Tries to solve a goal about [sum_of] by repeatedly unfolding 
  [sum_of], generalizing [sum_elements], and inducting on the 
  resulting goals. Solves goals with [simpl; ring], or 
  [simpl; ring [IHl]] in the inductive case *)
Ltac solve_sum_of_ring :=
  solve_sum_of ltac:(simpl; ring) ltac:(fun IHl => simpl; ring [IHl]).

(* We have a specific notation for a sum over a single register, so 
  that sums over many registers can look better. *)
Notation " '∑'' x ':' T ',' f " :=
  (@sum_of T _ (fun x => f)) 
  (at level 60, 
  x name, T at level 200, f at level 69,
  right associativity).

Notation " '∑'' x ',' f " :=
  (∑' x : _, f) 
  (at level 60, 
  x name, f at level 69,
  right associativity, 
  only parsing).

Lemma sum_of_ext_gen `{Summable A} (f g : A -> R) 
  (eqR : relation R) : Reflexive eqR ->
  Morphisms.Proper (eqR ==> eqR ==> eqR) radd ->
  (forall x, eqR (f x) (g x)) ->
  eqR (∑' x, f x) (∑' x, g x).
Proof.
  intros Heq Hadd Hfg.
  gen_sum_of l.
  induction l; [reflexivity|].
  simpl.
  apply Hadd.
  - apply Hfg.
  - apply IHl.
Qed.

Lemma sum_of_ext `{Summable A} (f g : A -> R) :
  (forall x, f x == g x) ->
  ∑' x, f x == ∑' x, g x.
Proof.
  apply sum_of_ext_gen; apply _.
Qed.

Lemma sum_of_ext_eq `{Summable A} (f g : A -> R) : 
  (forall x, f x = g x) ->
  ∑' x, f x = ∑' x, g x.
Proof.
  apply sum_of_ext_gen; apply _.
Qed.

Add Parametric Morphism {A} {SA : Summable A} : (@sum_of A SA) 
  with signature Morphisms.pointwise_relation A req ==> req as
  sum_of_mor.
Proof.
  apply sum_of_ext.
Qed.

Add Parametric Morphism {A} {SA : Summable A} : (@sum_of A SA) 
  with signature Morphisms.pointwise_relation A eq ==> eq as
  sum_of_mor_eq.
Proof.
  apply sum_of_ext_eq.
Qed.

Lemma sum_of_0 `{Summable A} : 
  ∑' _ : A, 0 == 0.
Proof.
  solve_sum_of_ring.
Qed.

Lemma sum_of_add `{Summable A} (f g : A -> R) : 
  ∑' x, f x + g x == (∑' x, f x) + (∑' x, g x).
Proof.
  solve_sum_of_ring.
Qed.

Lemma sum_of_distr_l `{Summable A} (f : A -> R) r: 
  (∑' x, f x) * r == ∑' x, f x * r.
Proof.
  solve_sum_of_ring.
Qed.

Lemma sum_of_distr_r `{Summable A} (f : A -> R) (r : R) : 
  r * (∑' x, f x) == ∑' x, r * f x.
Proof.
  solve_sum_of_ring.
Qed.

Lemma sum_of_comm `{Summable A, Summable B} (f : A -> B -> R) : 
  ∑' x, ∑' y, f x y == ∑' y, ∑' x, f x y.
Proof.
  rewrite_strat (bottomup (terms (@sum_of_defn B))).
  gen_sum_elem lB.
  induction lB.
  - apply sum_of_0.
  - simpl.
    rewrite sum_of_add.
    rewrite IHlB.
    reflexivity.
Qed.

Local Notation SummableType := (sigT Summable).

Import List.ListNotations.


Inductive SummableTy (B : Type) : Type -> Type :=
  | STnil : SummableTy B B
  | STcons (A : Type) (SA : Summable A) 
    {T : Type} : 
    SummableTy B T -> 
    SummableTy B (A -> T).


Existing Class SummableTy.
#[global] Hint Constructors SummableTy : typeclass_instances.

Global Arguments STnil {B}.
Global Arguments STcons {B} A SA {T} HT.

Fixpoint sum_summable_aux {fT} (Pf : SummableTy R fT) : fT -> R :=
  match Pf with 
  | STnil => fun r => r
  | STcons A SA Pf => fun f => 
    @sum_of A SA (fun r => sum_summable_aux Pf (f r))
  end.

(* Make sure sum_summable_aux simplifies in the proper circumstances *)
Global Arguments sum_summable_aux {_} !_ _ /.

Definition sum_summable {fT} (Pf : SummableTy R fT) : fT -> R :=
  sum_summable_aux Pf.

Lemma sum_summable_defn {fT} (Pf : SummableTy R fT) (f : fT) : 
  sum_summable Pf f = sum_summable_aux Pf f.
Proof. reflexivity. Qed.

(* Ensure [sum_summable] does not simplify *)
Global Opaque sum_summable.

Notation 
  "∑ x .. y , f" :=
  (sum_summable _ (fun x => .. (fun y => f) ..))
  (at level 60, 
  x binder, y binder, f at level 69,
  right associativity).

Lemma sum_one `{Summable A} f : 
  ∑ x : A, f x = ∑' x, f x.
Proof. 
  reflexivity.
Qed.

Lemma sum_none f : 
  sum_summable (STnil) f = f.
Proof. 
  reflexivity.
Qed.

Lemma sum_cons `{SA : Summable A} {fT} (Pf : SummableTy R fT) f : 
  sum_summable (STcons A SA Pf) f = 
  ∑' x, sum_summable Pf (f x).
Proof.
  reflexivity.
Qed.

Add Parametric Morphism `{SA : Summable A} {fT} 
  (Pf : SummableTy R fT) : (sum_summable 
  (STcons A SA Pf)) with signature
  Morphisms.pointwise_relation A eq ==> eq as 
  sum_summable_cons_mor.
Proof.
  intros f g Hfg.
  rewrite 2!sum_cons.
  apply sum_of_ext_eq.
  intros x.
  rewrite Hfg.
  reflexivity.
Qed.

Lemma sum_comm_head `{SA : Summable A} `{SB : Summable B} {fT}
  (Pf : SummableTy R fT) f : 
  sum_summable (STcons A SA 
    (STcons B SB Pf)) f ==
  sum_summable (STcons B SB
    (STcons A SA Pf))
    (fun b a => f a b).
Proof.
  rewrite_strat (bottomup sum_cons).
  apply sum_of_comm.
Qed.

Local Open Scope list_scope.


Inductive STPerm {C : Type} : forall {fT fT'}, 
  SummableTy C fT -> SummableTy C fT' -> Type :=
  | stperm_nil: STPerm STnil STnil
  | stperm_skip A SA {T T'} (ST : SummableTy C T) (ST' : SummableTy C T') : 
    STPerm ST ST' -> STPerm (STcons A SA ST) (STcons A SA ST')
  | stperm_swap A SA B SB {T} (ST : SummableTy C T) : 
    STPerm (STcons B SB (STcons A SA ST)) (STcons A SA (STcons B SB ST))
  | stperm_trans {T T' T''} (ST : SummableTy C T) 
      (ST' : SummableTy C T') (ST'' : SummableTy C T'') :
      STPerm ST ST' -> STPerm ST' ST'' -> STPerm ST ST''.

Fixpoint stperm_refl {fT} `(ST : SummableTy B fT) : STPerm ST ST :=
  match ST with 
  | STnil => stperm_nil
  | STcons A SA ST => stperm_skip A SA _ _ (stperm_refl ST)
  end.

Fixpoint stperm_symm {fT fT'} `(ST : SummableTy B fT) (ST' : SummableTy B fT') 
  (P : STPerm ST ST') : STPerm ST' ST :=
  match P with 
  | stperm_nil => stperm_nil
  | stperm_skip A SA ST ST' P' => stperm_skip A SA ST' ST (stperm_symm _ _ P')
  | stperm_swap A SA B SB ST => stperm_swap B SB A SA ST
  | stperm_trans ST ST' ST'' P P' => 
    stperm_trans ST'' ST' ST (stperm_symm _ _ P') (stperm_symm _ _ P)
  end.

Fixpoint perm_args_of_STPerm {fT fT'} 
  `{SfT : SummableTy B fT} {SfT' : SummableTy B fT'}
  (P : STPerm SfT SfT') : fT -> fT' :=
  match P with 
  | stperm_nil => fun r => r
  | stperm_skip A SA ST ST' P' => 
    fun f => fun a => perm_args_of_STPerm P' (f a)
  | stperm_swap A SA B SB ST => 
    fun f => fun a b => f b a
  | stperm_trans ST ST' ST'' P P' => 
    fun f => perm_args_of_STPerm P' (perm_args_of_STPerm P f)
  end.


Lemma sum_STPerm {fT fT'} (SfT : SummableTy R fT) (SfT' : SummableTy R fT') 
  (P : STPerm SfT SfT') (f : fT) : 
  sum_summable SfT' (perm_args_of_STPerm P f) ==
  sum_summable SfT f.
Proof.
  induction P.
  - reflexivity.
  - simpl.
    rewrite 2!sum_cons.
    setoid_rewrite IHP.
    reflexivity.
  - simpl.
    rewrite_strat (bottomup sum_cons).
    apply sum_of_comm.
  - simpl.
    rewrite <- IHP1, IHP2.
    reflexivity.
Qed.

Lemma sum_STPerm' {fT fT'} (SfT : SummableTy R fT) (SfT' : SummableTy R fT') 
  (P : STPerm SfT SfT') (f : fT) : 
  sum_summable SfT f == 
  sum_summable SfT' (perm_args_of_STPerm P f).
Proof.
  now rewrite sum_STPerm.
Qed.

Fixpoint swap_summablety_nth {C} (n : nat) : forall {fT}, SummableTy C fT -> 
  {fT' & SummableTy C fT'} :=
  match n with 
  | 0 => fun fT SfT => 
    match SfT with 
    | STcons A SA (@STcons _ B SB fT' SfT') =>
      existT _ (B -> A -> fT') 
        (STcons B SB (STcons A SA SfT'))
    | _ => existT _ fT SfT
    end
  | S n' => fun fT SfT => 
    match SfT with 
    | STcons A SA SfT' =>
      let SfT'' := swap_summablety_nth n' SfT' in 
      existT _ (A -> projT1 SfT'')
        (STcons A SA (projT2 SfT''))
    | STnil => existT _ C STnil
    end
  end.

Notation swap_type_nth n ST := (projT1 (swap_summablety_nth n ST)).
Notation swap_summable_nth n ST := (projT2 (swap_summablety_nth n ST)).


Fixpoint swap_summable_nth_STPerm {C} (n : nat) : 
  forall {fT} (SfT : SummableTy C fT), 
  STPerm SfT (swap_summable_nth n SfT) :=
  match n with 
  | 0 => fun fT SfT =>
    match SfT (* as ST' in SummableTy T return 
      @STPerm T (swap_type_nth 0 ST') ST' (swap_summable_nth 0 ST') *) with
    | STcons A SA SfT' => 
      match SfT' (* as ST' in SummableTy T return 
      @STPerm (A -> T) (swap_type_nth 0 (STcons A SA ST')) 
        (STcons A SA ST') (swap_summable_nth 0 (STcons A SA ST')) *) with 
      | STcons B SB SfT' => stperm_swap B SB A SA SfT'
      | STnil => stperm_refl (STcons A SA STnil)
      end
    | STnil => stperm_refl (STnil)
    end
  | S n' => fun fT SfT =>
    match SfT (* as ST' return STPerm ST' (swap_summable_nth (S n') ST') *) with 
    | STcons A SA SfT' =>
      stperm_skip A SA _ _
        (swap_summable_nth_STPerm n' SfT')
    | STnil => stperm_refl _
    end
  end.

Fixpoint swap_summablety_nths {C} (l : list nat) {fT} (ST : SummableTy C fT) : 
  {fT' & SummableTy C fT'} :=
  match l with 
  | [] => existT _ fT ST
  | n :: l' => 
    swap_summablety_nths l' (swap_summable_nth n ST)
  end.

Notation swap_type_nths l ST := (projT1 (swap_summablety_nths l ST)).
Notation swap_summable_nths l ST := (projT2 (swap_summablety_nths l ST)).

Fixpoint swap_summablety_nths_STPerm {C} (l : list nat) 
  {fT} (ST : SummableTy C fT) :
  STPerm ST (swap_summable_nths l ST) :=
  match l with 
  | [] => stperm_refl _
  | n :: l' => 
    stperm_trans _ _ _ 
      (swap_summable_nth_STPerm n ST)
      (swap_summablety_nths_STPerm l' (swap_summable_nth n ST))
  end.





Fixpoint insert_summablety_after_nth {C} (n : nat) 
  {A} (SA : Summable A) : forall {fT}, SummableTy C fT -> 
  {fT' & SummableTy C fT'} :=
  match n with
  | 0 => fun fT SfT => existT _ (A -> fT) (STcons A SA SfT)
  | S n' => 
    fun fT SfT => 
    match SfT with 
    | STnil => existT _ (A -> C) (STcons A SA STnil)
    | STcons B SB SfT' => 
      existT _ _ 
      (STcons B SB (projT2 (insert_summablety_after_nth n' SA SfT')))
    end
  end.

Notation insert_type_after_nth n SA ST :=
  (projT1 (insert_summablety_after_nth n SA ST)).
Notation insert_summable_after_nth n SA ST :=
  (projT2 (insert_summablety_after_nth n SA ST)).


Fixpoint insert_summable_after_nth_STPerm {C} (n : nat) 
  {A} (SA : Summable A) : forall {fT} (SfT : SummableTy C fT),
  STPerm (STcons A SA SfT) (insert_summable_after_nth n SA SfT) :=
  match n with
  | 0 => fun fT SfT => stperm_refl _
  | S n' => 
    fun fT SfT => 
    match SfT with 
    | STnil => stperm_refl _
    | STcons B SB SfT' => 
      stperm_trans _ _ _ 
        (stperm_swap B SB A SA SfT')
        (stperm_skip B SB _ _ (insert_summable_after_nth_STPerm n' SA SfT'))
    end
  end.

Definition swap_summablety_with_nth {C} (n : nat) 
  {fT} (SfT : SummableTy C fT) : 
  {fT' & SummableTy C fT'} :=
  match SfT with 
  | STnil => existT _ fT SfT
  | STcons A SA SfT' => insert_summablety_after_nth n SA SfT'
  end.

Notation swap_type_with_nth n ST := (projT1 (swap_summablety_with_nth n ST)).
Notation swap_summable_with_nth n ST := (projT2 (swap_summablety_with_nth n ST)).

Definition swap_summable_with_nth_STPerm {C} (n : nat) 
  {fT} (SfT : SummableTy C fT) : 
  STPerm SfT (swap_summable_with_nth n SfT) :=
  match SfT as SfT return STPerm SfT (swap_summable_with_nth n SfT) with 
  | STnil => stperm_refl _
  | STcons A SA SfT' => insert_summable_after_nth_STPerm n SA SfT'
  end.


Fixpoint extraction_sort_summablety {C} (l : list nat) : 
  forall {fT} (SfT : SummableTy C fT), 
  {fT' & SummableTy C fT'} :=
  match l with 
  | [] => fun fT SfT => existT _ fT SfT
  | n :: l' => 
    fun fT SfT =>
    match swap_summable_with_nth n SfT with 
    | STnil => existT _ _ STnil
    | STcons A SA SfT' => 
      existT _ _ (STcons A SA (projT2 (extraction_sort_summablety l' SfT')))
    end
  end.

Notation extraction_sort_type l ST := 
  (projT1 (extraction_sort_summablety l ST)).
Notation extraction_sort_summable l ST := 
  (projT2 (extraction_sort_summablety l ST)).

Fixpoint extraction_sort_summable_STPerm {C} (l : list nat) : 
  forall {fT} (SfT : SummableTy C fT), 
  STPerm SfT (extraction_sort_summable l SfT) :=
  match l with 
  | [] => fun fT SfT => stperm_refl _ 
  | n :: l' => 
    fun fT SfT =>
    stperm_trans SfT (swap_summable_with_nth n SfT)
        (extraction_sort_summable (n :: l') SfT)
      (swap_summable_with_nth_STPerm n SfT)
      (match swap_summable_with_nth n SfT as x in (SummableTy _ T)
        return (STPerm x (projT2
          match x with
          | STnil => existT (SummableTy C) _ _
          | STcons _ _ _ => existT (SummableTy C) _ _
          end)) with 
      | STnil => stperm_refl STnil
      | STcons A SA SfT' =>
        stperm_skip A SA SfT' (extraction_sort_summable l' SfT')
          (extraction_sort_summable_STPerm l' SfT')
      end)
end.



Fixpoint swap_summablety_with_nth_after {C} (n : nat) (d : nat) : 
  forall {fT}, SummableTy C fT -> 
  {fT' & SummableTy C fT'} :=
  match d with 
  | 0 => fun fT => swap_summablety_with_nth n
  | S d' => 
    fun fT SfT => 
    match SfT with 
    | STcons A SA SfT' =>
      let SfT'' := swap_summablety_with_nth_after n d' SfT' in 
      existT _ (A -> projT1 SfT'')
        (STcons A SA (projT2 SfT''))
    | STnil => existT _ C STnil
    end
  end.

Notation swap_type_with_nth_after n d ST := 
  (projT1 (swap_summablety_with_nth_after n d ST)).
Notation swap_summable_with_nth_after n d ST := 
  (projT2 (swap_summablety_with_nth_after n d ST)).

Fixpoint swap_summable_with_nth_after_STPerm {C} n d : forall
  {fT} (SfT : SummableTy C fT),
  STPerm SfT (swap_summable_with_nth_after n d SfT) :=
  match d (* as d return forall
  {fT} (SfT : SummableTy C fT),
  STPerm SfT (swap_summable_nth_after n d SfT) *) with 
  | 0 => fun fT SfT => swap_summable_with_nth_STPerm n SfT
  | S d' => 
    fun fT SfT => 
    match SfT (* as SfT return 
      STPerm SfT (swap_summable_nth_after n (S d') SfT) *) with 
    | STcons A SA SfT' =>
      stperm_skip A SA _ _ (swap_summable_with_nth_after_STPerm n d' SfT')
    | STnil => stperm_nil
    end
  end.

Fixpoint swap_summablety_with_nths_after {C} (l : list (nat * nat)) 
  {fT} (ST : SummableTy C fT) : 
  {fT' & SummableTy C fT'} :=
  match l with 
  | [] => existT _ fT ST
  | (n, d) :: l' => 
    swap_summablety_with_nths_after l' (swap_summable_with_nth_after n d ST)
  end.

Notation swap_type_with_nths_after l ST := 
  (projT1 (swap_summablety_with_nths_after l ST)).
Notation swap_summable_with_nths_after l ST := 
  (projT2 (swap_summablety_with_nths_after l ST)).

Fixpoint swap_summable_with_nths_after_STPerm {C} (l : list (nat * nat)) 
  {fT} (ST : SummableTy C fT) :
  STPerm ST (swap_summable_with_nths_after l ST) :=
  match l with 
  | [] => stperm_refl _
  | (n, d) :: l' => 
    stperm_trans _ _ _ 
      (swap_summable_with_nth_after_STPerm n d ST)
      (swap_summable_with_nths_after_STPerm l' 
      (swap_summable_with_nth_after n d ST))
  end.






Fixpoint swap_summablety_nth_after {C} (n : nat) (d : nat) : 
  forall {fT}, SummableTy C fT -> 
  {fT' & SummableTy C fT'} :=
  match d with 
  | 0 => fun fT => swap_summablety_nth n
  | S d' => 
    fun fT SfT => 
    match SfT with 
    | STcons A SA SfT' =>
      let SfT'' := swap_summablety_nth_after n d' SfT' in 
      existT _ (A -> projT1 SfT'')
        (STcons A SA (projT2 SfT''))
    | STnil => existT _ C STnil
    end
  end.

Notation swap_type_nth_after n d ST := 
  (projT1 (swap_summablety_nth_after n d ST)).
Notation swap_summable_nth_after n d ST := 
  (projT2 (swap_summablety_nth_after n d ST)).

Fixpoint swap_summable_nth_after_STPerm {C} n d : forall
  {fT} (SfT : SummableTy C fT),
  STPerm SfT (swap_summable_nth_after n d SfT) :=
  match d (* as d return forall
  {fT} (SfT : SummableTy C fT),
  STPerm SfT (swap_summable_nth_after n d SfT) *) with 
  | 0 => fun fT SfT => swap_summable_nth_STPerm n SfT
  | S d' => 
    fun fT SfT => 
    match SfT (* as SfT return 
      STPerm SfT (swap_summable_nth_after n (S d') SfT) *) with 
    | STcons A SA SfT' =>
      stperm_skip A SA _ _ (swap_summable_nth_after_STPerm n d' SfT')
    | STnil => stperm_nil
    end
  end.

Fixpoint swap_summablety_nths_after {C} (l : list (nat * nat)) 
  {fT} (ST : SummableTy C fT) : 
  {fT' & SummableTy C fT'} :=
  match l with 
  | [] => existT _ fT ST
  | (n, d) :: l' => 
    swap_summablety_nths_after l' (swap_summable_nth_after n d ST)
  end.

Notation swap_type_nths_after l ST := 
  (projT1 (swap_summablety_nths_after l ST)).
Notation swap_summable_nths_after l ST := 
  (projT2 (swap_summablety_nths_after l ST)).

Fixpoint swap_summablety_nths_after_STPerm {C} (l : list (nat * nat)) 
  {fT} (ST : SummableTy C fT) :
  STPerm ST (swap_summable_nths_after l ST) :=
  match l with 
  | [] => stperm_refl _
  | (n, d) :: l' => 
    stperm_trans _ _ _ 
      (swap_summable_nth_after_STPerm n d ST)
      (swap_summablety_nths_after_STPerm l' (swap_summable_nth_after n d ST))
  end.






Fixpoint summable_pointwise_relation {C} (RC : relation C) 
  {fT} (ST : SummableTy C fT) : 
  relation fT :=
  match ST with 
  | STnil => RC
  | STcons A _ ST' => 
    Morphisms.pointwise_relation A (summable_pointwise_relation RC ST')
  end.

Lemma summable_pointwise_relation_Reflexive
  `(RC : relation C) {fT} (ST : SummableTy C fT) : Reflexive RC ->
  Reflexive (summable_pointwise_relation RC ST).
Proof.
  induction ST; apply _.
Qed.

Lemma summable_pointwise_relation_Symmetric
  `(RC : relation C) {fT} (ST : SummableTy C fT) : Symmetric RC ->
  Symmetric (summable_pointwise_relation RC ST).
Proof.
  induction ST; apply _.
Qed.

Lemma summable_pointwise_relation_Transitive
  `(RC : relation C) {fT} (ST : SummableTy C fT) : Transitive RC ->
  Transitive (summable_pointwise_relation RC ST).
Proof.
  induction ST; apply _.
Qed.

#[export] Instance summable_pointwise_relation_Equivlance 
  `(RC : relation C) {fT} (ST : SummableTy C fT) : Equivalence RC ->
  Equivalence (summable_pointwise_relation RC ST).
Proof.
  induction ST; apply _.
Qed.

#[export] Instance subrelation_summable_pointwise_relation 
  `{RC : relation C} (HRC : Reflexive RC)
  `{SA : Summable A} {fT} {ST : SummableTy C fT} : 
  subrelation (Morphisms.pointwise_relation A eq)
    (summable_pointwise_relation RC (STcons A SA ST)).
Proof.
  intros f g Heq.
  simpl.
  intros a.
  rewrite Heq.
  apply summable_pointwise_relation_Reflexive, HRC.
Qed.

Add Parametric Morphism {fT} {ST : SummableTy R fT} : (sum_summable ST) 
  with signature summable_pointwise_relation req ST ==> req as sum_summable_mor.
Proof.
  induction ST.
  - simpl; easy.
  - simpl.
    intros f g Hfg.
    rewrite 2!sum_cons.
    apply sum_of_ext.
    intros a.
    apply IHST.
    apply Hfg.
Qed.


(* Split a summable type into an initial and terminal segment *)
Fixpoint split_summablety_after {C} (n : nat) {fT} (ST : SummableTy C fT) :
  { gT_fT : Type * Type & 
    (SummableTy (snd gT_fT) (fst gT_fT) * SummableTy C (snd gT_fT))%type} :=
  match n with 
  | 0 => existT _ (fT, fT) (STnil, ST)
  | S n' => 
    match ST (* in SummableTy _ fT 
      return { gT_fT : Type * Type & 
    (SummableTy (snd gT_fT) (fst gT_fT) * SummableTy C (snd gT_fT))%type} *) with 
    | @STnil _ => existT _ (_, _) (STnil, STnil)
    | STcons A SA ST' => 
      let 'existT _ (gT, fT') (HSg, HSf) := split_summablety_after n' ST' in 
      existT _ (A -> gT, fT') (STcons A SA HSg, HSf)
    end
  end.

Notation split_summable_ty1 n ST :=
  (fst (projT1 (split_summablety_after n ST))).
Notation split_summable_ty2 n ST :=
  (snd (projT1 (split_summablety_after n ST))).

Notation split_summable1 n ST :=
  (fst (projT2 (split_summablety_after n ST))).
Notation split_summable2 n ST :=
  (snd (projT2 (split_summablety_after n ST))).

(* Fixpoint split_sum_after {R} (n : nat) {fT} (ST : SummableTy R fT) : 
  fT -> 


Lemma  *)


Fixpoint summable_app {fT gT} 
  (ST : SummableTy fT gT) (ST' : SummableTy R fT) : 
  {fT' & SummableTy R fT'} :=
  match ST with 
  | STnil => 
    fun ST' => existT _ _ ST'
  | STcons A SA ST'' => 
    fun ST' => 
    existT _ _ (STcons A SA (projT2 (summable_app ST'' ST')))
  end ST'.






(* Corresponding results on lists to allow us to talk about products *)
(* TODO: Extend to trees (via permutations of their underlying lists)
  to avoid having to pre-associate *)

Import Permutation.

Import SetoidList.

Local Instance fold_left_mor f 
  (HProp : Morphisms.Proper (req ==> req ==> req) f) : 
  Morphisms.Proper (eqlistA req ==> req ==> req) (List.fold_left f).
Proof.
  intros l l' Hl.
  induction Hl; intros a a' Ha.
  - simpl.
    auto.
  - simpl.
    apply IHHl.
    apply HProp; auto.
Qed.

Lemma fold_left_to_unit {C} {ceq} `{Equivalence C ceq} 
  (cunit : C) (f : C -> C -> C)
  (Hlunit : forall x, ceq (f cunit x) x)
  (Hrunit : forall x, ceq (f x cunit) x)
  (Hassoc : forall x y z, ceq (f (f x y) z) (f x (f y z)))
  (HProp : Morphisms.Proper (ceq ==> ceq ==> ceq) f) l c : 
  ceq (fold_left f l c) (f c (fold_left f l cunit)).
Proof.
  revert c;
  induction l;
  intros c.
  - simpl.
    rewrite Hrunit.
    reflexivity.
  - simpl.
    rewrite 2!(IHl (f _ _)).
    rewrite Hlunit.
    rewrite Hassoc.
    reflexivity.
Qed.

Lemma fold_left_app_assoc {C} {ceq : relation C} `{Equivalence C ceq} 
  (cunit : C) (f : C -> C -> C)  
  (Hlunit : forall x, ceq (f cunit x) x)
  (Hrunit : forall x, ceq (f x cunit) x)
  (Hassoc : forall x y z, ceq (f (f x y) z) (f x (f y z)))
  (HProp : Morphisms.Proper (ceq ==> ceq ==> ceq) f) l l' c : 
  ceq (fold_left f (l ++ l') c) 
    (f (fold_left f l c) (fold_left f l' cunit)).
Proof.
  rewrite fold_left_app. 
  rewrite fold_left_to_unit by eassumption.
  reflexivity.
Qed.


(* An optimized left-associated list product which has no [1] term 
  unless the list is empty. *)
Definition list_prod (l : list R) : R :=
  match l with 
  | [] => rI
  | a :: l' => List.fold_left rmul l' a
  end.

Lemma list_prod_eq l : list_prod l == List.fold_left rmul l rI.
Proof.
  destruct l; [reflexivity|].
  simpl.
  now rewrite rmul_1_l.
Qed.

Lemma fold_left_product_perm_eq {l l' : list R} (Hl : Permutation l l') a : 
  List.fold_left rmul l a == List.fold_left rmul l' a.
Proof.
  revert a; induction Hl; intros a.
  - reflexivity.
  - simpl.
    auto.
  - simpl.
    rewrite <- 2!rmul_assoc, (rmul_comm y x).
    reflexivity.
  - rewrite IHHl1; apply IHHl2.
Qed.

Lemma product_perm_eq {l l' : list R} (Hl : Permutation l l') : 
  list_prod l == list_prod l'.
Proof.
  rewrite 2!list_prod_eq.
  now apply fold_left_product_perm_eq.
Qed.

Fixpoint insert_list_after_nth {C} (n : nat) (c : C) (l : list C) : list C :=
  match n with 
  | 0 => c :: l
  | S n' => 
    match l with 
    | [] => [c]
    | a :: l' => 
      a :: (insert_list_after_nth n' c l')
    end
  end.


Definition swap_list_with_nth {C} (n : nat) (l : list C) : list C :=
  match l with
  | [] => []
  | a :: l' => insert_list_after_nth n a l'
  end.

Fixpoint swap_list_with_nth_after {C} (n : nat) (d : nat) (l : list C) : list C :=
  match d with
  | 0 => swap_list_with_nth n l
  | S d' => 
    match l with
    | [] => []
    | a :: l' => a :: (swap_list_with_nth_after n d' l')
    end
  end.

Fixpoint swap_list_with_nths_after {C} (nds : list (nat * nat)) (l : list C) : list C :=
  match nds with 
  | [] => l
  | (n, d) :: nds' =>
    swap_list_with_nths_after nds' (swap_list_with_nth_after n d l)
  end.

Lemma insert_list_after_nth_perm {C} n c (l : list C) : 
  Permutation (c :: l) (insert_list_after_nth n c l).
Proof.
  revert c l;
  induction n; intros c l.
  - reflexivity.
  - destruct l; [reflexivity|]. 
    simpl.
    rewrite <- IHn.
    constructor.
Qed.

Lemma swap_list_with_nth_perm {C} n (l : list C) : 
  Permutation l (swap_list_with_nth n l).
Proof.
  destruct l; [reflexivity|].
  apply insert_list_after_nth_perm.
Qed.

Lemma swap_list_with_nth_after_perm {C} n d (l : list C) : 
  Permutation l (swap_list_with_nth_after n d l).
Proof.
  revert l;
  induction d;
  intros l; [apply swap_list_with_nth_perm|].
  destruct l; [reflexivity|].
  simpl.
  rewrite <- IHd.
  reflexivity.
Qed.

Lemma swap_list_with_nths_after_perm {C} nds (l : list C) : 
  Permutation l (swap_list_with_nths_after nds l).
Proof.
  revert l;
  induction nds as [|[n d]];
  intros l.
  - reflexivity.
  - simpl.
    rewrite <- IHnds.
    apply swap_list_with_nth_after_perm.
Qed.




Inductive termtree :=
  | termone : termtree
  | termconst (r : R) : termtree
  | termmul (l r : termtree) : termtree.

Fixpoint realize_termtree (t : termtree) : R :=
  match t with 
  | termone => rI
  | termconst r => r
  | termmul l r => rmul (realize_termtree l) (realize_termtree r)
  end.

Fixpoint list_of_termtree (t : termtree) : list R :=
  match t with 
  | termone => []
  | termconst r => [r]
  | termmul l r => list_of_termtree l ++ list_of_termtree r
  end.

Lemma realize_termtree_eq_list_prod_list_of_termtree (t : termtree) : 
  realize_termtree t == list_prod (list_of_termtree t).
Proof.
  rewrite list_prod_eq.
  induction t; [simpl; ring..|].
  simpl.
  rewrite (fold_left_app_assoc 1) by ((intros ? **; ring) || apply _).
  Morphisms.f_equiv; assumption.
Qed.

Lemma realize_termtree_eq_of_list_prod_perm (t t' : termtree) : 
  Permutation (list_of_termtree t) (list_of_termtree t') -> 
  realize_termtree t == realize_termtree t'.
Proof.
  intros Hperm.
  rewrite 2!realize_termtree_eq_list_prod_list_of_termtree.
  apply product_perm_eq, Hperm.
Qed.



Definition termtree_eq : relation termtree := fun t t' => 
  Permutation (list_of_termtree t) (list_of_termtree t').

Print Instances Equivalence.

#[export] Instance termtree_eq_equivalence : Equivalence termtree_eq.
Proof.
  unfold termtree_eq.
  split; hnf; intros. 
  - now reflexivity.
  - now symmetry.
  - now etransitivity; eassumption.
Qed.

Definition termfun_eq {fT} (SfT : SummableTy termtree fT) : relation fT := 
  summable_pointwise_relation termtree_eq SfT.

Global Arguments termfun_eq {_} (!_) _ _ /.

Definition summable_termfun_eq {fT fT'} 
  (SfT : SummableTy termtree fT) (SfT' : SummableTy termtree fT') : 
  fT -> fT' -> Prop :=
  fun f f' => 
  exists (P : STPerm SfT SfT'), termfun_eq SfT' (perm_args_of_STPerm P f) f'.


Fixpoint sum_termfun {fT} (SfT : SummableTy termtree fT) : fT -> R :=
  match SfT with 
  | STnil => realize_termtree
  | STcons A SA SfT' => fun f => 
    sum_of (fun a => sum_termfun SfT' (f a))
  end.



Add Parametric Morphism : realize_termtree
  with signature (termtree_eq ==> req) as realize_termtree_eq_of_termtree_eq.
Proof.
  apply realize_termtree_eq_of_list_prod_perm.
Qed.

Add Parametric Morphism {fT} (SfT : SummableTy termtree fT) : (sum_termfun SfT)
  with signature (termfun_eq SfT ==> req) as sum_termfun_eq_of_termfun_eq.
Proof.
  unfold termfun_eq.
  induction SfT.
  - simpl.
    intros ? ? ->.
    reflexivity.
  - simpl.
    intros f f' Hf.
    apply sum_of_ext.
    intros a.
    apply IHSfT.
    apply Hf.
Qed.

Add Parametric Morphism {C} {fT fT'} 
  (ceq : relation C)
  {SfT : SummableTy C fT} {SfT' : SummableTy C fT'} (P : STPerm SfT SfT') : 
  (perm_args_of_STPerm P) with signature 
  summable_pointwise_relation ceq SfT ==> summable_pointwise_relation ceq SfT'
  as perm_args_of_STPerm_summable_pointwise_mor.
Proof.
  induction P.
  - simpl.
    auto.
  - simpl.
    intros f f' Hf a.
    apply IHP, Hf.
  - simpl.
    intros f f' Hf a b.
    apply Hf.
  - simpl. 
    intros f f' Hf.
    apply IHP2.
    apply IHP1.
    apply Hf.
Qed.

Lemma perm_args_of_STPerm_stperm_symm {C} {fT fT'} 
  (ceq : relation C) `{Reflexive C ceq} `{Transitive C ceq}
  {SfT : SummableTy C fT} {SfT' : SummableTy C fT'} (P : STPerm SfT SfT') f :
  summable_pointwise_relation ceq SfT 
    (perm_args_of_STPerm (stperm_symm _ _ P) (perm_args_of_STPerm P f))
    f.
Proof.
  induction P.
  - simpl; reflexivity.
  - simpl.
    intros a.
    apply IHP.
  - simpl.
    intros b a.
    apply summable_pointwise_relation_Reflexive, _.
  - simpl.
    pose proof @summable_pointwise_relation_Transitive.
    rewrite IHP2.
    apply IHP1.
Qed.


Lemma perm_args_of_STPerm_stperm_refl {C} {fT} 
  (ceq : relation C) `{Reflexive C ceq}
  (SfT : SummableTy C fT) f :
  summable_pointwise_relation ceq SfT 
    (perm_args_of_STPerm (stperm_refl SfT) f)
    f.
Proof.
  induction SfT.
  - simpl; reflexivity.
  - simpl.
    intros a.
    auto.
Qed.

#[export] Instance summable_termfun_eq_equivalence 
  {fT} (SfT : SummableTy termtree fT) : 
  Equivalence (summable_termfun_eq SfT SfT).
Proof.
  split; intros ? *.
  - exists (stperm_refl _).
    simpl.
    rewrite perm_args_of_STPerm_stperm_refl by apply _.
    reflexivity.
  - intros (P & HP).
    exists (stperm_symm _ _ P).
    rewrite <- HP.
    apply perm_args_of_STPerm_stperm_symm; apply _.
  - intros (P & HP) (P' & HP').
    exists (stperm_trans _ _ _ P P').
    simpl.
    rewrite HP, HP'.
    reflexivity.
Qed.


Lemma sum_termfun_eq_of_summable_termfun_eq {fT fT'} 
  (SfT : SummableTy termtree fT) (SfT' : SummableTy termtree fT') f f' : 
  summable_termfun_eq SfT SfT' f f' -> 
  sum_termfun SfT f == sum_termfun SfT' f'.
Proof.
  intros (P & HP).
  revert HP;
  induction P;
  simpl;
  intros HP.
  - now rewrite HP.
  - apply sum_of_ext.
    intros a.
    apply IHP, HP.
  - rewrite sum_of_comm.
    apply sum_of_ext; intros a.
    apply sum_of_ext; intros b.
    specialize (HP a b).
    rewrite HP.
    reflexivity.
  - rewrite <- IHP2 by eassumption.
    apply IHP1.
    reflexivity.
Qed.







Module Alternate.


#[universes(polymorphic)]
Inductive SummableWithArrows : Type -> list SummableType -> Type :=
  | SummableWithArrows_R : SummableWithArrows R []
  | SummableWithArrows_cons (A : Type) (SA : Summable A) 
    {T : Type} {l : list SummableType} : 
    SummableWithArrows T l ->
    SummableWithArrows (A -> T) (existT Summable A SA :: l).


Existing Class SummableWithArrows.
#[global] Hint Constructors SummableWithArrows : typeclass_instances.

Fixpoint sum_summable_aux {l fT} (Pf : SummableWithArrows fT l) : fT -> R :=
  match Pf with 
  | SummableWithArrows_R => fun r => r
  | SummableWithArrows_cons A SA Pf => fun f => 
    @sum_of A SA (fun r => sum_summable_aux Pf (f r))
  end.

(* Make sure sum_summable_aux simplifies in the proper circumstances *)
Global Arguments sum_summable_aux {_ _} !_ _ /.

Definition sum_summable {l fT} (Pf : SummableWithArrows fT l) : fT -> R :=
  sum_summable_aux Pf.

Lemma sum_summable_defn {l fT} (Pf : SummableWithArrows fT l) (f : fT) : 
  sum_summable Pf f = sum_summable_aux Pf f.
Proof. reflexivity. Qed.

(* Ensure [sum_summable] does not simplify *)
Global Opaque sum_summable.

Notation 
  "∑ x .. y , f" :=
  (sum_summable _ (fun x => .. (fun y => f) ..))
  (at level 60, 
  x binder, y binder, f at level 69,
  right associativity).

Lemma SummableWithArrows_type_eq {l fT} (Pf : SummableWithArrows fT l) : 
  fT = List.fold_right (fun sA B => projT1 sA -> B) R l.
Proof.
  induction Pf; [reflexivity|].
  rewrite IHPf.
  reflexivity.
Defined.

Lemma SummableWithArrows_type_eq_arr {l fT} (Pf : SummableWithArrows fT l) : 
  fT = arrows (List.fold_right 
    (fun sA tl => Tcons (projT1 sA) tl) Tnil l) R.
Proof.
  induction Pf; [reflexivity|].
  rewrite IHPf.
  reflexivity.
Defined.


Lemma sum_one `{Summable A} f : 
  ∑ x : A, f x = ∑' x, f x.
Proof. 
  reflexivity.
Qed.

Lemma sum_none f : 
  sum_summable (SummableWithArrows_R) f = f.
Proof. 
  reflexivity.
Qed.

Lemma sum_cons `{SA : Summable A} {l fT} (Pf : SummableWithArrows fT l) f : 
  sum_summable (SummableWithArrows_cons A SA Pf) f = 
  ∑' x, sum_summable Pf (f x).
Proof.
  reflexivity.
Qed.

Add Parametric Morphism `{SA : Summable A} {l fT} 
  (Pf : SummableWithArrows fT l) : (sum_summable 
  (SummableWithArrows_cons A SA Pf)) with signature
  Morphisms.pointwise_relation A eq ==> eq as 
  sum_summable_cons_mor.
Proof.
  intros f g Hfg.
  rewrite 2!sum_cons.
  apply sum_of_ext_eq.
  intros x.
  rewrite Hfg.
  reflexivity.
Qed.

Lemma sum_comm_head `{SA : Summable A} `{SB : Summable B} {l fT}
  (Pf : SummableWithArrows fT l) f : 
  sum_summable (SummableWithArrows_cons A SA 
    (SummableWithArrows_cons B SB Pf)) f ==
  sum_summable (SummableWithArrows_cons B SB
    (SummableWithArrows_cons A SA Pf))
    (fun b a => f a b).
Proof.
  rewrite_strat (bottomup sum_cons).
  apply sum_of_comm.
Qed.

Local Open Scope list_scope.

(* Definition SummableWithArrows_cons_ind 
  (P : forall fT l, SummableWithArrows fT l -> Type) 
  {A SA}
  (Pcons : forall fT' l Pf',
    P (A -> fT') (_ :: l) (SummableWithArrows_cons A SA Pf')) : 
  forall l fT Pf, P fT (existT _ A SA :: l) Pf.
  let aux : forall fT l *)


Inductive PermutationT {A} : list A -> list A -> Type :=
  | perm_nil: PermutationT [] []
  | perm_skip x l l' : PermutationT l l' -> PermutationT (x::l) (x::l')
  | perm_swap x y l : PermutationT (y::x::l) (x::y::l)
  | perm_trans l l' l'' :
      PermutationT l l' -> PermutationT l' l'' -> PermutationT l l''.


(* Fixpoint type_summable_with_of_permT {l l'} (P : PermutationT l l') : 
  forall fT (Pf : SummableWithArrows fT l), {fT' & SummableWithArrows fT' l'} :=
  match P with 
  | perm_nil => 
    fun fT Pf => existT _ fT Pf
  | perm_skip x l l' P' => 

  | _ => sorry
  end. *)










Local Open Scope list_scope.

Fixpoint list_swap_nth {A} (n : nat) (l : list A) : list A :=
  match n with 
  | 0 => 
    match l with 
    | x :: y :: l' => y :: x :: l'
    | [x] => [x]
    | [] => []
    end
  | S n' => 
    match l with 
    | x :: l' => x :: list_swap_nth n' l'
    | [] => []
    end
  end.

Fixpoint type_swap_nth {l fT} (n : nat) (Pf : SummableWithArrows fT l) : Type :=
  match n with 
  | 0 => 
    match Pf with 
    | SummableWithArrows_cons A SA
      (@SummableWithArrows_cons B SB fT' _ Pf') => 
      B -> A -> fT'
    | SummableWithArrows_cons A SA SummableWithArrows_R => A -> R
    | SummableWithArrows_R => R
    end
  | S n' => 
    match Pf with 
    | SummableWithArrows_cons A SA Pf' => 
      A -> type_swap_nth n' Pf'
    | SummableWithArrows_R => R
    end
  end.

Fixpoint SummableWith_swap_nth {l fT} n : 
  forall (Pf : SummableWithArrows fT l),
  SummableWithArrows (type_swap_nth n Pf) (list_swap_nth n l) :=
  match n with 
  | 0 => fun Pf => 
    match Pf as Pf' in SummableWithArrows fT' l' 
      return SummableWithArrows (type_swap_nth 0 Pf') 
        (list_swap_nth 0 l') with 
    | SummableWithArrows_cons A SA Pf' => 
      match Pf' as Pf' in SummableWithArrows fT' l' 
        return SummableWithArrows (type_swap_nth 0 
          (SummableWithArrows_cons A SA Pf')) 
          (list_swap_nth 0 (existT Summable A SA :: l')) with 
      | SummableWithArrows_cons B SB Pf' => 
        SummableWithArrows_cons B SB (SummableWithArrows_cons A SA Pf')
      | SummableWithArrows_R => 
        SummableWithArrows_cons A SA SummableWithArrows_R
      end
    | SummableWithArrows_R => SummableWithArrows_R
    end
  | S n' => fun Pf => 
    match Pf with 
    | SummableWithArrows_cons A SA Pf' => 
      SummableWithArrows_cons A SA (SummableWith_swap_nth n' Pf')
    | SummableWithArrows_R => SummableWithArrows_R
    end
  end.

Fixpoint SummableWith_swap_nth_arg {l fT} n : 
  forall (Pf : SummableWithArrows fT l),
  fT -> type_swap_nth n Pf :=
  match n with 
  | 0 => fun Pf => 
    match Pf (* as Pf' in SummableWithArrows fT' l' 
      return fT' -> (type_swap_nth 0 Pf') *) with 
    | SummableWithArrows_cons A SA Pf' => 
      match Pf' (* as Pf' in SummableWithArrows fT' l' 
        return (A -> fT') -> (
          (type_swap_nth 0 (SummableWithArrows_cons A SA Pf'))) *) with 
      | SummableWithArrows_cons B SB Pf' => 
        fun f => fun b a => f a b
      | SummableWithArrows_R => 
        fun f => f
      end
    | SummableWithArrows_R => fun f => f
    end
  | S n' => fun Pf => 
    match Pf with 
    | SummableWithArrows_cons A SA Pf' => 
      fun f => fun a => 
      SummableWith_swap_nth_arg n' Pf' (f a)
    | SummableWithArrows_R => fun f => f
    end
  end.

(* Lemma sum_swap_helper {l fT} n (Pf : SummableWithArrows fT l) *)



Definition Arrows (l : list SummableType) (T : Type) := 
  List.fold_right (fun sA B => projT1 sA -> B) T l.

(* Helper function for computing a sum over a list of registers / summable types *)
Fixpoint sum_over_aux (l : list SummableType) : Arrows l R -> R :=
  match l with 
  | nil => fun r => r
  | cons sA l' => fun f => 
    @sum_of (projT1 sA) (projT2 sA) (fun r => sum_over_aux l' (f r))
  end.

(* TODO: Do we want this? *)
(* Ensure [sum_over_aux] simplifies properly *)
Global Arguments sum_over_aux (!_) _%_function_scope /.


(* The sum of a function over a list of registers *)
Definition sum_over (l : list SummableType) (f : Arrows l R) : R :=
  sum_over_aux l f.

(* Lemma to turn [sum_over] into its simplifying version *)
Lemma sum_over_defn l f : 
  sum_over l f = sum_over_aux l f.
Proof. reflexivity. Qed.

(* To make the notation work, we need [sum_over] not to expand *)
Global Opaque sum_over.

(* Helper function solving [Arrows ?l R = T] for [l], returning 
  an open term with holes for the [Summable] instances *)
Ltac _find_sum_over_list T :=
  let _ := match goal with |- _ => idtac T end in 
  let rec go T := 
    lazymatch T with 
    | R => uconstr:(@nil SummableType)
    | ?A -> ?T' => 
      let lT' := go T' in 
      let _ := match goal with |- _ => idtac lT' end in 
      uconstr:(@cons SummableType (@existT Type Summable A _) lT')
    | _ => fail "Could not recognize arrows list of type" T 
    end in 
  go T.
  (* let res := go T in 
  exact res. *)

(* Our main notation for summations, taking any number of registers *)
(* Notation 
  "∑ x .. y , f" :=
  (let u := (fun x => .. (fun y => f) ..) in 
    sum_over ltac:(
      let res := _find_sum_over_list ltac:(type of u) 
      in exact res)
    u)
  (at level 60, 
  x binder, y binder, f at level 69,
  right associativity,
  only parsing). *)

(* Our main notation for summations, taking any number of registers *)
Notation 
  "∑ x .. y , f" :=
  (sum_over _ (fun x => .. (fun y => f) ..))
  (at level 60, 
  x binder, y binder, f at level 69,
  right associativity).

End Alternate.

End Summation.
