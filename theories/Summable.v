Require Ring_theory.
Require Integral_domain.
Require List.
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

Import SR.
Module SRF := SemiRingFacts SR.
Import SRF.
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

Fixpoint perm_args_of_STperm {fT fT'} 
  `{SfT : SummableTy B fT} {SfT' : SummableTy B fT'}
  (P : STPerm SfT SfT') : fT -> fT' :=
  match P with 
  | stperm_nil => fun r => r
  | stperm_skip A SA ST ST' P' => 
    fun f => fun a => perm_args_of_STperm P' (f a)
  | stperm_swap A SA B SB ST => 
    fun f => fun a b => f b a
  | stperm_trans ST ST' ST'' P P' => 
    fun f => perm_args_of_STperm P' (perm_args_of_STperm P f)
  end.


Lemma sum_STperm {fT fT'} (SfT : SummableTy R fT) (SfT' : SummableTy R fT') 
  (P : STPerm SfT SfT') (f : fT) : 
  sum_summable SfT' (perm_args_of_STperm P f) ==
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


Fixpoint swap_summable_nth_STperm {C} (n : nat) : 
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
        (swap_summable_nth_STperm n' SfT')
    | STnil => stperm_refl _
    end
  end.

Fixpoint swap_summabletys {C} (l : list nat) {fT} (ST : SummableTy C fT) : 
  {fT' & SummableTy C fT'} :=
  match l with 
  | [] => existT _ fT ST
  | n :: l' => 
    swap_summabletys l' (swap_summable_nth n ST)
  end.

Notation swap_type_nths l ST := (projT1 (swap_summabletys l ST)).
Notation swap_summable_nths l ST := (projT2 (swap_summabletys l ST)).

Fixpoint swap_summabletys_STperm {C} (l : list nat) 
  {fT} (ST : SummableTy C fT) :
  STPerm ST (swap_summable_nths l ST) :=
  match l with 
  | [] => stperm_refl _
  | n :: l' => 
    stperm_trans _ _ _ 
      (swap_summable_nth_STperm n ST)
      (swap_summabletys_STperm l' (swap_summable_nth n ST))
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

