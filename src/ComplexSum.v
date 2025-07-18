Require Import QuantumLib.Complex.
Require Vector.
Import Vector.VectorNotations.
Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Btauto.

(*
This file demonstrates proving basic facts in the ZX calculus using "sum over paths" semantics for
ZX-diagrams. The main idea is to represent a ZX-diagram as a function from one or more registers of
indices (i.e. boolean values) to a complex.

Complex diagrams are built from simpler ones tensor-network style, i.e. by taking produces of generators
and summing over contracted indices.
*)


(* Part 1 defines a typeclass and notation for summations, then establishes some basic facts. *)

(* Typeclass for indices that can be summed over. The main instances are "bool" for a
   single 2D index and Vector.t A m, for A summable, which represents a register of "m"
   indices of type A.
   
   It consists of three members:
    - csum: a function that takes a function from A to C and returns a complex number
    - csum_ext: a property that states that if two functions from A to C are equal pointwise,
      then their sums are equal
    - csum_comm: a property that states that the order of summation does not matter
*)
Class ComplexSum (A : Type) :=
  { csum : (A -> C) -> C;
    csum_ext (f g : A -> C) : (forall b, f b = g b) -> csum f = csum g;
    csum_comm (f : A -> A -> C):
      csum (fun a => csum (fun b => f a b)) =
      csum (fun b => csum (fun a => f a b)) ;
    csum_distr (f : A -> C) (c : C):
      c * csum (fun a => f a) = csum (fun a => c * f a)  }.

#[global] Opaque csum.
#[global] Notation "∑ x , e" := (csum (fun x => (e))) (at level 50, x at level 60).
#[global] Notation "∑ x : n , e" := (csum (fun x : Vector.t _ n => (e))) (at level 50, x at level 60, n at level 60).

Section SumDefs.

Generalizable All Variables.
Variable A : Type.
Context `{csumA : ComplexSum A}.

(* enables rewriting to be done underneath a summation, via "setoid_rewrite" *)
#[global] Instance csum_morphism:
    Proper (pointwise_relation A eq ==> eq) csum.
Proof.
    simpl_relation.
    unfold pointwise_relation in H.
    apply csum_ext.
    assumption.
Qed.

Theorem csum_distl (f : A -> C) (c : C):
    (∑ a , f a) * c = ∑ a , f a * c.
Proof.
    rewrite Cmult_comm.
    rewrite csum_distr.
    apply csum_ext; intros.
    rewrite Cmult_comm.
    reflexivity.
Qed.

Definition csum_bool (f : bool -> C) : C :=
  f false + f true.

Theorem csum_bool_ext (f g: bool -> C):
    (forall b, f b = g b) -> csum_bool f = csum_bool g.
Proof.
    intros.
    unfold csum_bool.
    repeat rewrite H.
    reflexivity.
Qed.

Theorem csum_bool_comm (f : bool -> bool -> C):
      csum_bool (fun a => csum_bool (fun b => f a b)) =
      csum_bool (fun b => csum_bool (fun a => f a b)).
Proof.
    unfold csum_bool.
    ring.
Qed.

Theorem csum_bool_distr (f : bool -> C) (c : C):
    c * csum_bool f = csum_bool (fun b => c * f b).
Proof.
    unfold csum_bool.
    ring.
Qed.

#[global] Instance ComplexSum_bool : ComplexSum bool :=
  { csum := csum_bool;
    csum_ext := csum_bool_ext;
    csum_comm := csum_bool_comm;
    csum_distr := csum_bool_distr }.

Theorem csum_bool_def (f : bool -> C): csum f = f false + f true.
Proof.
    reflexivity.
Qed.


Fixpoint csum_vec {n: nat} (f: Vector.t A n -> C) : C :=
    match n, f with
    | O, _ => f []
    | S _, _ => csum (fun b : A => csum_vec (fun bs => f (b :: bs)))
    end.

Theorem csum_vec_ext {n: nat} (f g: Vector.t A n -> C) :
    (forall bs, f bs = g bs) ->
    csum_vec f = csum_vec g.
    induction n.
    - simpl. easy.
    - simpl. 
      intros H.
      apply csum_ext.
      intros b.
      destruct (IHn (fun bs => f (b :: bs)) (fun bs => g (b :: bs))).
      intros bs.
      apply (H (b :: bs)).
      reflexivity.
Qed.

Theorem csum_vec_succ0 {n: nat} (f: Vector.t A (S n) -> C) :
    csum_vec f = csum (fun b => csum_vec (fun bs => f (b :: bs))).
Proof.
    reflexivity.
Qed.

Theorem csum_vec_comm1_0 {n : nat} (f: A -> Vector.t A n -> C) :
    csum (fun b => csum_vec (fun bs => f b bs)) =
    csum_vec (fun bs => csum (fun b => f b bs)).
Proof.
    induction n.
    - easy.
    - setoid_rewrite csum_vec_succ0 at 1.
      rewrite csum_comm.
      setoid_rewrite IHn at 1.
      rewrite csum_vec_succ0.
      reflexivity.
Qed.

Instance csum_vec_morphism {n : nat}:
         Proper (pointwise_relation (Vector.t A n) eq ==> eq) csum_vec.
Proof.
    simpl_relation.
    unfold pointwise_relation in H.
    apply csum_vec_ext.
    assumption.
Qed.

Theorem csum_vec_comm {n m : nat} (f : Vector.t A n -> Vector.t A m -> C):
    csum_vec (fun a => csum_vec (fun b => f a b)) =
    csum_vec (fun b => csum_vec (fun a => f a b)).
Proof.
    induction n.
    - easy.
    - setoid_rewrite csum_vec_succ0.
      rewrite <- csum_vec_comm1_0.
      apply csum_ext.
      intros b.
      apply IHn.
Qed.

Theorem csum_vec_distr {n: nat} (f: Vector.t A n -> C) (c: C):
    c * csum_vec f = csum_vec (fun bs => c * f bs).
Proof.
    induction n.
    - reflexivity.
    - simpl.
      rewrite csum_distr.
      apply csum_ext; intros.
      apply IHn.
Qed.


#[global] Instance ComplexSum_vec {n: nat}: ComplexSum (Vector.t A n) :=
  { csum := csum_vec;
    csum_ext := csum_vec_ext;
    csum_comm := csum_vec_comm;
    csum_distr := csum_vec_distr }.

Theorem csum_vec_zero (f : Vector.t A 0 -> C) :
    csum f = f [].
    reflexivity.
Qed.

Theorem csum_vec_succ {n: nat} (f: Vector.t A (S n) -> C) :
    csum f = csum (fun b => csum (fun bs => f (b :: bs))).
Proof.
    reflexivity.
Qed.

Theorem csum_vec_comm1 {n : nat} (f: A -> Vector.t A n -> C) :
    csum (fun b => csum (fun bs => f b bs)) =
    csum (fun bs => csum (fun b => f b bs)).
Proof.
    assert (H: forall n (f : Vector.t A n -> C), csum f = csum_vec f).
    reflexivity.
    setoid_rewrite H.
    rewrite csum_vec_comm1_0.
    reflexivity.
Qed.

Theorem csum_vec_singleton (f: Vector.t A 1 -> C) :
    csum f = csum (fun b => f [b]).
Proof.
    easy.
Qed.

Theorem csum_vec_append {n m: nat} (f: Vector.t A (n + m) -> C) :
    csum f = csum (fun bs1 => csum (fun bs2 => f (bs1 ++ bs2))).
Proof.
    induction n as [|n IHn].
    - simpl. reflexivity.
    - simpl.
      repeat rewrite csum_vec_succ.
      apply csum_ext.
      intros b.
      rewrite IHn.
      simpl.
      reflexivity.
Qed.

End SumDefs.

Ltac split_sums :=
    repeat progress (
        try setoid_rewrite csum_vec_succ;
        try setoid_rewrite csum_vec_zero;
        try setoid_rewrite csum_vec_append).
