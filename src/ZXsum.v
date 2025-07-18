Require Import ComplexSum.
Require Import QuantumLib.Complex.
Require Vector.
Import Vector.VectorNotations.
Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Btauto.

(* Part 2 defines spiders and builds up to a proof of the general spider fusion rule. *)

(* Helper function for spider definition: returns true when all the booleans in the given
   vector are equal to "b" *)
Fixpoint allb {n: nat} (b : bool) (bs : Vector.t bool n) : bool :=
    match bs with
    | [] => true
    | b' :: bs' => (eqb b b') && allb b bs'
    end.

Lemma allb_single (b c: bool) : allb b [c] = eqb b c.
Proof.
    simpl.
    rewrite andb_comm.
    reflexivity.
Qed.

Lemma allb_append {n m: nat} (b : bool) (bs1 : Vector.t bool n) (bs2 : Vector.t bool m) :
    allb b (bs1 ++ bs2) = allb b bs1 && allb b bs2.
Proof.
    induction bs1.
    - reflexivity.
    - simpl. rewrite IHbs1. rewrite andb_assoc. reflexivity.
Qed.

(* A single Z spider, with the given phase on a register of qubit wires. Note that if "bs" is
   empty, then "allb false bs" and "allb true bs" both evaluate to true. This gives the correct
   definition for a 0-legged spider *)
Definition zsp {n: nat} (phase: R) (bs : Vector.t bool n) : C :=
    (if allb false bs then 1 else 0) +
    (if allb true bs then Cexp phase else 0).

Lemma zsp_allb {n m: nat} (phase: R) (bs: Vector.t bool n) (cs: Vector.t bool m) :
    (allb false bs) = (allb false cs) -> (allb true bs) = (allb true cs) -> zsp phase bs = zsp phase cs.
    intros Hf Ht.
    unfold zsp.
    rewrite Hf.
    rewrite Ht.
    reflexivity.
Qed.

(* tactic closes goals of the form "zsp p bs0 = zsp p bs1", where "bs0" and "bs1" are equal
   up to cons/append rules, repeated elements, and associativity/commutativity. *)
Ltac squash_spiders :=
  repeat progress (
    intros;
    try apply csum_ext;
    try apply (f_equal2 Cmult));
  apply zsp_allb;
  simpl;
  repeat rewrite allb_append;
  repeat rewrite allb_single;
  simpl;
  btauto.

(* convenience tactic for explicitly giving a replacement for spiders on the LHS
   of the current goal *)
Ltac replace_spiders t :=
  match goal with
    | [ |- ?lhs = _ ] => replace lhs with t by squash_spiders
  end.

(* summing over one leg of a spider removes it *)
Lemma sum_spider1 {n: nat} (p: R) (bs : Vector.t bool n) :
    ∑ c , zsp p (c :: bs) = zsp p bs.
Proof.
    unfold zsp.
    rewrite csum_bool_def.
    simpl.
    case (allb true bs);
    case (allb false bs);
    ring.
Qed.

(* summing over many legs of a spider removes them all *)
Lemma sum_spider {n m: nat} (p: R) (bs : Vector.t bool n):
    ∑ cs : m , zsp p (cs ++ bs) = zsp p (bs).
Proof.
    induction m.
    - easy.
    - simpl.
      rewrite csum_vec_succ.
      setoid_rewrite csum_vec_comm1.
      setoid_rewrite sum_spider1.
      assumption.
Qed.

(* zero or more self-loops can be removed *)
Theorem spider_loop {n m: nat} (p: R) (bs : Vector.t bool n) :
    ∑ cs : m , zsp p (cs ++ cs ++ bs) = zsp p bs.
Proof.
    replace_spiders (∑ cs : m , zsp p (cs ++ bs)).
    rewrite sum_spider.
    reflexivity.
Qed.

(* spider fusion where a single leg connects the spiders *)
Lemma spider1 {n m: nat} (p1 p2: R) (bs1 : Vector.t bool n) (bs2 : Vector.t bool m) :
    ∑ c , zsp p1 (c :: bs1) * zsp p2 (c :: bs2) =
    zsp (p1 + p2) (bs1 ++ bs2).
Proof.
    unfold zsp.
    rewrite csum_bool_def.
    repeat rewrite allb_append.
    simpl.
    case (allb true bs1);
    case (allb false bs1);
    case (allb true bs2);
    case (allb false bs2);
    simpl;
    autorewrite with Cexp_db;
    ring.
Qed.

(* spider fusion where many legs connect the spiders

The proof works by first fusing on a single leg, then removing self-loops. Up to leg re-arranging,
the main parts of this proof are applications of "spider1" and "spider_loop". *)
Theorem spider {n m k: nat} (p1 p2: R) (bs1 : Vector.t bool n) (bs2 : Vector.t bool m) :
    ∑ cs : k+1 , zsp p1 (cs ++ bs1) * zsp p2 (cs ++ bs2) =
    zsp (p1 + p2) (bs1 ++ bs2).
Proof.
    split_sums.
    replace_spiders (∑ bs0 : k, ∑ b, zsp p1 (b :: bs0 ++ bs1) * zsp p2 (b :: bs0 ++ bs2)).
    setoid_rewrite spider1.
    replace_spiders (∑ bs0 : k, zsp (p1 + p2) (bs0 ++ bs0 ++ bs1 ++ bs2)).
    setoid_rewrite spider_loop.
    reflexivity.
Qed.
