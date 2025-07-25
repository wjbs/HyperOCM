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




(* FIXME: Move *)

Fixpoint vseq (start : nat) (len : nat) : Vector.t nat len :=
  match len with 
  | 0 => []
  | S l' => start :: vseq (S start) l'
  end. 

Require QuantumLib.Quantum QuantumLib.Modulus.

Definition nat_to_bits (len : nat) : nat -> Vector.t bool len :=
  fun n => Vector.map (Nat.testbit n) (vseq 0 len). 

Require Import QuantumLib.Bits.


Definition bits_to_nat {len} (v : Vector.t bool len) :=
  funbool_to_nat len (fun k => 
    match lt_dec k len with 
    | left H => Vector.nth_order (Vector.rev v) H
    | right _ => false end).


Open Scope nat_scope.

Lemma to_list_vseq start len : 
  Vector.to_list (vseq start len) = seq start len.
Proof.
  revert start;
  induction len; intros start; [reflexivity|].
  simpl.
  rewrite <- IHlen.
  reflexivity.
Qed.


Lemma nat_to_bits_to_list (len : nat) n : n < 2 ^ len -> 
  Vector.to_list (nat_to_bits len n) = nat_to_binlist len n.
Proof.
  intros Hn.
  unfold nat_to_bits.
  rewrite Vector.to_list_map, to_list_vseq.
  apply nth_ext with (d:= false) (d':=false).
  - rewrite length_map, length_seq.
    rewrite nat_to_binlist_length; easy.
  - intros k Hk.
    rewrite map_nth_small with (dnew := 0) by 
      (now rewrite length_map in Hk).
    rewrite length_map, length_seq in Hk.
    rewrite seq_nth by auto.
    rewrite nth_nat_to_binlist.
    reflexivity.
Qed.

Require stdpp.fin.
Import Modulus.


Lemma nth_nat_to_bits_gen start len n p : 
  (Vector.map (Nat.testbit n) (vseq start len)) [@ p ] = 
  Nat.testbit (n / 2 ^ start) (fin.fin_to_nat p).
Proof.
  revert start.
  induction p; intros start.
  - simpl.
    rewrite Nat.testbit_odd.
    rewrite Nat.shiftr_div_pow2.
    reflexivity.
  - cbn.
    rewrite IHp.
    rewrite Nat.div2_div, Nat.Div0.div_div.
    rewrite Nat.mul_comm.
    reflexivity.
Qed.

Lemma nth_nat_to_bits len n p : 
  (nat_to_bits len n) [@ p ] = 
  Nat.testbit n (fin.fin_to_nat p).
Proof.
  unfold nat_to_bits.
  rewrite nth_nat_to_bits_gen.
  rewrite Nat.div_1_r.
  reflexivity.
Qed.

Lemma nat_to_bits_eq_of_mod len n : 
  nat_to_bits len n = nat_to_bits len (n mod 2 ^ len).
Proof.
  apply Vector.eq_nth_iff.
  intros p _ <-.
  rewrite 2!nth_nat_to_bits.
  rewrite testbit_mod_pow2.
  pose proof (fin.fin_to_nat_lt p).
  bdestruct_one; [reflexivity|lia].
Qed.
  

Lemma nat_to_bits_succ len n :
  nat_to_bits (S len) n =
  (Nat.odd n :: nat_to_bits len (n / 2))%vector.
Proof.
  apply Vector.eq_nth_iff.
  intros p _ <-.
  rewrite nth_nat_to_bits.
  induction p using fin.fin_S_inv; [reflexivity|].
  cbn -[Nat.div].
  rewrite Nat.div2_div.
  rewrite nth_nat_to_bits.
  reflexivity.
Qed.

Lemma nat_to_bits_plus l1 l2 n :
  nat_to_bits (l1 + l2) n =
  (nat_to_bits l1 n ++ nat_to_bits l2 (n / (2 ^ l1)))%vector.
Proof.
  revert n;
  induction l1; intros n; [now rewrite Nat.div_1_r|].
  cbn [Nat.add].
  rewrite nat_to_bits_succ by assumption.
  rewrite nat_to_bits_succ.
  cbn [Vector.append].
  f_equal.
  rewrite IHl1.
  rewrite Nat.Div0.div_div.
  reflexivity.
Qed.





Lemma nat_to_bits_to_nat (len : nat) n : 
  n < 2 ^ len -> 
  bits_to_nat (nat_to_bits len n) = n.
Proof.
  intros Hn.
  apply Nat.bits_inj.
  unfold bits_to_nat.
  intros k.
  rewrite testbit_funbool_to_nat.
  bdestruct_one.
  2: {
    replace n with (n mod (2 ^ len)) by 
      now rewrite Nat.mod_small by easy.
    rewrite Nat.mod_pow2_bits_high; easy.
  }
  destruct (lt_dec (len - S k) len); [|lia].
  rewrite Vector.to_list_nth_order with (d:=false).
  rewrite Vector.to_list_rev, rev_nth
    by (rewrite Vector.length_to_list; easy).
  rewrite Vector.length_to_list.
  rewrite sub_S_sub_S by easy.
  rewrite nat_to_bits_to_list by easy.
  rewrite nth_nat_to_binlist.
  reflexivity.
Qed.

Lemma nat_to_bits_inj (len : nat) n m : 
  n < 2 ^ len -> m < 2 ^ len -> 
  nat_to_bits len n = nat_to_bits len m <-> n = m.
Proof.
  intros Hn Hm.
  split; [|now intros ->].
  intros Hnm%(f_equal bits_to_nat).
  now rewrite 2!nat_to_bits_to_nat in Hnm by auto.
Qed.

Lemma bits_to_nat_to_bits {len} (v : Vector.t bool len) : 
  nat_to_bits len (bits_to_nat v) = v.
Proof.
  apply Vector.to_list_inj.
  apply nth_ext with (d:=false) (d':=false);
  [now rewrite 2!Vector.length_to_list|].
  rewrite Vector.length_to_list.
  intros k Hk.
  rewrite nat_to_bits_to_list by apply funbool_to_nat_bound.
  rewrite nth_nat_to_binlist.
  unfold bits_to_nat.
  rewrite testbit_funbool_to_nat.
  bdestruct_one; [|lia].
  destruct (lt_dec (len - S k) len); [|lia].
  rewrite Vector.to_list_nth_order with (d:=false).
  rewrite Vector.to_list_rev, rev_nth
    by (rewrite Vector.length_to_list; easy).
  rewrite Vector.length_to_list.
  rewrite sub_S_sub_S by easy.
  reflexivity.
Qed.



(* TODO: Replace with type-list based things *)
Definition AbsTensor (n m : nat) :=
  Vector.t bool n -> Vector.t bool m -> C.

Definition stack_tensor {n0 m0 n1 m1} 
  (t0 : AbsTensor n0 m0) (t1 : AbsTensor n1 m1) : 
    AbsTensor (n0 + n1) (m0 + m1) :=
  fun i j => 
  let (i0, i1) := Vector.splitat n0 i in 
  let (j0, j1) := Vector.splitat m0 j in 
  (t0 i0 j0 * t1 i1 j1)%C.

Definition compose_tensor {n m o} 
  (t0 : AbsTensor n m) (t1 : AbsTensor m o) : 
    AbsTensor n o :=
  fun i k => ∑ j : m, (t0 i j * t1 j k)%C.

Definition id_tensor n : AbsTensor n n :=
  fun i j => 
  if Vector.eqb bool Bool.eqb i j then C1 else C0.

Definition swap_tensor : AbsTensor 2 2 :=
  fun i j => 
  let (i1, i0) := (Vector.hd i, Vector.hd (Vector.tl i)) in
  let (j1, j0) := (Vector.hd j, Vector.hd (Vector.tl j)) in
  if Bool.eqb i0 j1 && Bool.eqb i1 j0 then C1 else C0.

Definition H_tensor : AbsTensor 1 1 :=
  fun i j => 
  let i := Vector.hd i in 
  let j := Vector.hd j in 
  Cdiv (match i, j with 
  | true, true => -C1
  | _, _ => C1
  end) (sqrt 2).

Fixpoint stack_tensors_1 n (t : AbsTensor 1 1) : AbsTensor n n :=
  match n with 
  | 0 => id_tensor 0
  | S n' => stack_tensor t (stack_tensors_1 n' t)
  end.

Definition Z_tensor n m α : AbsTensor n m :=
  fun i j => zsp α (i ++ j)%vector.

Definition X_tensor n m α : AbsTensor n m :=
  compose_tensor (compose_tensor 
    (stack_tensors_1 n H_tensor)
    (Z_tensor n m α))
    (stack_tensors_1 m H_tensor).

Definition cup_tensor : AbsTensor 0 2 :=
  fun i j => 
  let (j0, j1) := (Vector.hd j, Vector.hd (Vector.tl j)) in 
  if Bool.eqb j0 j1 then C1 else C0.

Definition cap_tensor : AbsTensor 2 0 :=
  fun i j => 
  let (i0, i1) := (Vector.hd i, Vector.hd (Vector.tl i)) in 
  if Bool.eqb i0 i1 then C1 else C0.

Definition matrix_of_tensor {n m : nat} (t : AbsTensor n m) : 
  Matrix.Matrix (2^m) (2^n) :=
  Matrix.make_WF (fun i j => 
    t (Vector.rev (nat_to_bits n j)) (Vector.rev (nat_to_bits m i))).

Definition tensor_of_matrix {n m : nat} (A : Matrix.Matrix (2^m) (2^n)) : 
  AbsTensor n m :=
  fun i j => A (bits_to_nat (Vector.rev j)) (bits_to_nat (Vector.rev i)).

Lemma WF_matrix_of_tensor {n m} (t : AbsTensor n m) : 
  WF_Matrix (matrix_of_tensor t).
Proof. apply WF_make_WF. Qed.

#[export] Hint Resolve WF_matrix_of_tensor : wf_db.

Add Parametric Morphism {n m} : (@tensor_of_matrix n m) with signature
  mat_equiv ==> eq as tensor_of_matrix_eq_of_mat_equiv.
Proof.
  intros A B HAB.
  unfold tensor_of_matrix.
  prep_matrix_equality.
  apply HAB; apply funbool_to_nat_bound.
Qed.

Lemma csum_vec_eq_bigsum {n} f : 
  ∑ v : n, f v = 
  Σ (fun i => f (nat_to_bits n i)) (2 ^ n).
Proof.
  induction n.
  - symmetry; apply Cplus_0_l.
  - rewrite csum_vec_succ, csum_bool_def.
    rewrite 2!IHn.
    etransitivity; [symmetry; refine (big_sum_plus (G:=C) _ _ _)|].
    change (2 ^ (S n)) with (2 * 2 ^ n).
    rewrite big_sum_product_div_mod_split.
    apply big_sum_eq_bounded.
    intros k Hk.
    simpl.
    rewrite Cplus_0_l.
    rewrite 2!nat_to_bits_succ.
    rewrite Nat.odd_mul, andb_false_r.
    rewrite Nat.odd_succ, Nat.even_mul, orb_true_r.
    rewrite Nat.div_mul by easy.
    replace (S (k * 2) / 2) with ((k * 2 + 1) / 2) by (f_equal; lia).
    rewrite Nat.div_add_l by easy.
    rewrite Nat.add_0_r.
    reflexivity.
Qed.

Lemma cast_refl {A n} (v : Vector.t A n) H :
  Vector.cast v H = v.
Proof.
  rewrite (Peano_dec.UIP_nat _ _ H eq_refl).
  clear H.
  induction v; [reflexivity|].
  simpl.
  congruence.
Qed.

Lemma to_list_cast {A n m} (v : Vector.t A m) (H : m = n) : 
  Vector.to_list (Vector.cast v H) = Vector.to_list v.
Proof.
  subst.
  rewrite cast_refl.
  reflexivity.
Qed.

Lemma rev_cast {A n m} (v : Vector.t A m) (H : m = n) : 
  Vector.rev (Vector.cast v H) = Vector.cast (Vector.rev v) H.
Proof.
  subst.
  now rewrite 2!cast_refl.
Qed.

Lemma rev_append {A n m} (v : Vector.t A m) (u : Vector.t A n) :  
  Vector.rev (v ++ u)%vector = 
  Vector.cast (Vector.rev u ++ Vector.rev v)%vector (Nat.add_comm _ _).
Proof.
  apply Vector.to_list_inj.
  rewrite to_list_cast, Vector.to_list_append, 
    3!Vector.to_list_rev, Vector.to_list_append.
  rewrite rev_app_distr.
  reflexivity.
Qed.

Lemma cast_nat_to_bits {n m i} (H : m = n) : 
  Vector.cast (nat_to_bits m i) H = nat_to_bits n i.
Proof.
  subst.
  now rewrite cast_refl.
Qed.

Lemma cast_cast {A n m o} (v : Vector.t A o) (H : o = m) (H' : m = n) : 
  Vector.cast (Vector.cast v H) H' = Vector.cast v (eq_trans H H').
Proof.
  subst.
  now rewrite 3!cast_refl.
Qed.

Lemma csum_cast {n m f} (H : m = n) : 
  ∑ v : n, f v = 
  ∑ v : m, f (Vector.cast v H).
Proof.
  subst.
  apply csum_ext.
  intros v.
  f_equal.
  clear f.
  induction v; [reflexivity|].
  simpl.
  congruence.
Qed.

Lemma csum_vec_0 f : 
  ∑ v : 0, f v = f (Vector.nil _).
Proof.
  reflexivity.
Qed.

Lemma csum_vec_app {n m} f : 
  ∑ v : n + m, f v = 
  ∑ v : n, ∑ u : m, f (v ++ u)%vector.
Proof.
  induction n; [reflexivity|].
  change (S n + m) with (S (n + m)).
  rewrite 2!csum_vec_succ.
  setoid_rewrite IHn.
  reflexivity.
Qed.

Lemma csum_vec_comm {n m} f :
  (∑ v : n, ∑ u : m, f v u) = 
  ∑ u : m, ∑ v : n, f v u.
Proof.
  induction n; [reflexivity|].
  rewrite csum_vec_succ.
  setoid_rewrite IHn.
  rewrite csum_vec_comm1.
  setoid_rewrite csum_vec_succ.
  reflexivity.
Qed.

Lemma csum_vec_1 f : 
  ∑ v : 1, f v = 
  ∑ v, f [v]%vector.
Proof.
  reflexivity.
Qed.

Lemma csum_vec_rev {n} f : 
  ∑ v : n, f (Vector.rev v) = 
  ∑ v : n, f v.
Proof.
  induction n.
  - rewrite 2!csum_vec_eq_bigsum.
    cbn.
    rewrite Vector.rev_nil.
    reflexivity.
  - rewrite csum_vec_succ.
    rewrite (csum_cast (Nat.add_comm n 1 : n + 1 = S n)).
    rewrite csum_vec_app.
    rewrite csum_vec_comm.
    rewrite csum_vec_1.
    setoid_rewrite <- IHn at 1.
    apply csum_ext; intros b.
    apply csum_ext; intros v.
    f_equal.
    apply Vector.to_list_inj.
    rewrite to_list_cast, Vector.to_list_append,
      Vector.to_list_rev, 2!Vector.to_list_cons, 
      Vector.to_list_rev, Vector.to_list_nil.
    simpl.
    rewrite rev_involutive.
    reflexivity.
Qed.

Lemma matrix_of_tensor_of_matrix {n m} (A : Matrix (2^n) (2^m)) : 
  matrix_of_tensor (tensor_of_matrix A) ≡ A.
Proof.
  unfold matrix_of_tensor, tensor_of_matrix.
  rewrite make_WF_equiv.
  intros i j Hi Hj.
  rewrite 2!Vector.rev_rev.
  now rewrite 2!nat_to_bits_to_nat by auto.
Qed.

Lemma tensor_of_matrix_of_tensor {n m} (t : AbsTensor n m) : 
  tensor_of_matrix (matrix_of_tensor t) = t.
Proof.
  unfold matrix_of_tensor, tensor_of_matrix.
  prep_matrix_equality.
  rewrite make_WF_equiv by apply funbool_to_nat_bound.
  now rewrite 2!bits_to_nat_to_bits, 2!Vector.rev_rev.
Qed.

Lemma tensor_of_matrix_inj {n m} (A B : Matrix (2^m) (2^n)) : 
  tensor_of_matrix A = tensor_of_matrix B -> 
  A ≡ B.
Proof.
  intros HAB%(f_equal matrix_of_tensor).
  rewrite <- matrix_of_tensor_of_matrix.
  rewrite HAB.
  rewrite matrix_of_tensor_of_matrix.
  reflexivity.
Qed.

Lemma matrix_of_tensor_inj {n m} (t s : AbsTensor n m) : 
  matrix_of_tensor t ≡ matrix_of_tensor s -> 
  t = s.
Proof.
  intros HAB.
  rewrite <- tensor_of_matrix_of_tensor.
  rewrite <- HAB.
  rewrite tensor_of_matrix_of_tensor.
  reflexivity.
Qed.

Lemma matrix_of_tensor_compose {n m o} (t : AbsTensor n m) (s : AbsTensor m o) : 
  matrix_of_tensor (compose_tensor t s) =
  matrix_of_tensor s × matrix_of_tensor t.
Proof.
  prep_matrix_equivalence.
  intros i k Hi Hk.
  unfold Mmult, matrix_of_tensor.
  unfold make_WF.
  bdestruct_one; [|lia].
  bdestruct_one; [|lia].
  simpl.
  unfold compose_tensor.
  rewrite <- csum_vec_rev.
  rewrite csum_vec_eq_bigsum.
  apply big_sum_eq_bounded.
  intros j Hj.
  bdestruct_one; [|lia].
  simpl.
  apply Cmult_comm.
Qed.

Lemma matrix_of_tensor_stack {n0 m0 n1 m1} 
  (t : AbsTensor n0 m0) (s : AbsTensor n1 m1) : 
  matrix_of_tensor (stack_tensor t s) =
  matrix_of_tensor t ⊗ matrix_of_tensor s.
Proof.
  prep_matrix_equivalence.
  intros i k Hi Hk.
  unfold stack_tensor, matrix_of_tensor, kron.
  rewrite 3!make_WF_equiv by show_moddy_lt.
  rewrite <- (cast_nat_to_bits (Nat.add_comm n1 n0)), 
    <- (cast_nat_to_bits (Nat.add_comm m1 m0)).
  rewrite 2!rev_cast.
  rewrite 2!nat_to_bits_plus.
  rewrite 2!rev_append.
  rewrite 2!cast_cast, 2!cast_refl.
  rewrite 2!Vector.splitat_append.
  f_equal.
  f_equal; f_equal; apply nat_to_bits_eq_of_mod.
Qed.

(* FIXME: Move *)
Lemma rev_inj {A n} (v u : Vector.t A n) : 
  Vector.rev v = Vector.rev u <-> v = u.
Proof.
  split; [|now intros ->].
  intros Heq%(f_equal Vector.rev).
  rewrite 2!Vector.rev_rev in Heq.
  apply Heq.
Qed.


Lemma matrix_of_tensor_id n : 
  matrix_of_tensor (id_tensor n) = I (2 ^ n).
Proof.
  prep_matrix_equivalence.
  intros i j Hi Hj.
  unfold matrix_of_tensor, id_tensor.
  rewrite make_WF_equiv by easy.
  apply f_equal_if; [|easy..].
  replace_bool_lia (i <? 2 ^ n) true.
  rewrite andb_true_r.
  apply Bool.eq_iff_eq_true.
  rewrite Nat.eqb_eq.
  rewrite Vector.eqb_eq by (apply Bool.eqb_true_iff).
  rewrite rev_inj.
  rewrite nat_to_bits_inj by easy.
  easy.
Qed.

Import Quantum. 

Definition plus_n_O' : forall n, n = (n + 0)%nat :=
  let fix go n : n = (n + 0)%nat :=
  match n with 
  | 0 => eq_refl
  | S n' => f_equal S (go n')
  end in 
  go.

Definition plus_n_S' : forall n, S n = (n + 1)%nat :=
  let fix go n : S n = (n + 1)%nat :=
  match n with 
  | 0 => eq_refl
  | S n' => f_equal S (go n')
  end in 
  go.

Definition rev' {A n} (v : Vector.t A n) : Vector.t A n :=
  let fix go {n} v :=
  match v with 
  | []%vector => []%vector
  | (a :: v)%vector => 
    eq_rect_r _ (go v ++ [a]%vector)%vector (plus_n_S' _)
  end in 
  go v.

Lemma cast_eq_eq_rect {A n m} (v : Vector.t A m) (H : m = n) : 
  Vector.cast v H = eq_rect _ (Vector.t A) v _ H.
Proof.
  subst.
  rewrite cast_refl.
  reflexivity.
Qed.


Lemma rev_eq_rev' {A n} (v : Vector.t A n) :
  Vector.rev v = rev' v.
Proof.
  induction v.
  - rewrite Vector.rev_nil.
    reflexivity.
  - rewrite (ZXsum.rev_append [h]%vector v : Vector.rev (h :: v)%vector = _).
    rewrite cast_eq_eq_rect.
    simpl.
    unfold eq_rect_r.
    f_equal; [|apply Peano_dec.UIP_nat].
    rewrite Vector.rev_cons, Vector.rev_nil.
    simpl.
    rewrite IHv.
    reflexivity.
Qed.

Lemma matrix_of_tensor_to_compute {n m} (t : AbsTensor n m) : 
  matrix_of_tensor t ≡
  fun i j => t (rev' (nat_to_bits n j)) (rev' (nat_to_bits m i)).
Proof.
  unfold matrix_of_tensor.
  rewrite make_WF_equiv.
  intros i j _ _.
  rewrite 2!rev_eq_rev'.
  reflexivity.
Qed.


Lemma matrix_of_tensor_swap : 
  matrix_of_tensor swap_tensor = swap.
Proof.
  prep_matrix_equivalence.
  rewrite matrix_of_tensor_to_compute.
  by_cell; reflexivity.
Qed.

Lemma matrix_of_tensor_cap : 
  matrix_of_tensor cap_tensor = list2D_to_matrix [[C1; C0; C0; C1]].
Proof.
  apply mat_equiv_eq;
    [auto_wf | apply show_WF_list2D_to_matrix; reflexivity |].
  rewrite matrix_of_tensor_to_compute.
  by_cell; reflexivity.
Qed.

Lemma matrix_of_tensor_cup : 
  matrix_of_tensor cup_tensor = list2D_to_matrix [[C1]; [C0]; [C0]; [C1]].
Proof.
  apply mat_equiv_eq;
    [auto_wf | apply show_WF_list2D_to_matrix; reflexivity |].
  rewrite matrix_of_tensor_to_compute.
  by_cell; reflexivity.
Qed.

Lemma matrix_of_tensor_H : 
  matrix_of_tensor H_tensor = hadamard.
Proof.
  prep_matrix_equivalence.
  rewrite matrix_of_tensor_to_compute.
  by_cell; [reflexivity..|].
  symmetry; apply Copp_mult_distr_l.
Qed.

Lemma matrix_of_stack_tensors_1 n (t : AbsTensor 1 1) : 
  matrix_of_tensor (stack_tensors_1 n t) = kron_n n (matrix_of_tensor t).
Proof.
  induction n; [apply matrix_of_tensor_id|].
  rewrite kron_n_assoc by auto_wf.
  cbn -[Nat.add].
  rewrite (@matrix_of_tensor_stack 1 1 n n).
  rewrite IHn.
  reflexivity.
Qed.



From VyZX Require Import CoreData.

Lemma Z_semantics_alt n m α i j : 
  Z_semantics n m α i j = 
  (if (i =? 0) && (j =? 0) then C1 else C0) + 
  (if (i =? 2 ^ m - 1) && (j =? 2 ^ n - 1) then Cexp α else C0).
Proof.
  unfold Z_semantics.
  destruct i; [destruct j; [destruct n; [destruct m|]|]|].
  - reflexivity.
  - pose proof (pow_positive 2 m ltac:(easy)).
    cbn [Nat.pow].
    replace_bool_lia (0 =? 2 * 2 ^ m - 1) false.
    lca.
  - pose proof (pow_positive 2 n ltac:(easy)).
    cbn [Nat.pow].
    replace_bool_lia (0 =? 2 * 2 ^ n - 1) false.
    rewrite andb_false_r.
    lca.
  - rewrite andb_false_r, Cplus_0_l.
    reflexivity.
  - rewrite andb_false_l, Cplus_0_l.
    reflexivity.
Qed.

(* FIXME: Move *)
Lemma allb_iff_eq_const {n} (v : Vector.t bool n) b : 
  allb b v = true <-> v = Vector.const b n.
Proof.
  induction v.
  - simpl.
    split; reflexivity.
  - simpl.
    rewrite andb_true_iff.
    rewrite Bool.eqb_true_iff, IHv.
    split; [intros []; congruence|intros ?%Vector.cons_inj; easy].
Qed.

(* FIXME: Move *) 
Lemma rev_const {A n} (a : A) :
  Vector.rev (Vector.const a n) = Vector.const a n.
Proof.
  apply Vector.to_list_inj.
  rewrite Vector.to_list_rev, Vector.to_list_const.
  rewrite rev_repeat.
  reflexivity.
Qed.

Lemma allb_rev {n} (v : Vector.t bool n) b : 
  allb b (Vector.rev v) = allb b v.
Proof.
  apply Bool.eq_iff_eq_true.
  rewrite 2!allb_iff_eq_const.
  split.
  - intros H%(f_equal Vector.rev).
    rewrite Vector.rev_rev, rev_const in H.
    auto.
  - intros ->.
    rewrite rev_const.
    reflexivity.
Qed.  

Lemma allb_false_nat_to_bits n i : (i < 2 ^ n)%nat -> 
  allb false (nat_to_bits n i) = (i =? 0).
Proof.
  intros Hi.
  apply Bool.eq_iff_eq_true.
  rewrite Nat.eqb_eq.
  rewrite allb_iff_eq_const.
  split.
  - intros Heq.
    apply Nat.bits_inj.
    intros k.
    rewrite Nat.bits_0.
    bdestruct (k <? n).
    + assert (Hk : (k < n)%nat) by assumption.
      apply (f_equal (fun m => Vector.nth m (Fin.of_nat_lt Hk))) in Heq.
      rewrite nth_nat_to_bits in Heq.
      rewrite fin.fin_to_nat_to_fin in Heq.
      rewrite Vector.const_nth in Heq.
      rewrite Heq.
      reflexivity.
    + replace i with (i mod 2 ^ n) by (apply Nat.mod_small; auto).
      rewrite Nat.mod_pow2_bits_high by easy.
      reflexivity.
  - intros ->.
    apply Vector.eq_nth_iff.
    intros p _ <-.
    rewrite nth_nat_to_bits, Vector.const_nth.
    rewrite Nat.bits_0.
    reflexivity.
Qed.

(* FIXME: Move *)
Lemma testbit_pow_2_sub_1 n k : 
  Nat.testbit (2 ^ n - 1) k = (k <? n).
Proof.
  revert k.
  induction n.
  - apply Nat.bits_0.
  - intros [|k].
    + cbn -[Nat.pow].
      rewrite Nat.odd_sub by (apply pow_positive; lia).
      rewrite Nat.odd_pow by easy.
      reflexivity.
    + cbn [Nat.testbit].
      rewrite Nat.div2_div.
      change (?x = _) with (x = (k <? n)).
      rewrite <- IHn.
      f_equal.
      cbn [Nat.pow].
      rewrite Nat.mul_comm.
      rewrite div_sub by easy.
      rewrite Nat.sub_0_r.
      reflexivity.
Qed.


Lemma allb_true_nat_to_bits n i : (i < 2 ^ n)%nat -> 
  allb true (nat_to_bits n i) = (i =? 2 ^ n - 1).
Proof.
  intros Hi.
  apply Bool.eq_iff_eq_true.
  rewrite Nat.eqb_eq.
  rewrite allb_iff_eq_const.
  split.
  - intros Heq.
    apply (f_equal Vector.to_list) in Heq.
    rewrite nat_to_bits_to_list in Heq by easy.
    rewrite Vector.to_list_const in Heq.
    apply (f_equal binlist_to_nat) in Heq.
    rewrite nat_to_binlist_inverse in Heq.
    rewrite Heq.
    apply binlist_to_nat_true.
  - intros ->.
    apply Vector.eq_nth_iff.
    intros p _ <-.
    rewrite nth_nat_to_bits.
    rewrite testbit_pow_2_sub_1.
    rewrite Vector.const_nth.
    apply Nat.ltb_lt.
    apply fin.fin_to_nat_lt.
Qed.


Lemma matrix_of_Z_tensor n m α : 
  matrix_of_tensor (Z_tensor n m α) = 
  Z_semantics n m α.
Proof.
  prep_matrix_equivalence.
  unfold matrix_of_tensor, Z_tensor.
  rewrite make_WF_equiv.
  intros i j Hi Hj.
  unfold zsp.
  rewrite Z_semantics_alt.
  f_equal.
  - apply f_equal_if; [|reflexivity..].
    rewrite allb_append, 2!allb_rev.
    rewrite 2!allb_false_nat_to_bits by easy.
    apply andb_comm.
  - apply f_equal_if; [|reflexivity..].
    rewrite allb_append, 2!allb_rev.
    rewrite 2!allb_true_nat_to_bits by easy.
    apply andb_comm.
Qed.

Lemma matrix_of_X_tensor n m α : 
  matrix_of_tensor (X_tensor n m α) = 
  X_semantics n m α.
Proof.
  unfold X_tensor.
  rewrite 2!matrix_of_tensor_compose.
  rewrite 2!matrix_of_stack_tensors_1.
  rewrite matrix_of_Z_tensor.
  rewrite matrix_of_tensor_H.
  rewrite <- Mmult_assoc.
  reflexivity.
Qed.


Fixpoint tensor_of_ZX {n m} (zx : ZX n m) : AbsTensor n m :=
  match zx with
  | Empty => id_tensor 0
  | Cup => cup_tensor
  | Cap => cap_tensor
  | Swap => swap_tensor
  | Wire => id_tensor 1
  | Box => H_tensor
  | X n m α => X_tensor n m α
  | Z n m α => Z_tensor n m α
  | Stack zx0 zx1 => stack_tensor (tensor_of_ZX zx0) (tensor_of_ZX zx1)
  | Compose zx0 zx1 => compose_tensor (tensor_of_ZX zx0) (tensor_of_ZX zx1)
  end.

Lemma matrix_of_tensor_of_ZX {n m} (zx : ZX n m) : 
  matrix_of_tensor (tensor_of_ZX zx) = ZX_semantics zx.
Proof.
  induction zx.
  - apply matrix_of_tensor_id.
  - apply matrix_of_tensor_cup.
  - apply matrix_of_tensor_cap.
  - apply matrix_of_tensor_swap.
  - apply matrix_of_tensor_id.
  - apply matrix_of_tensor_H.
  - apply matrix_of_X_tensor.
  - apply matrix_of_Z_tensor.
  - cbn [tensor_of_ZX ZX_semantics].
    rewrite matrix_of_tensor_stack.
    congruence.
  - cbn [tensor_of_ZX ZX_semantics].
    rewrite matrix_of_tensor_compose.
    congruence.
Qed.







(* Definition transpose  *)



  