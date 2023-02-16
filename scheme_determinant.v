(** Proving that the determinant Mk <> 0 for the example problem *)
Require Import Reals Psatz.
Require Import Coquelicot.Hierarchy.
Require Import Omega Init.Nat Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import combinatorics.
Require Import Arith.Even Div2.
Require Import Ah_inverse.

Lemma Mk_0: Mk 0%nat (-2) = 1.
Proof.
unfold Mk. simpl. unfold sum_n.
assert (sum_n_m (fun i : nat => det_func (-2) 0 i) 0 0=(fun i : nat => det_func (-2) 0 i) 0%nat).
{ apply (sum_n_n (fun i : nat => det_func (-2) 0 i) 0%nat). } rewrite H.
unfold det_func. simpl.
assert (nchoosek 0 0 =1). { apply comb_prop_1. } rewrite H0. nra.
Qed.


Lemma Mk_1: Mk 1%nat (-2) = -2.
Proof.
unfold Mk. simpl. unfold sum_n.
assert (sum_n_m (fun i : nat => det_func (-2) 1 i) 0 0 =(fun i : nat => det_func (-2) 1 i) 0%nat).
{ apply (sum_n_n (fun i : nat => det_func (-2) 1 i) 0%nat). } rewrite H.
unfold det_func. simpl.
assert ( nchoosek 1 0=1). { apply comb_prop_1. }rewrite H0. nra.
Qed.

Lemma Mk_2: Mk 2 (-2) =3.
Proof.
unfold Mk. simpl. unfold sum_n.
assert (sum_n_m (fun i : nat => det_func (-2) 2 i) 0 1 =sum_n_m (fun i : nat => det_func (-2) 2 i) 0%nat 0%nat +
          sum_n_m (fun i : nat => det_func (-2) 2 i) 1%nat 1%nat).
{ apply (sum_n_m_Chasles (fun i : nat => det_func (-2) 2 i) 0%nat 0%nat 1%nat). omega. omega. } rewrite H.
assert (sum_n_m (fun i : nat => det_func (-2) 2 i) 0 0=(fun i : nat => det_func (-2) 2 i) 0%nat).
{ apply (sum_n_n (fun i : nat => det_func (-2) 2 i) 0%nat). } rewrite H0.
assert (sum_n_m (fun i : nat => det_func (-2) 2 i) 1 1=(fun i : nat => det_func (-2) 2 i) 1%nat).
{ apply (sum_n_n (fun i : nat => det_func (-2) 2 i) 1%nat). } rewrite H1.
unfold det_func. simpl.
assert (nchoosek 2 0=1). { apply comb_prop_1. } rewrite H2.
assert (nchoosek 1 1=1). { apply comb_prop_2. omega. } rewrite H3.
nra.
Qed.


Lemma Mk_3: Mk 3 (-2) = -4.
Proof.
unfold Mk. simpl. unfold sum_n.
assert (sum_n_m (fun i : nat => det_func (-2) 3 i) 0 1=sum_n_m (fun i : nat => det_func (-2) 3 i) 0%nat 0%nat + 
          sum_n_m (fun i : nat => det_func (-2) 3 i) 1%nat 1%nat).
{ apply (sum_n_m_Chasles (fun i : nat => det_func (-2) 3 i) 0%nat 0%nat 1%nat). omega. omega. } rewrite H.
assert (sum_n_m (fun i : nat => det_func (-2) 3 i) 0 0= (fun i : nat => det_func (-2) 3 i) 0%nat). 
{ apply (sum_n_n (fun i : nat => det_func (-2) 3 i) 0%nat). } rewrite H0.
assert (sum_n_m (fun i : nat => det_func (-2) 3 i) 1 1=(fun i : nat => det_func (-2) 3 i) 1%nat).
{ apply (sum_n_n (fun i : nat => det_func (-2) 3 i) 1%nat). } rewrite H1.
unfold det_func. simpl.
assert (nchoosek 3 0=1). { apply comb_prop_1. } rewrite H2.
assert ( nchoosek 2 1 =2). { apply comb_prop_2. omega. } rewrite H3.
nra.
Qed.

Require Import Coq.Program.Equality Coq.Init.Wf.


(* We used the code snippets for lemma/theorem le_s, strongind_aux, weaken and strongind from
    http://pldev.blogspot.com/2012/02/proving-strong-induction-principle-for.html
*)

Lemma le_S :
  forall n m : nat,
    (n <= S m)%nat -> (n <= m)%nat \/ n = S m.
Proof.
  intros.
  inversion H.
  right. reflexivity.
  left. assumption.
Qed.


Theorem strongind_aux :
 Mk 0%nat (-2) = (-1)^0%nat * (INR 0+1) -> 
  (forall n:nat, (forall m:nat, (m <= n)%nat -> Mk m (-2) = (-1)^m * (INR m +1)) ->  Mk (S n) (-2)= (-1)^(S n)* (INR (S n)+1)) ->
  forall n:nat, (forall m:nat, ((m <= n)%nat -> Mk m (-2) = (-1)^m * (INR m +1))).
Proof.
  induction n as [ | n' IHn' ].
    intros m H1.
    inversion H1.
    assumption.
    intros.
    assert ((m <= n')%nat \/ m = S n'). apply le_S. assumption.
    inversion H2.
    apply IHn'; assumption.
    rewrite H3.
    apply (H0 n'); assumption.
Qed.

Lemma weaken :
  (forall n:nat, (forall m:nat, ((m <= n)%nat -> Mk m (-2) = (-1)^m * (INR m +1)))) -> (forall n:nat, Mk n (-2) = (-1)^n * (INR n +1)).
Proof.
intros H n.
apply (H n n).
apply le_n.
Qed.


Theorem strong_ind: 
Mk 0%nat (-2) = (-1)^0%nat * (INR 0+1) ->
(forall n:nat, (forall m:nat, (m <= n)%nat -> Mk m (-2) = (-1)^m * (INR m +1)) -> Mk (S n) (-2)= (-1)^(S n)* (INR (S n)+1)) ->
  forall n:nat, Mk n (-2) = (-1)^n * (INR n +1).
Proof.
intros.
intros.
apply weaken.
apply strongind_aux;assumption.
Qed.


Lemma Mk_rec: forall k:nat, Mk k (-2) = (-1)^k * (INR k+1).
Proof.
apply strong_ind.
+ simpl. assert (Mk 0 (-2)=1). { apply Mk_0. } rewrite H. nra.
+ intros.
  assert ( (n<=1)%nat \/ (1<n)%nat). { omega. } destruct H0.
  - assert (n=0%nat \/ n=1%nat). { omega. } destruct H1.
    * rewrite H1. simpl. assert (Mk 1 (-2)=-2). { apply Mk_1. } rewrite H2. nra.
    * rewrite H1. simpl. assert (Mk 2 (-2) =3). { apply Mk_2. }rewrite H2. nra.
  - assert (INR (S n) + 1 = (2* (INR n +1) - INR n)).
  { assert (S n = (n+1)%nat). { omega. } rewrite H1.
    assert (INR (n + 1)=INR n + INR 1). { apply plus_INR. } rewrite H2.
    assert ( INR 1 = 1). { reflexivity. } rewrite H3. nra.
  } rewrite H1.
  assert ( S n = (n+1)%nat). { omega. }rewrite H2.
  assert ((-1) ^ (n + 1)= (-1)^ n * (-1)^1). { apply pow_add. } rewrite H3.
  assert ((-1) ^ n * (-1) ^ 1 * (2 * (INR n + 1) - INR n)= (-1) * ( 2*((-1)^n * (INR n +1)) - (-1)^n * INR n)).
  { nra. } rewrite H4.
  rewrite <-H.
  assert ((-1) ^ n * INR n= (-1) * ((-1)^(n-1)%nat * (INR (n-1) +1))).
  { assert (-1 * ((-1) ^ (n - 1) * (INR (n - 1) + 1))= ((-1)^(n-1)%nat * (-1)^1) * (INR (n-1) +1)). { nra. } rewrite H5.
    assert ((-1)^ ((n-1)+1)%nat = (-1)^ (n-1)%nat * (-1)^1). { apply pow_add. } rewrite <-H6.
    assert ((n - 1 + 1)%nat= n). { nia. } rewrite H7.
    assert (INR (n - 1)= INR n - INR 1). { apply minus_INR. nia. } rewrite H8.
    assert (INR 1=1). { reflexivity. } rewrite H9.  nra.
  } rewrite H5.  
  assert (Mk (n-1)%nat (-2) = (-1) ^ (n - 1) * (INR (n - 1) + 1)). { specialize (H (n-1)%nat).
  assert ((n - 1 <= n)%nat). { nia. } specialize (H H6). apply H. } rewrite <-H6.
  assert ((2 * Mk n (-2) - -1 * Mk (n - 1) (-2))=(2 * Mk n (-2) + Mk (n - 1) (-2))). { nra. } rewrite H7.
  assert (-1 * (2 * Mk n (-2) + Mk (n - 1) (-2))= -2 * Mk n (-2) - Mk (n-1)%nat (-2)). { nra. } rewrite H8.
  assert (n = ((n+1)-1)%nat). { nia. } 
  assert ( (n-1)%nat = ((n+1)-2)%nat). {  nia. } 
  assert (Mk n (-2)= Mk ((n+1)-1)%nat (-2)). { rewrite <-H9. reflexivity. } rewrite H11.
  assert (Mk (n - 1) (-2)= Mk ((n+1)-2)%nat (-2)).  { rewrite <-H10. reflexivity. } rewrite H12. apply Ah_inverse.Mk_recurr. nia.
Qed.

Lemma Mk_not_0: forall N:nat,  Mk N (-2) <> 0.
Proof.
intros.
assert (Mk N (-2) = (-1)^N * (INR N+1)). { apply Mk_rec. } rewrite H. 
apply Rmult_integral_contrapositive_currified. 
apply pow_nonzero. nra.
assert (INR (N+1)= INR N + INR 1). { apply plus_INR. } assert (INR 1 = 1). { reflexivity. } rewrite <-H1. rewrite <-H0.
assert ( 0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H2. apply lt_0_INR. omega.
Qed.

