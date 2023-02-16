(****** Formalizing certain properties from combinatorics ***************)
Require Import Reals Psatz.
Require Import Omega Init.Nat Arith.EqNat.
Require Import Coq.Arith.PeanoNat Coq.Structures.Equalities.

Open Scope R_scope.

Definition nchoosek (n k: nat) : R := INR (fact n) / (INR (fact k) * INR (fact (n-k))).


Lemma nplus1cr: forall (r n :nat), (r <=n)%nat -> nchoosek (n+1) r = (INR (n+1) * (/ INR (n-r+1))) * nchoosek n r.
Proof.
intros.
unfold nchoosek.
assert ( fact (n+1)= ((n+1)%nat * fact n)%nat). 
{ assert (S n = (n+1)%nat). { omega. }rewrite <-H0. apply fact_simpl. } rewrite H0.
assert ( fact (n + 1 - r)= ((n-r+1)%nat * fact (n-r))%nat).
{ assert ((n + 1 - r)%nat = S (n-r)). { omega. } rewrite H1. 
  assert ((n - r + 1)%nat = S (n-r)). { omega. } rewrite H2. apply fact_simpl.
} rewrite H1.
assert (INR ((n + 1) * fact n) = INR (n+1) * INR (fact n)). { apply mult_INR. } rewrite H2.
assert (INR ((n - r + 1) * fact (n - r))= INR (n-r+1) * INR (fact (n-r))). { apply mult_INR. } rewrite H3. 
assert (INR (fact n) / (INR (fact r) * INR (fact (n - r)))= INR (fact n) * (/ INR (fact r)) * (/INR (fact (n - r)))).
{ assert (/ (INR (fact r) * INR (fact (n - r)))=(/ INR (fact r)) * (/INR (fact (n - r)))).
  { apply Rinv_mult_distr. apply INR_fact_neq_0. apply INR_fact_neq_0. }
  assert (INR (fact n) / (INR (fact r) * INR (fact (n - r)))= INR (fact n) * (/ (INR (fact r) * INR (fact (n - r))))). { nra. } rewrite H5.
  rewrite H4. nra.
} rewrite H4.
assert (INR (n + 1) * / INR (n - r + 1) * (INR (fact n) * / INR (fact r) * / INR (fact (n - r)))=
          (INR (n + 1) * INR (fact n) ) * (/ INR (fact r) *  / INR (n - r + 1) * / INR (fact (n - r)))). { nra. } rewrite H5.
assert (INR (n + 1) * INR (fact n) / (INR (fact r) * (INR (n - r + 1) * INR (fact (n - r))))=
          (INR (n + 1) * INR (fact n)) * (/ (INR (fact r) * (INR (n - r + 1) * INR (fact (n - r)))))). { nra. } rewrite H6.
assert (/ (INR (fact r) * (INR (n - r + 1) * INR (fact (n - r))))=(/ INR (fact r) * / INR (n - r + 1) * / INR (fact (n - r)))).
{ assert (/ (INR (fact r) * (INR (n - r + 1) * INR (fact (n - r)))) = (/INR (fact r)) * (/ (INR (n - r + 1) * INR (fact (n - r))))). 
  { apply Rinv_mult_distr. apply INR_fact_neq_0. rewrite <-H3. rewrite <-H1. apply INR_fact_neq_0. } rewrite H7.
  assert ( / (INR (n - r + 1) * INR (fact (n - r))) = (/ INR (n - r + 1) ) * (/  INR (fact (n - r)))). 
  { apply Rinv_mult_distr. 
    assert ( 0< INR (n - r + 1) -> INR (n - r + 1) <> 0). { nra. } apply H8. apply lt_0_INR. omega. apply INR_fact_neq_0. } rewrite H8. nra. 
} rewrite H7. nra.
Qed.

Lemma comb_prop_1: forall (n:nat), nchoosek n 0%nat= 1.
Proof.
intros.
assert (n=0%nat \/ (0<n)%nat). { omega. } destruct H.
+ rewrite H.
  unfold nchoosek.
  assert ( (0-0)%nat = 0%nat). { omega. } rewrite H0.
  assert (fact 0=1%nat). { auto. } rewrite H1.
  assert (INR 1=1). { reflexivity. }rewrite H2. nra.
+ unfold nchoosek.
  assert ((n - 0)%nat=n). { omega. } rewrite H0.
  assert (fact 0=1%nat). { auto. }rewrite H1.
  assert (INR 1=1). { reflexivity. }rewrite H2. 
  assert ((1 * INR (fact n))=INR (fact n)). { nra. } rewrite H3.
  assert (INR (fact n) / INR (fact n)= INR (fact n) * (/ INR (fact n))). { nra. }rewrite H4.
  apply Rinv_r. assert ( 0< INR (fact n) -> INR (fact n) <> 0). { nra. }  apply H5. 
  apply lt_0_INR. apply lt_O_fact. 
Qed.


Lemma comb_prop_2: forall (n:nat), (1<=n)%nat -> nchoosek n 1%nat=INR n.
Proof.
intros.
unfold nchoosek.
assert ((fact 1)=1%nat). { auto. } rewrite H0. assert (INR 1=1). { reflexivity. }rewrite H1.
assert (1 * INR (fact (n - 1))= INR (fact (n - 1))). { nra. } rewrite H2.
assert ( fact n = (n* fact (n-1))%nat).
{ induction n.
  + contradict H1. omega. 
  + assert ((S n - 1)%nat = n). { omega. }rewrite H3.
    auto.
} rewrite H3. 
assert (INR (n * fact (n - 1))= INR n * INR (fact(n-1)) ). { apply mult_INR. } rewrite H4.
assert (INR n * INR (fact (n - 1)) / INR (fact (n - 1))= INR n * (INR (fact (n - 1)) * (/INR (fact (n - 1))))). { nra. }rewrite H5.
assert ((INR (fact (n - 1)) * / INR (fact (n - 1)))=1). { apply Rinv_r. assert ( 0< INR (fact (n - 1)) -> INR (fact (n - 1)) <> 0). { nra. } apply H6.
apply lt_0_INR. apply lt_O_fact. } rewrite H6. nra.
Qed. 

