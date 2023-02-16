(**** Verifying that Eh is the inverse of Ah using the definition. Eh * Ah = I & Ah* Eh = I ***)
(*** This definition of inverse is for a general symmetric tridiagonal matrix Ah (a, b,a). *****)


Require Import Reals Psatz.
Require Import Coquelicot.Hierarchy.
Require Import Omega Init.Nat Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import R_sqrt Rpower.
Require Import Ah_properties.
Require Import obvio_lemmas.
Require Import combinatorics.


Definition identity (N:nat) := mk_matrix N N (fun i j => 
                        if (eqb i j) then 1 else 0).

Definition invertible (N:nat) (A:matrix N N) (B:matrix N N):= Mmult B A = identity N /\ Mmult A B= identity N.

(* Combinatorics definition in Coq *)


Definition det_func (D:R) (k i:nat):= (-1)^i * (nchoosek (k-i) i)* (D^ (k-2*i)).

Definition Mk (N:nat) (D:R):= sum_n (fun i:nat => det_func D N i) (div2 N).

(** Defining inverse of a symmetric tridiagonal matrix **)
(** D= b/a **)
Definition inverse_A (N:nat) (a b:R):= mk_matrix N N (fun i j =>
          if (leb i j) then (1/a) *((-1)^(i+j))* ( (Mk i (b/a)) * (Mk (N-j-1)%nat (b/a)) */ (Mk N (b/a)))
            else (1/a)* ((-1)^(i+j))* ( (Mk j (b/a)) * (Mk (N-i-1)%nat (b/a))) */ (Mk N (b/a))).


Lemma det_func_Sk:forall (D:R) (i k :nat),  (0<(k - 2 * i))%nat ->det_func D (S k) i = D* (INR ((k-i)+1) * (/ INR ((k-i)-i+1))) * det_func D k i.
Proof.
intros.
unfold det_func.
  assert (D ^ (S k - 2 * i)= D* D ^ (k - 2 * i)).
  { assert (D* D ^ (k - 2 * i)= D ^ 1 *D ^ (k - 2 * i)). { nra. } rewrite H0.
    assert ( D ^ (1+ (k - 2 * i))%nat = D ^ 1 *D ^ (k - 2 * i)). { apply pow_add. } rewrite <-H1.
    assert ((S k - 2 * i)%nat=(1 + (k - 2 * i))%nat). 
    { assert ((1 + (k - 2 * i))%nat=  ( 1 + k - 2*i)%nat). { omega. }rewrite H2. omega. } rewrite H2.
    nra.
  } rewrite H0. 
  assert ( nchoosek (S k - i) i =(INR ((k-i)+1) * (/ INR ((k-i)-i+1))) * nchoosek (k-i)%nat i). 
  { assert  ((S k - i)%nat = ((k-i)+1)%nat). { omega. } rewrite H1. apply nplus1cr. omega. } rewrite H1. nra.
Qed.


(* Defining the recurrence relation *)
Hypothesis Mk_recurr : forall (k:nat) (D:R), Mk k D = D * Mk (k-1)%nat D - Mk (k-2)%nat D.

(** Boundary conditions for Mk as stated in the reference paper [17] **)
Hypothesis Mk_B0 : forall (D:R), Mk 0 D =1.
Hypothesis Mk_B1: forall (D:R), Mk 1 D = D.

(****** Using the recurrence definition of the determinant Mk *********)

Lemma Mk_prop_1(a b:R): forall (j N:nat), (2<N)%nat-> (0<j)%nat -> 
  (-1) ^ pred j * Mk (N - pred j) (b/a) + (-1) ^ j * (b/a) * Mk (N - j) (b/a) +(-1) ^ S j * Mk (N - S j) (b/a)=0.
Proof.
intros.
assert ( j =((pred j)+1)%nat). { omega. } 
assert (S j = ((pred j)+2)%nat). { omega. }
assert ((-1) ^ j= (-1)^ (pred j) * (-1)^1). { assert ( (-1)^j = (-1)^ ((pred j)+1)%nat). { rewrite <-H1. reflexivity. } rewrite H3. apply pow_add. }
assert ((-1) ^ S j = (-1)^ (pred j) * (-1)^2). { assert ((-1) ^ S j=(-1)^ ((pred j)+2)%nat). { rewrite <-H2. reflexivity. } rewrite H4. apply pow_add. } rewrite H4. rewrite H3.
assert ((-1) ^ pred j * Mk (N - pred j) (b/a) +(-1) ^ pred j * (-1) ^ 1 * (b/a) * Mk (N - j) (b/a) +(-1) ^ pred j * (-1) ^ 2 * Mk (N - S j) (b/a)=
          (-1)^(pred j) * ( Mk (N - pred j) (b/a) + (-b/a)*  Mk (N - j) (b/a)+Mk (N - S j) (b/a))). { nra. } rewrite H5.
assert ((Mk (N - pred j) (b/a) + (-b/a) * Mk (N - j) (b/a) + Mk (N - S j) (b/a)) = 0).
{ assert ((N - j)%nat = ((N - pred j)-1)%nat). { nia. } rewrite H6.
  assert ((N - S j)%nat = ((N - pred j)-2)%nat). { nia. }rewrite H7.
  assert (Mk (N - pred j) (b/a) = (b/a)*Mk (N - pred j - 1) (b/a) - Mk (N - pred j - 2) (b/a) ->Mk (N - pred j) (b/a) + (-b/a) * Mk (N - pred j - 1) (b/a) +Mk (N - pred j - 2) (b/a) = 0). { nra. }
  apply H8. apply Mk_recurr.
} rewrite H6. nra.
Qed. 

Lemma Mk_prop_2 (a b:R):forall (j: nat),(0<j)%nat -> (-1) ^ pred j * Mk (pred j) (b/a) + (-1) ^ j * (b/a) * Mk j (b/a) +(-1) ^ S j * Mk (S j) (b/a) = 0.
Proof.
intros.
assert ( j =((pred j)+1)%nat). { omega. } 
assert (S j = ((pred j)+2)%nat). { omega. }
assert ((-1) ^ j= (-1)^ (pred j) * (-1)^1). { assert ( (-1)^j = (-1)^ ((pred j)+1)%nat). { rewrite <-H0. reflexivity. } rewrite H2. apply pow_add. }
assert ((-1) ^ S j = (-1)^ (pred j) * (-1)^2). { assert ((-1) ^ S j=(-1)^ ((pred j)+2)%nat). { 
rewrite <-H1. reflexivity. } rewrite H3. apply pow_add. } rewrite H2. rewrite H3.
assert ((-1) ^ pred j * Mk (pred j) (b/a) +(-1) ^ pred j * (-1) ^ 1 * (b/a) * Mk j (b/a) +(-1) ^ pred j * (-1) ^ 2 * Mk (S j) (b/a)=
        (-1)^ (pred j) * (Mk (pred j) (b/a) + (-b/a)* Mk j (b/a) + Mk (S j) (b/a))). { nra. } rewrite H4.
assert (Mk (pred j) (b/a) + (-b/a) * Mk j (b/a) + Mk (S j) (b/a)=0).
{ assert ( (S j) = (j+1)%nat). { nia. }rewrite H5.
  assert (Mk j (b/a)= Mk ((j+1)-1)%nat (b/a)). { assert ((j + 1 - 1)%nat =j). { nia. } rewrite H6. reflexivity. } rewrite H6.
  assert (Mk (pred j) (b/a)= Mk ((j+1)-2)%nat (b/a)). { assert ((j + 1 - 2)%nat = pred j). { nia. } rewrite H7. reflexivity. } rewrite H7.
  assert (Mk (j + 1) (b/a)= (b/a) *  Mk (j + 1 - 1) (b/a) - Mk (j + 1 - 2) (b/a) -> 
                Mk (j + 1 - 2) (b/a) + (-b/a) * Mk (j + 1 - 1) (b/a) + Mk (j + 1) (b/a) = 0). { nra. } apply H8. apply Mk_recurr.
} rewrite H5. nra.
Qed.


(************************** Verification of the inverse starts here ********************************)



Lemma Ah_prop_1 (a b:R): forall (i j N:nat), (N=3)%nat -> (i<N)%nat -> j = 1%nat->  0<a -> sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0
        l)
     (coeff_mat Hierarchy.zero (Ah 3 a b a) l j)) 0
  2 = 0.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a) l j)) 0 2= sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 0%nat 0%nat + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 1%nat 2%nat).
{ apply (sum_n_m_Chasles    (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 0%nat 0%nat 2%nat). omega. omega. }
rewrite H3.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 1 2=sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 1%nat 1%nat + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 2%nat 2%nat).
{ apply (sum_n_m_Chasles    (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 1%nat 1%nat 2%nat). omega. omega. }
rewrite H4.
assert (sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
     (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 0 0 +
(sum_n_m
   (fun l : nat =>
    mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
      (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 1 1 +
 sum_n_m
   (fun l : nat =>
    mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
      (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 2 2)=sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
     (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 0 0 +
sum_n_m
   (fun l : nat =>
    mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
      (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 1 1 +
 sum_n_m
   (fun l : nat =>
    mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
      (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 2 2). { nra. } rewrite H5.
assert (sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
     (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 0 0= (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
     (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 0%nat).
{ apply (sum_n_n  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
     (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j))). } rewrite H6.
assert (sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
     (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 1 1 = (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
     (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 1%nat).
{ apply (sum_n_n (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
     (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 1%nat). } rewrite H7.
assert (sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
     (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 2 2= (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
     (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 2%nat).
{ apply (sum_n_n (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 0 l)
     (coeff_mat Hierarchy.zero (Ah  3 a b a ) l j)) 2%nat). } rewrite H8.
unfold Ah.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0)) 0 j=(fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 0%nat j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 0%nat j). omega. omega. } rewrite H9.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0)) 1 j=(fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 1%nat j).
{ apply (coeff_mat_bij Hierarchy.zero(fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 1%nat j). omega. omega. } rewrite H10.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0)) 2 j=(fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 2%nat j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 2%nat j). omega. omega. } rewrite H11.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
      (mk_matrix 3 3
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (3 - j0 - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (3 - i0 - 1) (b / a)) *
          / Mk 3 (b / a))) 0 0=(fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (3 - j0 - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (3 - i0 - 1) (b / a)) *
          / Mk 3 (b / a)) 0%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (3 - j0 - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (3 - i0 - 1) (b / a)) *
          / Mk 3 (b / a)) 0 0). omega. omega. } rewrite H12.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (3 - j0 - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (3 - i0 - 1) (b / a)) *
          / Mk 3 (b / a))) 0 1= (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (3 - j0 - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (3 - i0 - 1) (b / a)) *
          / Mk 3 (b / a)) 0%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero(fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (3 - j0 - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (3 - i0 - 1) (b / a)) *
          / Mk 3 (b / a)) 0 1). omega. omega. } rewrite H13.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (3 - j0 - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (3 - i0 - 1) (b / a)) *
          / Mk 3 (b / a))) 0 2= (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (3 - j0 - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (3 - i0 - 1) (b / a)) *
          / Mk 3 (b / a)) 0%nat 2%nat).
{ apply (coeff_mat_bij  Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (3 - j0 - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (3 - i0 - 1) (b / a)) *
          / Mk 3 (b / a)) 0 2). omega. omega. } rewrite H14.
assert (0 <=? 0=true). { apply leb_correct. omega. } rewrite H15.
assert ( 0 <=? 1= true). { apply leb_correct. omega. } rewrite H16.
assert (0 <=? 2=true). { apply leb_correct. omega. } rewrite H17.
assert ( 0 =? j=false). { assert ((0 =? j) = false <-> 0%nat <> j). { apply beq_nat_false_iff. } destruct H18. apply H19. omega. } rewrite H18.
assert ( 0 - j =? one=false). { assert ((0 - j =? one) = false <->(0-j)%nat <> one). { apply beq_nat_false_iff. } destruct H19. apply H20.
assert ((0 - j)%nat =0%nat). { apply obvio_2. omega. } rewrite H21. discriminate. } rewrite H19.
assert (j - 0 =? one =true). { rewrite H1. auto. } rewrite H20.
assert (1 =? j=true). { rewrite H1. auto. } rewrite H21.
assert (2 =? j=false). { assert ((2 =? j) = false <-> 2%nat <> j). { apply beq_nat_false_iff. } destruct H22. apply H23. omega. } rewrite H22.
assert (2 - j =? one=true). { rewrite H1. auto. } rewrite H23. 
assert ((-1) ^ (0 + 0)= 1). { assert ((0 + 0)%nat = 0%nat). { omega. } rewrite H24. nra. } rewrite H24.
assert ((3 - 0-1)%nat = 2%nat). { omega. } rewrite H25.
assert ((-1) ^ (0 + 1) = -1). { assert ((0 + 1)%nat = 1%nat). { omega. } rewrite H26. nra. } rewrite H26.
assert ((3 - 1-1)%nat = 1%nat). { omega. }rewrite H27.
assert ((3 - 2 - 1)%nat = 0%nat). { omega. } rewrite H28.
assert ((-1) ^ (0 + 2)=1). { assert ((0 + 2)%nat = 2%nat). { omega. } rewrite H29. nra. } rewrite H29.
assert (mult (1/a * 1 * (Mk 0 (b/a) * Mk 2 (b/a) * / Mk 3 (b/a)))  a=
          (1/a * 1 * (Mk 0 (b/a) * Mk 2 (b/a) * / Mk 3 (b/a))) * a). { reflexivity. } rewrite H30.
assert (1/a * 1 * (Mk 0 (b/a) * Mk 2 (b/a) * / Mk 3 (b/a)) *a =
          (/a  * a)*  (Mk 0 (b/a)) * (Mk 2 (b/a) * (/ Mk 3 (b/a)))). { nra. }rewrite H31.
assert (mult  ((1/a) * -1 * (Mk 0 (b/a) * Mk 1 (b/a) * / Mk 3 (b/a)))  b=
          (1/a * -1 * (Mk 0 (b/a) * Mk 1 (b/a) * / Mk 3 (b/a))) * b). { reflexivity. } rewrite H32.
assert (1/a * -1 * (Mk 0 (b/a) * Mk 1 (b/a) * / Mk 3 (b/a)) *b=
          (-1*( b/a)*  (Mk 0 (b/a))) * ( Mk 1 (b/a) * (/ Mk 3 (b/a)))). { nra. } rewrite H33.
assert (mult (1/a * 1 * (Mk 0 (b/a) * Mk 0 (b/a) * / Mk 3 (b/a)))  a=
          (1/a * 1 * (Mk 0 (b/a) * Mk 0 (b/a) * / Mk 3 (b/a))) * a). { reflexivity. } rewrite H34.
assert (1/a * 1 * (Mk 0 (b/a) * Mk 0 (b/a) * / Mk 3 (b/a)) *a=
           (/a * a)*  (Mk 0 (b/a)) * (Mk 0 (b/a) * (/Mk 3 (b/a)))). { nra. } rewrite H35.
assert (1= /a * a ). { apply Rinv_l_sym. nra. } rewrite <-H36.
assert (1 * Mk 0 (b / a) * (Mk 2 (b / a) * / Mk 3 (b / a)) +
        -1 * (b / a) * Mk 0 (b / a) * (Mk 1 (b / a) * / Mk 3 (b / a)) +
        1 * Mk 0 (b / a) * (Mk 0 (b / a) * / Mk 3 (b / a))=
        (Mk 0 (b/a))* (Mk 2 (b/a) - (b/a) * (Mk 1 (b/a)) + Mk 0 (b/a)) *(/ Mk 3 (b/a))). { nra. } rewrite H37.
assert ((Mk 2 (b / a) - b / a * Mk 1 (b / a) + Mk 0 (b / a))=0).
{ assert (Mk 2 (b/a) = (b/a) * (Mk 1 (b/a)) - Mk 0 (b/a)). { apply Mk_recurr. } rewrite H38. nra. }
rewrite H38. nra.
Qed.




Lemma Ah_prop_2 (a b:R) :forall (i j N:nat) , (3<N)%nat /\  j = 1%nat -> 0 < a ->sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
        l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0
  2 = 0.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0 2 =sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat 1%nat + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 2%nat 2%nat).
{ apply (sum_n_m_Chasles   (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat 1%nat 2%nat). omega. omega. }rewrite H1.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0 1 =sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat 0%nat + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 1%nat 1%nat).
{ apply (sum_n_m_Chasles  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat 0%nat 1%nat). omega. omega. } rewrite H2.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0 0=  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat). } rewrite H3.
assert (sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 1 1= (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 1%nat).
{ apply (sum_n_n (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 1%nat). } rewrite H4.
assert (sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 2 2 =(fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 2%nat). 
{ apply (sum_n_n (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 2%nat).  } rewrite H5.
unfold inverse_A. 
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) 0 0=   (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) 0%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) 0%nat 0%nat). omega. omega. } rewrite H6.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) 0 1= (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) 0%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) 0%nat 1%nat). omega. omega. } rewrite H7.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) 0 2= (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) 0%nat 2%nat).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) 0%nat 2%nat). omega. omega. } rewrite H8.
assert ( 0 <=? 0=true). { apply leb_correct. omega. } rewrite H9.
assert (0 <=? 1=true). { apply leb_correct. omega. } rewrite H10.
assert (0 <=? 2=true). { apply leb_correct. omega. } rewrite H11.
unfold Ah.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0)) 0 j=(fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 0%nat j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 0%nat j). omega. omega. } rewrite H12.
assert (  coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0)) 1 j= (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 1%nat j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 1%nat j). omega. omega. } rewrite H13.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0)) 2 j=(fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 2%nat j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 2%nat j). omega. omega. } rewrite H14. destruct H.
assert (0 =? j=false). { assert ((0 =? j) = false <-> 0%nat <> j). { apply beq_nat_false_iff. } destruct H16. apply H17. omega. } rewrite H16.
assert ( 0 - j =? one=false). { assert ((0 - j =? one) = false <-> (0-j)%nat <> one). { apply beq_nat_false_iff. } destruct H17. apply H18. assert ((0 - j)%nat=0%nat). { apply obvio_2. omega. } rewrite H19. discriminate. }
rewrite H17. assert ( j - 0 =? one=true). { rewrite H15. auto. } rewrite H18.
assert ( 1 =? j=true). { rewrite H15. auto. } rewrite H19.
assert (2 =? j=false). { assert ((2 =? j) = false <->  2%nat <> j). { apply beq_nat_false_iff. } destruct H20. apply H21. omega. } rewrite H20.
assert ( 2 - j =? one=true). { rewrite H15. auto. } rewrite H21.
assert ((-1) ^ (0 + 0)=1). { assert ((0 + 0)%nat = 0%nat). { omega. }rewrite H22. nra. } rewrite H22.
assert ((-1) ^ (0 + 1)= -1). { assert ((0 + 1)%nat = 1%nat). { omega. } rewrite H23. nra. }rewrite H23.
assert ((-1) ^ (0 + 2)=1). { assert ((0 + 2)%nat = 2%nat). { omega. }rewrite H24. nra. }rewrite H24.
assert ((N - 0 - 1)%nat = (N-1)%nat). { omega. } rewrite H25.
assert ((N - 1 - 1)%nat = (N-2)%nat). { omega. } rewrite H26.
assert ( (N - 2 - 1)%nat = (N-3)%nat). { omega. } rewrite H27.
assert (mult  (1/a * 1 *   (Mk 0 (b/a) * Mk (N - 1) (b/a) * / Mk N (b/a))) a=
          (1/a * 1*  (Mk 0 (b/a) * Mk (N - 1) (b/a) * / Mk N (b/a))) * a).  { reflexivity. } rewrite H28.
assert (1/a * 1 * (Mk 0 (b/a) * Mk (N - 1) (b/a) * / Mk N (b/a)) *a=
        (/a * a) * (Mk 0 (b/a)) * (Mk (N - 1) (b/a) * (/ Mk N (b/a)))). { nra. } rewrite H29.
assert ( mult  (1/a * -1 *   (Mk 0 (b/a) * Mk (N - 2) (b/a) * / Mk N (b/a)))  b=
           (1/a * -1 *   (Mk 0 (b/a) * Mk (N - 2) (b/a) * / Mk N (b/a))) * b). { reflexivity. }rewrite H30. 
assert (1/a * -1 * (Mk 0 (b/a) * Mk (N - 2) (b/a) * / Mk N (b/a)) *b =
        (- (b/a) * Mk 0 (b/a))* ( Mk (N - 2) (b/a) * (/ Mk N (b/a)))). { nra. } rewrite H31.
assert (mult  (1/a * 1 *   (Mk 0 (b/a) * Mk (N - 3) (b/a) * / Mk N (b/a)))  a=
          (1/a * 1 *   (Mk 0 (b/a) * Mk (N - 3) (b/a) * / Mk N (b/a))) *  a). { reflexivity. } rewrite H32.
assert (1/a * 1 * (Mk 0 (b/a) * Mk (N - 3) (b/a) * / Mk N (b/a)) *a=
          (/a * a) * (Mk 0 (b/a)) * ( Mk (N - 3) (b/a) *(/  Mk N (b/a)))). { nra. } rewrite H33.
assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <-H34.
assert (1 * Mk 0 (b / a) * (Mk (N - 1) (b / a) * / Mk N (b / a)) +
          - (b / a) * Mk 0 (b / a) * (Mk (N - 2) (b / a) * / Mk N (b / a)) +
          1 * Mk 0 (b / a) * (Mk (N - 3) (b / a) * / Mk N (b / a)) =
        (Mk 0 (b/a)) * (Mk (N-1) (b/a) + (-b/a) * Mk (N-2) (b/a) + Mk (N-3) (b/a)) * (/Mk N (b/a))).  { nra. } rewrite H35.
assert ((Mk (N - 1) (b / a) + - b / a * Mk (N - 2) (b / a) + Mk (N - 3) (b / a))=0).
{ assert (-Mk (N - 1) (b/a)+ (b/a) * Mk (N - 2) (b/a) -  Mk (N - 3) (b/a)=0). {
    assert (-Mk (N - 1) (b/a) + (b/a) * Mk (N - 2) (b/a) -Mk (N - 3) (b/a)=
            (-1)^(pred 2)* Mk (N - 1) (b/a) + (-1)^ (2)* (b/a) * Mk (N - 2) (b/a) + (-1)^(S 2) * Mk (N - 3) (b/a)). { simpl.  nra. } rewrite H36.
    apply (Mk_prop_1 a b 2%nat N). omega. nia. }
    assert ( - Mk (N - 1) (b/a) + (b/a) * Mk (N - 2) (b/a) -  Mk (N - 3) (b/a) = 0-> Mk (N - 1) (b/a) + (-b/a) * Mk (N - 2) (b/a) + Mk (N - 3) (b/a) = 0). { nra. } apply H37.
  rewrite H36. nra.
  } rewrite H36. nra.
Qed.



Lemma size_prop_1: forall (j N:nat), (2<N)%nat -> (1<j<(N-2)%nat)%nat  -> ((N - pred j - 1)%nat = (N-(pred j+1))%nat ).
Proof.
intros. omega.
Qed.

Lemma size_prop_2: forall (j N:nat), (2<N)%nat -> (1<j<(N-2)%nat)%nat  ->((N - j - 1)%nat = (N- (j+1))%nat).
Proof.
intros. omega.
Qed.

Lemma size_prop_3: forall (j N:nat), (2<N)%nat -> (1<j<(N-2)%nat)%nat  -> ((pred j + 1)%nat = pred (j+1)%nat).
Proof.
intros. omega.
Qed.
    
Lemma size_prop_4: forall (j N:nat), (2<N)%nat -> (1<j<(N-2)%nat)%nat  -> ((N - S j - 1)%nat = (N - ( S (j+1)))%nat).
Proof.
intros. omega.
Qed.
     
Lemma size_prop_5: forall (j N:nat), (2<N)%nat -> (1<j<(N-2)%nat)%nat  ->((S j + 1)%nat= S (j+1)%nat). 
Proof.
intros. omega.
Qed.

Lemma Ah_prop_3(a b :R) : forall (j N:nat) , (2<N)%nat -> (1<j<(N-2)%nat)%nat -> 0<a -> sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
        l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
  (pred j) (S j) = 0.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
          (pred j) (S j)=sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j) j + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (S j) (S j)).
{ apply (sum_n_m_Chasles (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j) j (S j)). omega. omega. } rewrite H2.
assert (sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
        (pred j) j =sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j) (pred j) + sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (S (pred j)) j).
{ apply (sum_n_m_Chasles   (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j) (pred j) j). omega. omega. }rewrite H3.
assert ((S (pred j))=j). { omega. }rewrite H4.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
          (pred j) (pred j)= (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (pred j)).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (pred j)). } rewrite H5.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) j j= (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) j).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) j). }rewrite H6.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
          (S j) (S j)= (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (S j)).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (S j)). } rewrite H7.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j0 : nat =>
         if i <=? j0
         then
          1 / a * (-1) ^ (i + j0) *
          (Mk i (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j0) * (Mk j0 (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) 0 (pred j)=(fun i j0 : nat =>
         if i <=? j0
         then
          1 / a * (-1) ^ (i + j0) *
          (Mk i (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j0) * (Mk j0 (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (pred j)).
{ apply (coeff_mat_bij  Hierarchy.zero (fun i j0 : nat =>
         if i <=? j0
         then
          1 / a * (-1) ^ (i + j0) *
          (Mk i (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j0) * (Mk j0 (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (pred j)). omega. omega. } rewrite H8.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j0 : nat =>
         if i <=? j0
         then
          1 / a * (-1) ^ (i + j0) *
          (Mk i (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j0) * (Mk j0 (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) 0 j=(fun i j0 : nat =>
         if i <=? j0
         then
          1 / a * (-1) ^ (i + j0) *
          (Mk i (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j0) * (Mk j0 (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j0 : nat =>
         if i <=? j0
         then
          1 / a * (-1) ^ (i + j0) *
          (Mk i (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j0) * (Mk j0 (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat j). omega. omega. } rewrite H9.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j0 : nat =>
         if i <=? j0
         then
          1 / a * (-1) ^ (i + j0) *
          (Mk i (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j0) * (Mk j0 (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) 0 (S j)= (fun i j0 : nat =>
         if i <=? j0
         then
          1 / a * (-1) ^ (i + j0) *
          (Mk i (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j0) * (Mk j0 (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (S j)).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j0 : nat =>
         if i <=? j0
         then
          1 / a * (-1) ^ (i + j0) *
          (Mk i (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j0) * (Mk j0 (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (S j)). omega. omega. } rewrite H10.
assert (0 <=? pred j=true). { apply leb_correct. omega. } rewrite H11.
assert (0 <=? j=true). { apply leb_correct. omega. }rewrite H12.
assert (0 <=? S j=true). { apply leb_correct. omega. } rewrite H13.
unfold Ah.
assert ( coeff_mat Hierarchy.zero
           (mk_matrix N N
              (fun i j0 : nat =>
               if i =? j0
               then b
               else
                if i - j0 =? one
                then a
                else if j0 - i =? one then a else 0)) 
           (pred j) j=  (fun i j0 : nat =>
               if i =? j0
               then b
               else
                if i - j0 =? one
                then a
                else if j0 - i =? one then a else 0) (pred j) j).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i j0 : nat =>
               if i =? j0
               then b
               else
                if i - j0 =? one
                then a
                else if j0 - i =? one then a else 0) (pred j) j). omega. omega. } rewrite H14.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j0 : nat =>
         if i =? j0
         then b
         else
          if i - j0 =? one
          then a
          else if j0 - i =? one then a else 0)) j j=(fun i j0 : nat =>
         if i =? j0
         then b
         else
          if i - j0 =? one
          then a
          else if j0 - i =? one then a else 0) j j).
{ apply (coeff_mat_bij 0 (fun i j0 : nat =>
         if i =? j0
         then b
         else
          if i - j0 =? one
          then a
          else if j0 - i =? one then a else 0) j j). omega. omega. } rewrite H15.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j0 : nat =>
         if i =? j0
         then b
         else
          if i - j0 =? one
          then a
          else if j0 - i =? one then a else 0)) 
     (S j) j=  (fun i j0 : nat =>
         if i =? j0
         then b
         else
          if i - j0 =? one
          then a
          else if j0 - i =? one then a else 0) (S j) j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j0 : nat =>
         if i =? j0
         then b
         else
          if i - j0 =? one
          then a
          else if j0 - i =? one then a else 0) (S j) j). omega. omega. } rewrite H16.
assert (pred j =? j=false). { assert ((pred j =? j) = false <-> (pred j) <> j). { apply beq_nat_false_iff. } destruct H17. apply H18. omega. } rewrite H17.
assert ( pred j - j =? one=false). { assert ((pred j - j =? one) = false <-> (pred j - j)%nat <> one). { apply beq_nat_false_iff. } destruct H18. apply H19. assert ((pred j - j)%nat=0%nat). { apply obvio_2. omega. } rewrite H20. discriminate. }
rewrite H18.
assert (j - pred j =? one=true). { assert ((j - pred j)%nat=one). { assert (pred j = (j-1)%nat). { omega. } rewrite H19.  assert ((j - (j - 1))%nat= 1%nat). { omega. } rewrite H20. reflexivity. } rewrite H19. auto. } 
rewrite H19. assert (j =? j=true). { symmetry. apply beq_nat_refl. } rewrite H20.
assert (S j =? j = false). { assert ((S j =? j) = false <-> (S j) <> j). { apply beq_nat_false_iff. } destruct H21. apply H22. omega. } rewrite H21.
assert ( S j - j =? one= true). { assert ((S j - j)%nat=1%nat). { omega. } rewrite H22. auto. } rewrite H22.
assert ((0 + pred j)%nat = pred j). { auto. } rewrite H23.
assert ((0 + j)%nat = j). { auto. } rewrite H24.
assert ((0 + S j)%nat = S j). { auto. } rewrite H25.
assert (mult  (1/a * (-1) ^ (pred j) *   (Mk 0 (b/a) * Mk (N - pred j-1) (b/a) * / Mk N (b/a)))  a =
              (1/a* (-1) ^ (pred j) *   (Mk 0 (b/a) * Mk (N - pred j-1) (b/a) * / Mk N (b/a)))* a). { reflexivity. } rewrite H26.
assert (1/a * (-1) ^ pred j *(Mk 0 (b/a) * Mk (N - pred j-1) (b/a) * / Mk N (b/a)) *a=
          (/a * a) * (((-1) ^ pred j * Mk 0 (b/a) * Mk (N - pred j-1) (b/a)) * (/ Mk N (b/a)))). { nra. }rewrite H27.
assert (mult  (1/a * (-1) ^ j *   (Mk 0 (b/a) * Mk (N - j-1) (b/a) * / Mk N (b/a)))  b =
           (1/a * (-1) ^ (j) *   (Mk 0 (b/a) * Mk (N - j-1) (b/a) * / Mk N (b/a))) * b). { reflexivity. }rewrite H28.
assert (1/a * (-1) ^ j * (Mk 0 (b/a) * Mk (N - j-1) (b/a) * / Mk N (b/a)) *b=
           (b/a) * ( ((-1) ^ j * Mk 0 (b/a) * Mk (N - j-1) (b/a)) * (/ Mk N (b/a)))). { nra. }rewrite H29.
assert (mult  (1/a * (-1) ^ S j *   (Mk 0 (b/a) * Mk (N - S j-1) (b/a) * / Mk N (b/a)))  a=
        (1/a * (-1) ^ S j *   (Mk 0 (b/a) * Mk (N - S j-1) (b/a) * / Mk N (b/a)))* a). { reflexivity. }rewrite H30.
assert (1/a * (-1) ^ S j *(Mk 0 (b/a) * Mk (N - S j-1) (b/a) * / Mk N (b/a)) *a=
         (/a * a) * ( ((-1) ^ S j * Mk 0 (b/a)* Mk (N - S j-1) (b/a) ) * (/Mk N (b/a)))). { nra. } rewrite H31.
assert (1=/a * a). { apply Rinv_l_sym. nra. } rewrite <- H32.
assert (1 * ((-1) ^ pred j * Mk 0 (b / a) * Mk (N - pred j - 1) (b / a) * / Mk N (b / a)) +
          b / a * ((-1) ^ j * Mk 0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a)) +
          1 * ((-1) ^ S j * Mk 0 (b / a) * Mk (N - S j - 1) (b / a) * / Mk N (b / a))=
          Mk 0 (b/a) * ((-1)^ (pred j) * Mk (N-pred j -1) (b/a) + (-1)^ j * (b/a) *Mk (N-j-1) (b/a) + (-1)^ (S j) * Mk ( N - S j -1) (b/a)) * (/ Mk N (b/a))). 
{ nra. }  rewrite H33.
assert ( ((-1) ^ pred j * Mk (N - pred j-1) (b/a) + (-1) ^ j * (b/a) * Mk (N - j-1) (b/a) + (-1) ^ S j * Mk (N - S j-1) (b/a))=0).
{ assert ((-1)*(-1) ^ pred j * Mk (N - pred j - 1) (b/a) +(-1)*(-1) ^ j * (b/a) * Mk (N - j - 1) (b/a) +(-1)*(-1) ^ S j * Mk (N - S j - 1) (b/a) = 0->
                (-1) ^ pred j * Mk (N - pred j - 1) (b/a) +(-1) ^ j * (b/a) * Mk (N - j - 1) (b/a) +(-1) ^ S j * Mk (N - S j - 1) (b/a) = 0). { nra. } apply H34.
  assert (-1 * (-1) ^ pred j * Mk (N - pred j - 1) (b/a)= (-1)^(pred j +1)%nat * Mk (N - pred j - 1) (b/a)).
  { assert (-1 * (-1) ^ pred j * Mk (N - pred j - 1) (b/a)= ( (-1)^1 * (-1) ^ pred j) *  Mk (N - pred j - 1) (b/a)). { nra. } rewrite H35.
    assert ( (-1)^ ( 1+ pred j)%nat =(-1) ^ 1 * (-1) ^ pred j). { apply pow_add. } rewrite <-H36. 
    assert ((1 + pred j)%nat = (pred j + 1)%nat). { omega. } rewrite H37. reflexivity. } rewrite H35.
      assert (-1 * (-1) ^ j * (b/a) * Mk (N - j - 1) (b/a)= (-1)^ (j+1)%nat * (b/a)*Mk (N - j - 1) (b/a)).
      { assert (-1 * (-1) ^ j * (b/a)* Mk (N - j - 1) (b/a) = ((-1)^1 * (-1)^j) * (b/a) * Mk (N - j - 1) (b/a)). { nra. }  rewrite H36.
        assert ((-1)^ (1+j)%nat = ((-1)^1 * (-1)^j)). { apply pow_add. } rewrite <-H37. assert ( (1 + j)%nat = (j + 1)%nat). { omega. } rewrite H38.
        reflexivity.
      } rewrite H36. 
      assert (-1 * (-1) ^ S j * Mk (N - S j - 1) (b/a)= (-1)^ (S j +1)%nat *  Mk (N - S j - 1) (b/a)).
      { assert (-1 * (-1) ^ S j * Mk (N - S j - 1) (b/a)= ( (-1)^1 * (-1)^ (S j)) *  Mk (N - S j - 1) (b/a)). { nra. } rewrite H37.
        assert ((-1) ^ (1+S j)%nat = (-1)^1 * (-1)^ (S j)). { apply pow_add. } rewrite <-H38. assert ( (1 + S j)%nat =  (S j + 1)%nat). { omega. } rewrite H39.
        reflexivity.
      } rewrite H37.
      assert ((N - pred j - 1)%nat = (N-(pred j+1))%nat ). { apply size_prop_1. apply H. apply H0. } rewrite H38.
      assert ((N - j - 1)%nat = (N- (j+1))%nat). { apply size_prop_2. apply H. apply H0. } rewrite H39.
      assert ((pred j + 1)%nat = pred (j+1)%nat). { apply (size_prop_3 j  N). apply H. apply H0. }  rewrite H40. 
      assert ((N - S j - 1)%nat = (N - ( S (j+1)))%nat). { apply size_prop_4. apply H. apply H0.  } rewrite H41.
      assert ((S j + 1)%nat= S (j+1)%nat). { apply (size_prop_5 j N). apply H. apply H0.  } rewrite H42.
      apply Mk_prop_1. apply H. nia.
    } rewrite H34. nra.
Qed.

Lemma size_prop_6: forall N:nat , (2<N)%nat -> (N- ( S (N-2)))%nat = 1%nat.
Proof.
intros.
omega.
Qed.

Lemma size_prop_7: forall N:nat , (2<N)%nat -> (N- (N-2))%nat = 2%nat.
Proof. 
intros. omega.
Qed.

Lemma size_prop_8: forall N:nat , (2<N)%nat -> (N- (pred (N-2)))%nat= 3%nat.
Proof.
intros. omega.
Qed.

Lemma size_prop_9: forall N:nat , (2<N)%nat ->  (N-3)%nat = pred (N-2)%nat.
Proof.
intros. omega.
Qed.

Lemma size_prop_10: forall N:nat , (2<N)%nat -> pred N = S (N-2)%nat.
Proof.
intros. omega.
Qed.

Lemma size_prop_11: forall N:nat , (3<N)%nat -> (2< N)%nat.
Proof.
intros. omega.
Qed.

Lemma size_prop_12: forall N:nat , (3<N)%nat ->(N - 2)%nat = ((N-3) +1)%nat.
Proof.
intros. omega. 
Qed.
 
Lemma size_prop_13: forall N:nat , (3<N)%nat -> pred N= ((N-3)+2)%nat.
Proof.
intros. omega.
Qed.

Lemma Ah_prop_4 ( a b :R):forall (N:nat),(3<N)%nat ->  0<a ->sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A N a b) 0
        l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l
        (N - 2))) (N - 3) (pred N) = 0.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a) l (N - 2))) 
          (N - 3) (pred N)=sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a) l (N - 2))) (N-3)%nat (N-2)%nat + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a) l (N - 2))) (S (N-2)%nat) (pred N)).
{ apply (sum_n_m_Chasles  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a) l (N - 2))) (N-3)%nat (N-2)%nat (pred N)). omega. omega. }
rewrite H1. assert ((S (N - 2))= pred N). { omega. } rewrite H2.
assert (sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
        (N - 3) (N - 2)=sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat (N-3)%nat + sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (S (N-3)%nat) (N-2)%nat).
{ apply (sum_n_m_Chasles (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat (N-3)%nat (N-2)%nat). omega. omega. }
rewrite H3. assert ( (S (N - 3)) = (N-2)%nat). { omega. } rewrite H4.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
          (N - 3) (N - 3)=(fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat). } rewrite H5.
assert (sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
        (N - 2) (N - 2)=(fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-2)%nat).
{ apply (sum_n_n (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-2)%nat). } rewrite H6.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
          (pred N) (pred N) = (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (pred N)).
{ apply (sum_n_n  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (pred N)). } rewrite H7.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) 0 (N - 3)= (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (N - 3)%nat).
{ apply (coeff_mat_bij Hierarchy.zero   (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (N - 3)%nat). omega. omega. } rewrite H8.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) 0 (N - 2)=    (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (N - 2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (N - 2)%nat). omega. omega. } rewrite H9.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) 0 (pred N)= (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (pred N)%nat).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (pred N)%nat). omega. omega. } rewrite H10.
assert ( 0 <=? N - 3=true). { apply leb_correct. omega. } rewrite H11.
assert (0 <=? N - 2=true). { apply leb_correct. omega. } rewrite H12.
assert (0 <=? pred N=true). { apply leb_correct. omega. } rewrite H13.
unfold Ah.
assert ( coeff_mat Hierarchy.zero
           (mk_matrix N N
              (fun i j : nat =>
               if i =? j
               then b
               else
                if i - j =? one
                then a
                else if j - i =? one then a else 0)) 
           (N - 3) (N - 2) =  (fun i j : nat =>
               if i =? j
               then b
               else
                if i - j =? one
                then a
                else if j - i =? one then a else 0) (N-3)%nat (N-2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i j : nat =>
               if i =? j
               then b
               else
                if i - j =? one
                then a
                else if j - i =? one then a else 0) (N-3)%nat (N-2)%nat). omega. omega. } rewrite H14.
assert (coeff_mat Hierarchy.zero
           (mk_matrix N N
              (fun i j : nat =>
               if i =? j
               then b
               else
                if i - j =? one
                then a
                else if j - i =? one then a else 0)) 
           (N - 2) (N - 2)=(fun i j : nat =>
               if i =? j
               then b
               else
                if i - j =? one
                then a
                else if j - i =? one then a else 0) (N-2)%nat (N-2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero(fun i j : nat =>
               if i =? j
               then b
               else
                if i - j =? one
                then a
                else if j - i =? one then a else 0) (N-2)%nat (N-2)%nat). omega. omega. } rewrite H15.
assert (coeff_mat Hierarchy.zero
         (mk_matrix N N
            (fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0)) 
         (pred N) (N - 2)= (fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0) (pred N) (N-2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero(fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0) (pred N) (N-2)%nat). omega. omega. } rewrite H16.
assert (N - 3 =? N - 2=false). { assert ((N - 3 =? N - 2) = false <-> (N-3)%nat <> (N-2)%nat). { apply beq_nat_false_iff. } destruct H17. apply H18. omega. } rewrite H17.
assert ( N - 3 - (N - 2) =? one=false). { assert ((N - 3 - (N - 2) =? one) = false <-> (N - 3 - (N - 2))%nat <> one ). { apply beq_nat_false_iff. } destruct H18. apply H19. 
assert ((N - 3 - (N - 2))%nat= 0%nat). { apply obvio_2. omega. } rewrite H20. discriminate. }
rewrite H18.
assert (N - 2 - (N - 3) =? one = true). { assert ((N - 2 - (N - 3))%nat = 1%nat).  { omega. } rewrite H19. auto. } rewrite H19.
assert ( N - 2 =? N - 2=true). { symmetry. apply beq_nat_refl. } rewrite H20.
assert ( pred N =? N - 2=false). { assert ((pred N =? N - 2) = false <-> (pred N) <> (N-2)%nat). { apply beq_nat_false_iff. } destruct H21. apply H22. omega. } rewrite H21.
assert ( pred N - (N - 2) =? one= true). { assert ((pred N - (N - 2))%nat = 1%nat). { omega. } rewrite H22. auto. } rewrite H22.
assert ((N - (N - 3))%nat = 3%nat). { omega. } rewrite H23.
assert ( (N - (N - 2))%nat=2%nat). { omega. } rewrite H24.
assert ((N - pred N)%nat = 1%nat). { omega. } rewrite H25.
assert ((0 + (N - 3))%nat = (N-3)%nat). { auto. } rewrite H26.
assert ((0 + (N - 2))%nat = (N-2)%nat). { auto. } rewrite H27.
assert((0 + pred N)%nat = pred N). { auto. }rewrite H28.
assert ( (3 - 1)%nat = 2%nat). { auto. } rewrite H29.
assert ((2 - 1)%nat = 1%nat). { auto. } rewrite H30.
assert ((1 - 1)%nat = 0%nat). { auto. }rewrite H31.
assert (mult  (1/a * (-1) ^ (N - 3) *   (Mk 0 (b/a) * Mk 2 (b/a) * / Mk N (b/a)))   a =
        (1/a* (-1) ^ (N - 3) *   (Mk 0 (b/a) * Mk 2 (b/a) * / Mk N (b/a))) *   a). { reflexivity. } rewrite H32.
assert (1/a * (-1) ^ (N - 3) * (Mk 0 (b/a) * Mk 2 (b/a) * / Mk N (b/a)) *a=
        ( /a * a) * ( ( (-1) ^ (N - 3)*Mk 0 (b/a) *Mk 2 (b/a)) *(/  Mk N (b/a)))). { nra. } rewrite H33.
assert (mult  (1/a* (-1) ^ (N - 2) *   (Mk 0 (b/a) * Mk 1 (b/a) * / Mk N (b/a)))   b=
         (1/a* (-1) ^ (N - 2) *   (Mk 0 (b/a) * Mk 1 (b/a) * / Mk N (b/a)))*  b). { reflexivity. } rewrite H34.
assert (1/a * (-1) ^ (N - 2) * (Mk 0 (b/a) * Mk 1 (b/a) * / Mk N (b/a)) *b=
         ( b/a)* ( ((-1) ^ (N - 2)*  Mk 0 (b/a)*Mk 1 (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H35.
assert (mult  (1/a * (-1) ^ pred N *   (Mk 0 (b/a) * Mk 0 (b/a) * / Mk N (b/a)))   a=
        (1/a * (-1) ^ pred N *   (Mk 0 (b/a) * Mk 0 (b/a) * / Mk N (b/a))) * a). { reflexivity. }rewrite H36.
assert (1/a * (-1) ^ pred N * (Mk 0 (b/a) * Mk 0 (b/a) * / Mk N (b/a)) *a =
           ( /a * a)* ((  (-1) ^ pred N * Mk 0 (b/a) *  Mk 0 (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H37.
assert (1=/a * a). { apply Rinv_l_sym. nra. } rewrite <-H38.
assert (1 * ((-1) ^ (N - 3) * Mk 0 (b / a) * Mk 2 (b / a) * / Mk N (b / a)) +
        b / a * ((-1) ^ (N - 2) * Mk 0 (b / a) * Mk 1 (b / a) * / Mk N (b / a)) +
        1 * ((-1) ^ pred N * Mk 0 (b / a) * Mk 0 (b / a) * / Mk N (b / a))=
          Mk 0 (b/a) * ( (-1)^ (N-3) * Mk 2 (b/a) + (-1)^ (N-2) * (b/a) * Mk 1 (b/a) + (-1)^ (pred N) * Mk 0 (b/a)) * (/ Mk N (b/a))).
{ nra. } rewrite H39.
assert (( (-1)^ (N-3) * Mk 2 (b/a) + (-1)^ (N-2) * (b/a) * Mk 1 (b/a) + (-1)^ (pred N) * Mk 0 (b/a))=0).
{ assert( (N - 2)%nat = ((N-3) +1)%nat). { apply size_prop_12. apply H. } rewrite H40.
   assert ( pred N= ((N-3)+2)%nat). { apply size_prop_13. apply H. } rewrite H41.
  assert ((-1) ^ (N - 3 + 1)= (-1)^ (N-3)%nat * (-1)^1). { apply pow_add. } rewrite H42.
    assert ((-1) ^ (N - 3 + 2)= (-1)^ (N-3)%nat * (-1)^2).  { apply pow_add. } rewrite H43.
   assert((-1) ^ (N - 3) * Mk 2 (b / a) + (-1) ^ (N - 3) * (-1) ^ 1 * (b / a) * Mk 1 (b / a) +(-1) ^ (N - 3) * (-1) ^ 2 * Mk 0 (b / a)=
                    (-1)^ (N-3) * ( Mk 2 (b/a) + (-1)^ 1* (b/a)  * Mk 1 (b/a) + (-1)^2 * Mk 0 (b/a))). { nra. } rewrite H44.
   assert ((Mk 2 (b / a) + (-1) ^ 1 * (b / a) * Mk 1 (b / a) + (-1) ^ 2 * Mk 0 (b / a))=
                  (-1)^ (pred 1) * Mk (pred 1) (b/a) + (-1)^1 * (b/a) * Mk 1 (b/a) + (-1)^ (S 1) * Mk (S 1) (b/a)). { simpl. nra. } rewrite H45.
    assert (((-1) ^ pred 1 * Mk (pred 1) (b / a) + (-1) ^ 1 * (b / a) * Mk 1 (b / a) +
                (-1) ^ 2 * Mk 2 (b / a))=0). { apply Mk_prop_2. auto. } rewrite H46. nra.
} rewrite H40. nra.
Qed.


Lemma size_prop_14: forall N:nat , (2<N)%nat ->  pred N = ((N-2)+1)%nat.
Proof.
intros. omega.
Qed.



Lemma Ah_prop_5 (a b:R): forall (N:nat) , (2<N)%nat -> 0 < a ->sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
        l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l
        (pred N))) (N - 2) (pred N) = 0.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (pred N)))
          (N - 2) (pred N)=sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (pred N))) (N-2)%nat (N-2)%nat + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (pred N))) (S (N-2)%nat) (pred N)).
{ apply (sum_n_m_Chasles (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (pred N))) (N-2)%nat (N-2)%nat (pred N)). omega. omega. } rewrite H1.
assert (  (S (N - 2))= (pred N)). { omega. } rewrite H2.
assert (sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l (pred N)))
        (N - 2) (N - 2)=(fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l (pred N))) (N-2)%nat).
{ apply (sum_n_n (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l (pred N))) (N-2)%nat). } rewrite H3.
assert (sum_n_m  (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l (pred N)))
            (pred N) (pred N)=(fun l : nat =>
             mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l (pred N))) (pred N)).
{ apply (sum_n_n (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l (pred N))) (pred N)). } rewrite H4.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) 0 (N - 2)=  (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (N - 2)%nat).
{ apply (coeff_mat_bij  Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (N - 2)%nat). omega. omega. } rewrite H5.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) 0 (pred N)=(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (pred N)).
{ apply (coeff_mat_bij Hierarchy.zero   (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 0%nat (pred N)). omega. omega. } rewrite H6.
assert (0 <=? N - 2=true). { apply leb_correct. omega. }rewrite H7.
assert ( 0 <=? pred N=true). { apply leb_correct. omega. } rewrite H8.
unfold Ah.
assert ( coeff_mat Hierarchy.zero
         (mk_matrix N N
            (fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0)) 
         (N - 2) (pred N)= (fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0) (N-2)%nat (pred N)).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0) (N-2)%nat (pred N)). omega. omega. } rewrite H9.
assert (coeff_mat Hierarchy.zero
           (mk_matrix N N
              (fun i j : nat =>
               if i =? j
               then b
               else
                if i - j =? one
                then a
                else if j - i =? one then a else 0)) 
           (pred N) (pred N)= (fun i j : nat =>
               if i =? j
               then b
               else
                if i - j =? one
                then a
                else if j - i =? one then a else 0) (pred N) (pred N)).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
               if i =? j
               then b
               else
                if i - j =? one
                then a
                else if j - i =? one then a else 0) (pred N) (pred N)). omega. omega. } rewrite H10.
assert (N - 2 =? pred N = false). { assert ((N - 2 =? pred N) = false <-> (N-2)%nat <> pred N). { apply beq_nat_false_iff. } destruct H11. apply H12. omega. } rewrite H11.
assert (N - 2 - pred N =? one=false). { assert ((N - 2 - pred N =? one) = false <-> (N - 2 - pred N )%nat <> one). { apply beq_nat_false_iff. } destruct H12. apply H13. 
assert ((N - 2 - pred N)%nat=0%nat). { apply obvio_2. omega. } rewrite H14. discriminate. } rewrite H12.
assert ( pred N - (N - 2) =? one=true). { assert ((pred N - (N - 2))%nat =1%nat). { omega. } rewrite H13. auto. } rewrite H13.
assert ( pred N =? pred N=true). { symmetry. apply beq_nat_refl. } rewrite H14.
assert ((0 + (N - 2))%nat = (N-2)%nat). { auto. } rewrite H15.
assert ((N - (N - 2))%nat = 2%nat). { omega. } rewrite H16.
assert ( (N - pred N)%nat =1%nat). { omega. } rewrite H17. 
assert ((0 + pred N)%nat = pred N). { auto. }rewrite H18.
assert ((1 - 1)%nat =0%nat). { auto. } rewrite H19.
assert ((2 - 1)%nat =1%nat). { auto. }rewrite H20.
assert (mult  (1/a * (-1) ^ (N - 2) *   (Mk 0 (b/a) * Mk 1 (b/a) * / Mk N (b/a)))   a=
          (1/a* (-1) ^ (N - 2) *   (Mk 0 (b/a) * Mk 1 (b/a) * / Mk N (b/a))) * a). { reflexivity. }rewrite H21.
assert (1/a* (-1) ^ (N - 2) * (Mk 0 (b/a) * Mk 1 (b/a) * / Mk N (b/a)) *a=
          ( /a * a) * (( (-1) ^ (N - 2) * Mk 0 (b/a) * Mk 1 (b/a) ) * (/ Mk N (b/a)))). { nra. }rewrite H22.
assert (mult  (1/a * (-1) ^ pred N *   (Mk 0 (b/a) * Mk 0 (b/a) * / Mk N (b/a)))   b=
           (1/a * (-1) ^ pred N *   (Mk 0 (b/a) * Mk 0 (b/a) * / Mk N (b/a))) * b). { reflexivity. } rewrite H23.
assert (1/a * (-1) ^ pred N * (Mk 0 (b/a) * Mk 0 (b/a) * / Mk N (b/a)) *b=
           ( b/a) * (( (-1) ^ pred N  * Mk 0 (b/a) *  Mk 0 (b/a)) * (/ Mk N (b/a)))). { nra. }rewrite H24.
assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H25. 
assert ( pred N = ((N-2)+1)%nat). { apply size_prop_14. apply H. } rewrite H26.
assert ((-1) ^ (N - 2 + 1)= (-1)^ (N-2)%nat * (-1)^1). { apply pow_add. } rewrite H27.
assert (1 * ((-1) ^ (N - 2) * Mk 0 (b / a) * Mk 1 (b / a) * / Mk N (b / a)) +
          b / a * ((-1) ^ (N - 2) * (-1) ^ 1 * Mk 0 (b / a) * Mk 0 (b / a) * / Mk N (b / a))=
          (-1)^(N-2) * Mk 0 (b/a) * (Mk 1 (b/a) + (-b/a) * Mk 0 (b/a)) *(/ Mk N (b/a))). { nra. } rewrite H28.
assert ((Mk 1 (b / a) + - b / a * Mk 0 (b / a))=0).
{ assert ( Mk 1 (b/a) = b/a). { apply Mk_B1. } rewrite H29.
  assert ( Mk 0 (b/a)=1). { apply Mk_B0. } rewrite H30. nra.
} rewrite H29. nra.
Qed.


Lemma Ah_prop_6 (a b:R): Mk 3 (b/a) <> 0 -> 0<a -> sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
     (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0 2 =1.
Proof.
intros.
assert (sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0 2 =sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat 1%nat + sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 2%nat 2%nat).
{ apply (sum_n_m_Chasles (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat 1%nat 2%nat). omega. omega. } 
rewrite H1.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0 1=sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat 0%nat + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 1%nat 1%nat).
{ apply (sum_n_m_Chasles  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat 0%nat 1%nat). omega. omega. } rewrite H2.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0 0 =(fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat). } rewrite H3.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 1 1 =  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 1%nat).
{ apply (sum_n_n  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 1%nat). } rewrite H4.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 2 2 =  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 2%nat).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 2%nat). } rewrite H5.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a))) 1 0= (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) 1%nat 0%nat).
{ apply (coeff_mat_bij  Hierarchy.zero  (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) 1%nat 0%nat). omega. omega. } rewrite H6.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a))) 1 1=(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) 1%nat 1%nat).
{ apply (coeff_mat_bij  Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) 1%nat 1%nat). omega. omega. } rewrite H7.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a))) 1 2=(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) 1%nat 2%nat).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) 1%nat 2%nat). omega. omega. } rewrite H8.
assert ( 1 <=? 0=false). { apply leb_correct_conv. omega. } rewrite H9.
assert (1 <=? 1=true). { apply leb_correct. omega. } rewrite H10.
assert ( 1 <=? 2=true). { apply leb_correct. omega. } rewrite H11.
unfold Ah.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0)) 0 1=(fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 0%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 0%nat 1%nat). omega. omega. } rewrite H12.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0)) 1 1= (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 1%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 1%nat 1%nat). omega. omega. } rewrite H13.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0)) 2 1= (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 2%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 2%nat 1%nat). omega. omega. } rewrite H14.
assert (0 =? 1=false). { auto. } rewrite H15.
assert (0 - 1 =? one=false). { auto. }rewrite H16.
assert (1 - 0 =? one=true). { auto. } rewrite H17.
assert (1 =? 1=true). { auto. } rewrite H18.
assert ( 2 =? 1=false). { auto. } rewrite H19.
assert (2 - 1 =? one=true). { auto. }rewrite H20.
assert ((-1) ^ (1 + 0) =-1). { assert ((1 + 0)%nat= 1%nat). { omega. } rewrite H21. nra. } rewrite H21.
assert ((-1) ^ (1 + 1)=1). { assert ((1 + 1)%nat=2%nat). { omega. } rewrite H22. nra. }rewrite H22.
assert ((-1) ^ (1 + 2)=-1). { assert ((1 + 2)%nat=3%nat). { omega. } rewrite H23. nra. } rewrite H23.
assert ((3 - 1-1)%nat = 1%nat). { omega. } rewrite H24.
assert ((3 - 2-1)%nat = 0%nat). { omega. }rewrite H25.
assert (mult (1/a * -1 * (Mk 0 (b/a) * Mk 1 (b/a)) * / Mk 3 (b/a))  a=
           (1/a* -1 * (Mk 0 (b/a) * Mk 1 (b/a)) * / Mk 3 (b/a)) *  a). { reflexivity. }rewrite H26.
assert (1/a * -1 * (Mk 0 (b/a) * Mk 1 (b/a)) * / Mk 3 (b/a) * a=
          ( /a * a) * (( -1 * Mk 0 (b/a) * Mk 1 (b/a))* (/ Mk 3 (b/a)))). { nra. }rewrite H27.
assert (mult (1/a * 1 * (Mk 1 (b/a) * Mk 1 (b/a) * / Mk 3 (b/a)))  b=
          (1/a * 1 * (Mk 1 (b/a) * Mk 1 (b/a) * / Mk 3 (b/a))) * b). { reflexivity. } rewrite H28.
assert (1/a * 1 * (Mk 1 (b/a) * Mk 1 (b/a) * / Mk 3 (b/a)) *b=
           ( b/a) * ( (  Mk 1 (b/a) *  Mk 1 (b/a)) * (/ Mk 3 (b/a)))). { nra. }rewrite H29.
assert (mult (1/a* -1 * (Mk 1 (b/a) * Mk 0 (b/a) * / Mk 3 (b/a)))  a=
          (1/a * -1 * (Mk 1 (b/a) * Mk 0 (b/a) * / Mk 3 (b/a))) * a). { reflexivity. }rewrite H30.
assert (1/a * -1 * (Mk 1 (b/a) * Mk 0 (b/a) * / Mk 3 (b/a)) *a=
        (/a * a) * ( ( -1 * Mk 1 (b/a) * Mk 0 (b/a)) * ( / Mk 3 (b/a)))). { nra. } rewrite H31.
assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <-H32.
assert (Mk 0 (b / a)=1). { apply Mk_B0. } rewrite H33.
assert (Mk 1 (b/a) = b/a). { apply Mk_B1. } rewrite H34.
assert (1 * (-1 * 1 * (b / a) * / Mk 3 (b / a)) + b / a * (b / a * (b / a) * / Mk 3 (b / a)) +
            1 * (-1 * (b / a) * 1 * / Mk 3 (b / a))= ( (b/a)^3 - 2* (b/a)) *(/ Mk 3 (b/a))). { nra. } rewrite H35.
assert (Mk 3 (b / a)=((b / a) ^ 3 - 2 * (b / a))).
{ assert (Mk 3 (b/a) = (b/a) * Mk 2 (b/a) - Mk 1 (b/a)). { apply Mk_recurr. } rewrite H36.
  assert ( Mk 2 (b/a) = (b/a) * Mk 1 (b/a) - Mk 0 (b/a)). { apply Mk_recurr. } rewrite H37.
  assert (Mk 1 (b/a) = b/a). { apply Mk_B1. } rewrite H38.
  assert (Mk 0 (b/a) =1 ). { apply Mk_B0. } rewrite H39. nra.
} rewrite <-H36. symmetry.
apply Rinv_r_sym. nra.
Qed. 

Lemma size_prop_30: forall (N:nat), (2<N)%nat -> (N - pred N - 1)%nat = 0%nat.
Proof.
intros. omega.
Qed.

Lemma size_prop_31: forall (i N:nat),  (2<N)%nat ->(0 < i < pred N)%nat-> (i + pred N)%nat = (i + (N - 2) + 1)%nat.
Proof.
intros. omega.
Qed.


Lemma Ah_prop_7 (a b:R): forall (i j N:nat), (2<N)%nat ->(0 < i < pred N)%nat ->j = pred N-> i <> j-> 0<a -> sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
  (N - 2) (pred N) = 0.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
          (N - 2) (pred N)=sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (N-2)%nat (N-2)%nat + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (S (N-2)%nat) (pred N)).
{ apply (sum_n_m_Chasles  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (N-2)%nat (N-2)%nat (pred N)). omega. omega. } rewrite H4.
assert ( (S (N - 2))= pred N). { omega. } rewrite H5.
assert (sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
            (N - 2) (N - 2)=(fun l : nat =>
             mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (N-2)%nat).
{ apply (sum_n_n (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (N-2)%nat). } rewrite H6.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
          (pred N) (pred N)=(fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred N)).
{ apply (sum_n_n(fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred N)). } rewrite H7.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i (N - 2)= (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (N - 2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (N - 2)%nat). omega. omega. } rewrite H8.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i (pred N)=(fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (pred N)).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (pred N)). omega. omega. } rewrite H9.
assert (i <=? N - 2=true). { apply leb_correct. omega. } rewrite H10.
assert (i <=? pred N=true). { apply leb_correct. omega. } rewrite H11.
unfold Ah. rewrite H1.
assert ( coeff_mat Hierarchy.zero
             (mk_matrix N N
                (fun i0 j0 : nat =>
                 if i0 =? j0
                 then b
                 else
                  if i0 - j0 =? one
                  then a
                  else if j0 - i0 =? one then a else 0)) 
             (N - 2) (pred N)= (fun i0 j0 : nat =>
                 if i0 =? j0
                 then b
                 else
                  if i0 - j0 =? one
                  then a
                  else if j0 - i0 =? one then a else 0) (N-2)%nat (pred N)).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
                 if i0 =? j0
                 then b
                 else
                  if i0 - j0 =? one
                  then a
                  else if j0 - i0 =? one then a else 0) (N-2)%nat (pred N)). omega. omega. } rewrite H12.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else if i0 - j0 =? one then a else if j0 - i0 =? one then a else 0)) 
     (pred N) (pred N)=(fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else if i0 - j0 =? one then a else if j0 - i0 =? one then a else 0) 
     (pred N) (pred N)).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else if i0 - j0 =? one then a else if j0 - i0 =? one then a else 0) 
     (pred N) (pred N)). omega. omega. } rewrite H13.
assert (pred N =? pred N=true). { symmetry. apply beq_nat_refl. }  rewrite H14.
assert ( N - 2 =? pred N=false). { assert ((N - 2 =? pred N) = false <-> (N-2)%nat <> pred N). { apply beq_nat_false_iff. } destruct H15. apply H16. omega. } rewrite H15.
assert ( N - 2 - pred N =? one=false). { assert ((N - 2 - pred N)%nat =0%nat). { apply obvio_2. omega. } rewrite H16. auto. }rewrite H16.
assert ( pred N - (N - 2) =? one =true). { assert ((pred N - (N - 2))%nat = 1%nat). { omega. } rewrite H17. auto. } rewrite H17.
assert ((N - (N - 2) - 1)%nat = 1%nat). { omega. } rewrite H18.
assert ((N - pred N - 1)%nat =0%nat). { apply size_prop_30. apply H. } rewrite H19.
assert (mult  (1/a * (-1) ^ (i + (N - 2)) *   (Mk i (b/a) * Mk 1 (b/a) * / Mk N (b/a))) a =
        (1/a * (-1) ^ (i + (N - 2)) *   (Mk i (b/a) * Mk 1 (b/a) * / Mk N (b/a))) * a). { reflexivity. } rewrite H20.
assert (1/a * (-1) ^ (i + (N - 2)) * (Mk i (b/a) * Mk 1 (b/a) * / Mk N (b/a)) *a=
        ( /a * a) * Mk i (b/a)  * ( ((-1) ^ (i + (N - 2)) *  Mk 1 (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H21.
assert (mult  (1/a * (-1) ^ (i + pred N) *   (Mk i (b/a) * Mk 0 (b/a) * / Mk N (b/a))) b=
           (1/a * (-1) ^ (i + pred N) *   (Mk i (b/a) * Mk 0 (b/a) * / Mk N (b/a))) * b). { reflexivity. } rewrite H22.
assert (1/a * (-1) ^ (i + pred N) * (Mk i (b/a) * Mk 0 (b/a) * / Mk N (b/a)) *b=
         ( b/a) * Mk i (b/a)  *( ((-1) ^ (i + pred N)  *  Mk 0 (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H23.
assert (1=/a* a). { apply Rinv_l_sym. nra. } rewrite <-H24.
assert ((i + pred N)%nat = ((i + (N - 2))+1)%nat). { apply size_prop_31. apply H. apply H0. } rewrite H25.
assert ((-1) ^ (i + (N - 2) + 1) = (-1) ^ (i + (N - 2)) * (-1)^1). { apply pow_add. }rewrite H26.
assert ( 1 * Mk i (b / a) * ((-1) ^ (i + (N - 2)) * Mk 1 (b / a) * / Mk N (b / a)) +
            b / a * Mk i (b / a) * ((-1) ^ (i + (N - 2)) * (-1) ^ 1 * Mk 0 (b / a) * / Mk N (b / a))=
          Mk i (b/a) * (-1)^(i+(N-2)) * (Mk 1 (b/a) + (-1)^(1) * (b/a) * Mk 0 (b/a) ) * (/ Mk N (b/a))). { nra. } rewrite H27.
assert (Mk 1 (b / a) + (-1) ^ 1 * (b / a) * Mk 0 (b / a)=0).
{ assert (Mk 1 (b/a) = b/a). { apply Mk_B1. } rewrite H28.
  assert (Mk 0 (b/a) = 1). { apply Mk_B0. } rewrite H29. nra.
} rewrite H28. nra.
Qed.


Lemma Ah_prop_9 (a b:R):forall (N:nat), (N=3)%nat -> (Mk N (b/a)<> 0) -> 0<a -> sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero
        (inverse_A N a b ) 1 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 1))  0 2 = 1.
Proof.
intros.
rewrite H.
assert (sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero 
              (inverse_A 3 a b) 1 l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0  2 =sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero 
              (inverse_A 3 a b) 1 l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat 1%nat + sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero 
              (inverse_A 3 a b) 1 l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 2%nat 2%nat).
{ apply (sum_n_m_Chasles (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero 
              (inverse_A 3 a b) 1 l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat 1%nat 2%nat). omega. omega. } rewrite H2.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero
                (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1))  0 1=sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero
                (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat 0%nat + sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero
                (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 1%nat 1%nat).
{ apply (sum_n_m_Chasles  (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero
                (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat 0%nat 1%nat). omega. omega. } rewrite H3.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero
                (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1))  0 0=(fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero
                (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat).
{ apply (sum_n_n (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero
                (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat). } rewrite H4.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero
                (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1))  1 1= (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero
                (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 1%nat).
{ apply (sum_n_n (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero
                (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 1%nat). } rewrite H5.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero
                (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1))  2 2= (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero
                (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 2%nat).
{ apply (sum_n_n (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero
                (inverse_A 3 a b) 1 l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 2%nat). } rewrite H6.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a))) 1 0=(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) 1%nat 0%nat).
{ apply (coeff_mat_bij  Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) 1%nat 0%nat). omega. omega. } rewrite H7.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a))) 1 1=(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) 1%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) 1%nat 1%nat). omega. omega. } rewrite H8.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a))) 1 2=(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) 1%nat 2%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) 1%nat 2%nat). omega. omega. } rewrite H9.
assert (1 <=? 0=false). { apply leb_correct_conv. omega. } rewrite H10.
assert (1 <=? 1=true). { apply leb_correct. omega. } rewrite H11.
assert (1 <=? 2=true). { apply leb_correct. omega. } rewrite H12.
unfold Ah.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0))  0 1=(fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 0%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 0%nat 1%nat). omega. omega. } rewrite H13.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0))  1 1=(fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 1%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 1%nat 1%nat). omega. omega. } rewrite H14.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0))  2 1= (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 2%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 2%nat 1%nat). omega. omega. } rewrite H15.
assert (0 =? 1= false). { auto. } rewrite H16.
assert (0 - 1 =? one=false). { auto. } rewrite H17.
assert ( 1 - 0 =? one=true). { auto. } rewrite H18.
assert (1 =? 1=true). { auto. } rewrite H19.
assert (2 =? 1=false). { auto. }rewrite H20.
assert (2 - 1 =? one=true). { auto. }rewrite H21.
assert ((-1) ^ (1 + 0)=-1). { assert ((1 + 0)%nat = 1%nat). { omega. } rewrite H22. nra. } rewrite H22.
assert ((-1) ^ (1 + 1)=1). { assert ((1 + 1)%nat = 2%nat). { omega. } rewrite H23.  nra. } rewrite H23.
assert ((-1) ^ (1 + 2)= -1). { assert ((1 + 2)%nat = 3%nat). { omega. } rewrite H24. nra. }rewrite H24.
assert ((3 - 1 - 1)%nat = 1%nat). { auto. } rewrite H25. 
assert ((3 - 2 - 1)%nat=0%nat). { auto. } rewrite H26.
assert (mult (1/a * -1 * (Mk 0 (b/a) * Mk 1 (b/a)) * / Mk 3 (b/a))  a=
        (1/a* -1 * (Mk 0 (b/a) * Mk 1 (b/a)) * / Mk 3 (b/a)) * a). { reflexivity. }rewrite H27.
assert (1/a * -1 * (Mk 0 (b/a) * Mk 1 (b/a)) * / Mk 3 (b/a) *a=
        (/a * a)* ( (-1 * Mk 0 (b/a) * Mk 1 (b/a)) * (/ Mk 3 (b/a)))). { nra. }rewrite H28.
assert (mult (1/a * 1  * (Mk 1 (b/a) * Mk 1 (b/a) * / Mk 3 (b/a)))  b=
          (1/a * 1 * (Mk 1 (b/a) * Mk 1 (b/a) * / Mk 3 (b/a))) * b). { reflexivity. } rewrite H29.
assert (1/a* 1 * (Mk 1 (b/a) * Mk 1 (b/a) * / Mk 3 (b/a)) *b=
         (b/a) * ( ( 1  *  Mk 1 (b/a) * Mk 1 (b/a))* (/ Mk 3 (b/a)))). { nra. }rewrite H30.
assert (mult (1/a * -1 * (Mk 1 (b/a) * Mk 0 (b/a) * / Mk 3 (b/a)))  a=
          (1/a * -1 * (Mk 1 (b/a) * Mk 0 (b/a) * / Mk 3 (b/a))) * a). { reflexivity. }rewrite H31.
assert (1/a * -1 * (Mk 1 (b/a) * Mk 0 (b/a) * / Mk 3 (b/a)) *a=
           (/a * a) * ( (-1 * Mk 1 (b/a) * Mk 0 (b/a)) * (/ Mk 3 (b/a)))). { nra. } rewrite H32.
assert (1=/a * a). { apply Rinv_l_sym. nra. } rewrite <- H33.
assert (Mk 0 (b/a) =1). { apply Mk_B0. } rewrite H34.
assert (Mk 1 (b/a)=b/a). { apply Mk_B1. } rewrite H35.
assert (1 * (-1 * 1 * (b / a) * / Mk 3 (b / a)) +
          b / a * (1 * (b / a) * (b / a) * / Mk 3 (b / a)) +
          1 * (-1 * (b / a) * 1 * / Mk 3 (b / a))=
                ((b/a)^3 - 2* (b/a)) *(/Mk 3 (b/a))). { nra. } rewrite H36.
assert (Mk 3 (b/a) = (b/a)^3 - 2* (b/a)).
{ assert (Mk 3 (b/a) = (b/a) * Mk 2 (b/a) - Mk 1 (b/a)). { apply Mk_recurr. } rewrite H37.
  assert (Mk 2 (b/a) = (b/a)*Mk 1 (b/a) - Mk 0 (b/a)). { apply Mk_recurr. } rewrite H38.
  rewrite H34. rewrite H35. nra.
} rewrite <- H37.  symmetry. apply Rinv_r_sym. rewrite H in H0. nra. 
Qed.



Hypothesis Mk_prop_3: forall (a b:R) (i N:nat), (2<N)%nat -> (1< i< N-2)%nat -> Mk N (b/a) <> 0 -> 
              (Mk i (b / a) * Mk (N - i) (b / a) - Mk (i - 1) (b / a) * Mk (N - i - 1) (b / a))  = Mk N (b/a).



Lemma Ah_prop_10(a b:R): forall (i N:nat), (2<N)%nat -> (1< i < (N-2)%nat) %nat -> Mk N (b/a) <> 0 -> 0< a->  sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero 
        (inverse_A N a b ) i l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l i))
  (pred i) (S i) = 1.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l i))
          (pred i) (S i)=sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l i)) (pred i) i + sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l i)) (S i) (S i)).
{ apply (sum_n_m_Chasles   (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l i)) (pred i) i (S i)). omega. omega. } rewrite H3.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero 
                (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l i))
          (pred i) i =sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero 
                (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l i)) (pred i) (pred i) + sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero 
                (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l i)) (S (pred i)) i).
{ apply (sum_n_m_Chasles (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero 
                (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l i)) (pred i) (pred i) i). omega. omega. } rewrite H4.
assert ((S (pred i))=i). { omega. } rewrite H5.
assert (sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero 
              (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l i))
        (pred i) (pred i)=  (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero 
              (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l i)) (pred i)).
{ apply (sum_n_n (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero 
              (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l i)) (pred i)). } rewrite H6.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero 
                (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l i)) i i= (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero 
                (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l i)) i).
{ apply (sum_n_n (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero 
                (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l i)) i). } rewrite H7.
assert (sum_n_m
            (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                  l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l i))
            (S i) (S i)=   (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                  l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l i)) (S i)).
{ apply (sum_n_n (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                  l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l i)) (S i)). } rewrite H8.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i (pred i)= (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (pred i)).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (pred i)). omega. omega. } rewrite H9.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i i= (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i i).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i i). omega. omega. } rewrite H10.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i (S i)=  (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (S i)).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (S i)). omega. omega. } rewrite H11.
assert ( i <=? pred i=false). { apply leb_correct_conv. omega. } rewrite H12.
assert (i <=? i=true). { apply leb_correct. omega. } rewrite H13.
assert (i <=? S i=true). { apply leb_correct. omega. } rewrite H14.
unfold Ah.
assert ( coeff_mat Hierarchy.zero
           (mk_matrix N N
              (fun i0 j : nat =>
               if i0 =? j
               then b
               else
                if i0 - j =? one
                then a
                else if j - i0 =? one then a else 0))
           (pred i) i=(fun i0 j : nat =>
               if i0 =? j
               then b
               else
                if i0 - j =? one
                then a
                else if j - i0 =? one then a else 0) (pred i) i).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j : nat =>
               if i0 =? j
               then b
               else
                if i0 - j =? one
                then a
                else if j - i0 =? one then a else 0) (pred i) i). omega. omega. } rewrite H15.
assert (coeff_mat Hierarchy.zero
           (mk_matrix N N
              (fun i0 j : nat =>
               if i0 =? j
               then b
               else
                if i0 - j =? one
                then a
                else if j - i0 =? one then a else 0))  i i= (fun i0 j : nat =>
               if i0 =? j
               then b
               else
                if i0 - j =? one
                then a
                else if j - i0 =? one then a else 0) i i).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i0 j : nat =>
               if i0 =? j
               then b
               else
                if i0 - j =? one
                then a
                else if j - i0 =? one then a else 0) i i). omega. omega. } rewrite H16.
assert (coeff_mat Hierarchy.zero
           (mk_matrix N N
              (fun i0 j : nat =>
               if i0 =? j
               then b
               else
                if i0 - j =? one
                then a
                else if j - i0 =? one then a else 0))
           (S i) i=(fun i0 j : nat =>
               if i0 =? j
               then b
               else
                if i0 - j =? one
                then a
                else if j - i0 =? one then a else 0) (S i) i).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j : nat =>
               if i0 =? j
               then b
               else
                if i0 - j =? one
                then a
                else if j - i0 =? one then a else 0) (S i) i). omega. omega. } rewrite H17.
assert ( pred i =? i=false). { assert ((pred i =? i) = false <-> pred i <> i). { apply beq_nat_false_iff. } destruct H18. apply H19. omega. } rewrite H18.
assert ( pred i - i =? one=false). { assert ((pred i - i =? one) = false <-> (pred i - i)%nat <> one). { apply beq_nat_false_iff. } destruct H19. apply H20.
assert ((pred i - i)%nat=0%nat). { apply obvio_2. omega. } rewrite H21. discriminate. } rewrite H19.
assert (i - pred i =? one=true). { assert ((i - pred i)%nat= 1%nat). { omega. } rewrite H20. auto. } rewrite H20.
assert (i =? i=true). { symmetry. apply beq_nat_refl. }rewrite H21.
assert (S i =? i=false). { assert ((S i =? i) = false <-> (S i) <> i). { apply beq_nat_false_iff. } destruct H22. apply H23. omega. } rewrite H22.
assert (S i - i =? one=true). { assert ((S i-i)%nat= 1%nat). { omega. }  rewrite H23. auto. }rewrite H23.
assert (mult  (1/a* (-1) ^ (i + pred i) *   (Mk (pred i) (b/a) * Mk (N - i - 1) (b/a)) * / Mk N (b/a)) a=
         (1/a* (-1) ^ (i + pred i) *   (Mk (pred i) (b/a) * Mk (N - i - 1) (b/a)) * / Mk N (b/a)) * a). { reflexivity. } rewrite H24.
assert (1/a * (-1) ^ (i + pred i) *(Mk (pred i) (b/a) * Mk (N - i - 1) (b/a)) * / Mk N (b/a) * a=
        (/a * a) * ( ((-1) ^ (i + pred i) * Mk (pred i) (b/a) * Mk (N - i - 1) (b/a))* (/ Mk N (b/a)))). { nra. } rewrite H25.
assert (mult  (1/a * (-1) ^ (i + i) *   (Mk i (b/a) * Mk (N - i - 1) (b/a) * / Mk N (b/a)))  b=
          (1/a * (-1) ^ (i + i) *   (Mk i (b/a) * Mk (N - i - 1) (b/a) * / Mk N (b/a))) * b). { reflexivity. } rewrite H26.
assert (1/a* (-1) ^ (i + i) *(Mk i (b/a) * Mk (N - i - 1) (b/a) * / Mk N (b/a)) *b=
           (b/a) * ( (  (-1) ^ (i + i) * Mk i (b/a) * Mk (N - i - 1) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H27.
assert (mult  (1/a* (-1) ^ (i + S i) *   (Mk i (b/a) * Mk (N - S i - 1) (b/a) * / Mk N (b/a)))  a=
          (1/a * (-1) ^ (i + S i) *   (Mk i (b/a) * Mk (N - S i - 1) (b/a) * / Mk N (b/a))) * a). { reflexivity. } rewrite H28.
assert (1/a * (-1) ^ (i + S i) *(Mk i (b/a) * Mk (N - S i - 1) (b/a) * / Mk N (b/a)) *a=
            (/a * a) * ( ( (-1) ^ (i + S i) * Mk i (b/a) * Mk (N - S i - 1) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H29.
assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H30.

assert (1 *((-1) ^ (i + pred i) * Mk (pred i) (b/a) * Mk (N - i - 1) (b/a) * / Mk N (b/a)) +(b/a)*
          ((-1) ^ (i + i)  * Mk i (b/a) * Mk (N - i - 1) (b/a) * / Mk N (b/a)) +1 *((-1) ^ (i + S i) * Mk i (b/a) * Mk (N - S i - 1) (b/a) * / Mk N (b/a))=
             ((-1) ^ (i + pred i) * Mk (pred i) (b/a) * Mk (N - i - 1) (b/a)+
            (-1) ^ (i + i) * (b/a) * Mk i (b/a) * Mk (N - i - 1) (b/a) +(-1) ^ (i + S i) * Mk i (b/a) * Mk (N - S i - 1) (b/a)) * (/ Mk N (b/a))). { nra. } rewrite H31.
assert ( (-1) ^ (i + pred i)= (-1)^i * (-1)^ (pred i)). { apply pow_add. } rewrite H32.
assert ((-1) ^ (i + i)= (-1)^i * (-1)^i). { apply pow_add. } rewrite H33.
assert ((-1) ^ i * (-1) ^ pred i * Mk (pred i) (b/a) * Mk (N - i - 1) (b/a) +
                 (-1) ^ i * (-1) ^ i * (b/a) * Mk i (b/a) * Mk (N - i - 1) (b/a)=
          ( (-1)^i * Mk (N - i - 1) (b/a)) * (  (-1) ^ pred i * Mk (pred i) (b/a) + (-1) ^ i * (b/a) * Mk i (b/a))). { nra. } rewrite H34.
assert ((  (-1) ^ pred i * Mk (pred i) (b/a) + (-1) ^ i * (b/a) * Mk i (b/a))= - (-1)^ (S i)* Mk (S i) (b/a)).
{ assert ((-1) ^ pred i * Mk (pred i) (b/a) + (-1) ^ i * (b/a) * Mk i (b/a) + (-1) ^ S i * Mk (S i) (b/a)=0 -> 
          (-1) ^ pred i * Mk (pred i) (b/a) + (-1) ^ i * (b/a) * Mk i (b/a) =- (-1) ^ S i * Mk (S i) (b/a)). { nra. }  apply H35. apply Mk_prop_2. nia.
} rewrite H35.
assert ((-1) ^ i * Mk (N - i - 1) (b/a) * (- (-1) ^ S i * Mk (S i) (b/a))= ( (-1)^ i * (-1)^(S i)) * (-1) * Mk (S i) (b/a) * Mk (N - i - 1) (b/a)). { nra. } rewrite H36.
assert ( (-1)^ ( i + S i) = (-1)^ i * (-1)^ S i). { apply pow_add. } rewrite <-H37.
assert ((-1) ^ (i + S i)= -1). { assert ((i + S i)%nat = S (2*i)). { omega. }rewrite H38. apply pow_1_odd. } rewrite H38.  
assert (((-1 * -1 * Mk (S i) (b/a) * Mk (N - i - 1) (b/a) + -1 * Mk i (b/a) * Mk (N - S i - 1) (b/a)) * / Mk N (b/a))=
         ( Mk (S i) (b/a) * Mk (N - i - 1) (b/a) -  Mk i (b/a) * Mk (N - S i - 1) (b/a))* (/ Mk N (b/a))). { nra. }rewrite H39.
assert (Mk (S i) (b/a) = (b/a) * Mk (S i -1)(b/a) - Mk (S i -2) (b/a)). { apply Mk_recurr. } rewrite H40.
assert ( (S i -1)%nat= i). { omega. } rewrite H41.
assert ( ( S i -2)%nat = (i-1)%nat).  { omega. } rewrite H42. 
assert (((b / a * Mk i (b / a) - Mk (i - 1) (b / a)) * Mk (N - i - 1) (b / a) -
            Mk i (b / a) * Mk (N - S i - 1) (b / a)) * / Mk N (b / a)=
             ( Mk i (b/a) * ((b/a) * Mk (N-i-1) (b/a) - Mk (N- S i -1) (b/a) ) - Mk (i-1) (b/a) * Mk (N-i-1) (b/a)) * (/ Mk N (b/a))).  { nra. } rewrite H43.
assert ( (N- S i -1)%nat = ((N-i)-2)%nat). { omega. }  rewrite H44.
assert (Mk (N-i) (b/a) = (b / a * Mk (N - i - 1) (b / a) - Mk (N - i - 2) (b / a))). { apply Mk_recurr. } rewrite <- H45.
assert ((Mk i (b / a) * Mk (N - i) (b / a) - Mk (i - 1) (b / a) * Mk (N - i - 1) (b / a)) = Mk N (b/a)).
{ apply Mk_prop_3. omega. auto. apply H1. } rewrite H46.
symmetry.  apply Rinv_r_sym. auto.
Qed.


Lemma size_prop_15: forall N:nat, (3<N)%nat -> (N - (N - 2) - 1)%nat= 1%nat.
Proof.
intros. omega.
Qed.

Lemma size_prop_16:  forall N:nat, (3<N)%nat ->(N - pred N - 1)%nat= 0%nat.
Proof.
intros. omega.
Qed.

Lemma size_prop_17:  forall N:nat, (3<N)%nat ->(-1) ^ (N - 2 + (N - 3))=-1.
Proof.
intros. 
assert ((N - 2 + (N - 3))%nat = (2* (N-3) +1)%nat). { omega. } rewrite H0.
assert ((-1) ^ (2 * (N - 3) + 1)= (-1)^ (2 * (N - 3))* (-1)^1). { apply pow_add. } rewrite H1.
assert ((-1) ^ (2 * (N - 3))=1). { apply pow_1_even. } rewrite H2. nra.
Qed.

Lemma size_prop_18:forall N:nat, (3<N)%nat -> (-1) ^ (N - 2 + (N - 2))= 1.
Proof.
intros.
assert ((N - 2 + (N - 2))%nat = (2 * (N-2))%nat). { omega. } rewrite H0.
apply pow_1_even.
Qed.

Lemma size_prop_19: forall N:nat, (3<N)%nat ->(-1) ^ (N - 2 + pred N)=-1.
Proof.
intros.
assert ((N - 2 + pred N)%nat= (2* (N-2) +1)%nat). { omega. } rewrite H0.
assert ((-1) ^ (2 * (N - 2) + 1)= (-1)^ (2 * (N - 2)) * (-1)^1). { apply pow_add. } rewrite H1.
assert ((-1) ^ (2 * (N - 2))=1). { apply pow_1_even. } rewrite H2. nra.
Qed.

Lemma size_prop_20: forall N:nat, (N-0)%nat = N.
Proof.
intros. omega.
Qed.



Lemma size_Nm1: forall (N:nat), (3<N)%nat -> ((N-1)-1)%nat = (N-2)%nat.
Proof.
intros. omega.
Qed.

Lemma size_Nm2: forall (N:nat), (3<N)%nat -> ((N-1)-2)%nat = (N-3)%nat.
Proof.
intros. omega.
Qed.

Lemma Ah_prop_11 (a b:R):forall (N:nat), (3<N)%nat ->  Mk N (b/a) <> 0 -> 0<a -> sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A N a b)
        (N - 2) l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l
        (N - 2))) (N - 3) (pred N) = 1.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
          (N - 3) (pred N)=sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat (N-2)%nat + sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (S (N-2)%nat) (pred N)).
{ apply (sum_n_m_Chasles  (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))  (N-3)%nat (N-2)%nat (pred N)). omega. omega. } rewrite H2.
assert ((S (N - 2))=pred N). { omega. } rewrite H3.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l
                (N - 2))) (N - 3) (N - 2)=sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l
                (N - 2))) (N-3)%nat (N-3)%nat + sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l
                (N - 2))) (S (N-3)%nat) (N-2)%nat).
{ apply (sum_n_m_Chasles   (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l
                (N - 2))) (N-3)%nat (N-3)%nat (N-2)%nat). omega. omega. } rewrite H4.
assert (S (N - 3) = (N-2)%nat). { omega. } rewrite H5.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l
                (N - 2))) (N - 3) (N - 3)=(fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l
                (N - 2))) (N-3)%nat).
{ apply (sum_n_n (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l
                (N - 2))) (N-3)%nat). } rewrite H6.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l
                (N - 2))) (N - 2) (N - 2) =(fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l
                (N - 2))) (N-2)%nat).
{ apply (sum_n_n (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b )
                (N - 2) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l
                (N - 2))) (N-2)%nat). } rewrite H7.
assert (sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A N a b )
              (N - 2) l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l
              (N - 2))) (pred N) (pred N)=(fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A N a b )
              (N - 2) l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l
              (N - 2))) (pred N)).
{ apply (sum_n_n (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A N a b )
              (N - 2) l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l
              (N - 2))) (pred N)). } rewrite H8.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) (N - 2) (N - 3)= (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (N - 2)%nat (N - 3)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (N - 2)%nat (N - 3)%nat). omega. omega. } rewrite H9.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) (N - 2) (N - 2)=  (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (N - 2)%nat (N - 2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (N - 2)%nat (N - 2)%nat). omega. omega. } rewrite H10.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) (N - 2) (pred N)=(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (N - 2)%nat (pred N)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (N - 2)%nat (pred N)%nat). omega. omega. } rewrite H11.
assert (N - 2 <=? N - 3=false). { apply leb_correct_conv. omega. }  rewrite H12. 
assert ( N - 2 <=? N - 2=true). { apply leb_correct. omega. } rewrite H13.
assert (N - 2 <=? pred N=true). { apply leb_correct. omega. }rewrite H14.
unfold Ah.
assert (coeff_mat Hierarchy.zero
         (mk_matrix N N
            (fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0))
         (N - 3) (N - 2)=(fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0) (N-3)%nat (N-2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0) (N-3)%nat (N-2)%nat). omega. omega. } rewrite H15.
assert ( coeff_mat Hierarchy.zero
         (mk_matrix N N
            (fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0))
         (N - 2) (N - 2)=(fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0) (N-2)%nat (N-2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0) (N-2)%nat (N-2)%nat). omega. omega. } rewrite H16.
assert (coeff_mat Hierarchy.zero
             (mk_matrix N N
                (fun i j : nat =>
                 if i =? j
                 then b
                 else
                  if i - j =? one
                  then a
                  else if j - i =? one then a else 0))
             (pred N) (N - 2)= 
                (fun i j : nat =>
                 if i =? j
                 then b
                 else
                  if i - j =? one
                  then a
                  else if j - i =? one then a else 0) (pred N) (N-2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
                 if i =? j
                 then b
                 else
                  if i - j =? one
                  then a
                  else if j - i =? one then a else 0) (pred N) (N-2)%nat). omega. omega. }rewrite H17.
assert (N - 3 =? N - 2=false). { assert ((N - 3 =? N - 2) = false <-> (N-3)%nat <> (N-2)%nat). { apply beq_nat_false_iff. } destruct H18. apply H19. omega. } rewrite H18.
assert (N - 3 - (N - 2) =? one= false). { assert ((N - 3 - (N - 2) =? one) = false <-> (N - 3 - (N - 2))%nat <> one). { apply beq_nat_false_iff. }destruct H19. apply H20. 
assert ((N - 3 - (N - 2))%nat =0%nat). { apply obvio_2. omega. } rewrite H21. discriminate. } rewrite H19.
assert (N - 2 - (N - 3) =? one=true). { assert ((N - 2 - (N - 3))%nat =1%nat). { omega. } rewrite H20. auto. } rewrite H20.
assert (N - 2 =? N - 2=true). { symmetry. apply beq_nat_refl. } rewrite H21.
assert (pred N =? N - 2=false). { assert ((pred N =? N - 2) = false <-> pred N <> (N-2)%nat). { apply beq_nat_false_iff. } destruct H22. apply H23. omega. } rewrite H22.
assert (pred N - (N - 2) =? one=true). { assert ((pred N - (N - 2))%nat=1%nat). { omega. } rewrite H23. auto. } rewrite H23.
assert (mult  (1/a * (-1) ^ (N - 2 + (N - 3)) *   (Mk (N - 3) (b/a) * Mk (N - (N - 2) - 1) (b/a)) *    / Mk N (b/a)) a=
          (1/a * (-1) ^ (N - 2 + (N - 3)) *   (Mk (N - 3) (b/a) * Mk (N - (N - 2) - 1) (b/a)) *    / Mk N (b/a)) * a). { reflexivity. } rewrite H24.
assert (1/a * (-1) ^ (N - 2 + (N - 3)) *(Mk (N - 3) (b/a) * Mk (N - (N - 2) - 1) (b/a)) */ Mk N (b/a) * a=
         (/a * a) * ( ((-1) ^ (N - 2 + (N - 3))*Mk (N - 3) (b/a) * Mk (N - (N - 2) - 1) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H25.
assert (mult  (1/a * (-1) ^ (N - 2 + (N - 2)) * (Mk (N - 2) (b/a) * Mk (N - (N - 2) - 1) (b/a) * / Mk N (b/a)))  b=
        (1/a * (-1) ^ (N - 2 + (N - 2)) * (Mk (N - 2) (b/a) * Mk (N - (N - 2) - 1) (b/a) * / Mk N (b/a))) * b). { reflexivity. } rewrite H26.
assert (1/a * (-1) ^ (N - 2 + (N - 2)) *(Mk (N - 2) (b/a) * Mk (N - (N - 2) - 1) (b/a) * / Mk N (b/a)) *b=
           (b/a) * ( ( (-1) ^ (N - 2 + (N - 2)) * Mk (N - 2) (b/a) * Mk (N - (N - 2) - 1) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H27.
assert (mult  (1/a * (-1) ^ (N - 2 + pred N) *   (Mk (N - 2) (b/a) * Mk (N - pred N - 1) (b/a) * / Mk N (b/a)))  a=
          (1/a * (-1) ^ (N - 2 + pred N) *   (Mk (N - 2) (b/a) * Mk (N - pred N - 1) (b/a) * / Mk N (b/a))) * a). { reflexivity. } rewrite H28.
assert (1/a * (-1) ^ (N - 2 + pred N) *(Mk (N - 2) (b/a) * Mk (N - pred N - 1) (b/a) * / Mk N (b/a)) *a =
         (/a* a) * ( ((-1) ^ (N - 2 + pred N) * Mk (N - 2) (b/a) * Mk (N - pred N - 1) (b/a)) * (/ Mk N (b/a)))).  { nra. } rewrite H29.
assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H30.
assert ((N - (N - 2) - 1)%nat= 1%nat). { apply size_prop_15. apply H. } rewrite H31.
assert ((N - pred N - 1)%nat= 0%nat). { apply size_prop_16. apply H. } rewrite H32.
assert ((-1) ^ (N - 2 + (N - 3))=-1). { apply size_prop_17. apply H. } rewrite H33.
assert ((-1) ^ (N - 2 + (N - 2))= 1). { apply size_prop_18. apply H. } rewrite H34.
assert ((-1) ^ (N - 2 + pred N)=-1). { apply size_prop_19. apply H.  }rewrite H35.
assert ( Mk 1 (b/a) = b/a). { apply Mk_B1. } rewrite H36.
assert ( Mk 0 (b/a) = 1). { apply Mk_B0. } rewrite H37.
assert (1 * (-1 * Mk (N - 3) (b / a) * (b / a) * / Mk N (b / a)) +
          b / a * (1 * Mk (N - 2) (b / a) * (b / a) * / Mk N (b / a)) +
          1 * (-1 * Mk (N - 2) (b / a) * 1 * / Mk N (b / a))=
         ( ((b/a)^2 - 1)* Mk (N-2) (b/a) - (b/a) * Mk (N-3) (b/a)) * (/ Mk N (b/a))). { nra. } rewrite H38.
apply Rmult_eq_reg_r with (Mk N (b/a)).
assert ((((b / a) ^ 2 - 1) * Mk (N - 2) (b / a) - b / a * Mk (N - 3) (b / a)) * / Mk N (b / a) *Mk N (b / a)=
          (((b / a) ^ 2 - 1) * Mk (N - 2) (b / a) - b / a * Mk (N - 3) (b / a)) * ( Mk N (b/a) * (/ Mk N (b/a)))). { nra. } rewrite H39.
assert ( (Mk N (b / a) * / Mk N (b / a))=1). { apply Rinv_r. auto. } rewrite H40.
assert ( Mk N (b/a) = (b/a) * Mk (N-1) (b/a) - Mk (N-2) (b/a)). { apply Mk_recurr. } rewrite H41.
assert ( Mk (N-1) (b/a) = (b/a) * Mk ((N-1)-1)%nat (b/a) - Mk ((N-1)-2)%nat (b/a)). { apply Mk_recurr. }  rewrite H42.
assert (((N-1)-1)%nat= (N-2)%nat). { apply size_Nm1. apply H. }  rewrite H43.
assert ( ((N-1)-2)%nat = (N-3)%nat). { apply size_Nm2. apply H. } rewrite H44.
nra. auto.
Qed.


Lemma Ah_prop_12(a b:R):forall (i N:nat), (2<N)%nat /\ (0<i<(pred N))%nat -> Mk N (b/a) <> 0 -> 0<a ->  sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A N a b ) i
        l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0 1 = 0.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0 1=sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0%nat 0%nat +sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 1%nat 1%nat).
{ apply (sum_n_m_Chasles  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0%nat 0%nat 1%nat). omega. omega. } rewrite H2.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0 0=(fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0%nat).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0%nat). } rewrite H3.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 1 1= (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 1%nat).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 1%nat). } rewrite H4.
unfold Ah.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j : nat =>
         if i0 =? j
         then b
         else
          if i0 - j =? one
          then a
          else if j - i0 =? one then a else 0)) 0 0= (fun i0 j : nat =>
         if i0 =? j
         then b
         else
          if i0 - j =? one
          then a
          else if j - i0 =? one then a else 0) 0%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j : nat =>
         if i0 =? j
         then b
         else
          if i0 - j =? one
          then a
          else if j - i0 =? one then a else 0) 0%nat 0%nat). omega. omega. }rewrite H5.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j : nat =>
         if i0 =? j
         then b
         else
          if i0 - j =? one
          then a
          else if j - i0 =? one then a else 0)) 1 0= (fun i0 j : nat =>
         if i0 =? j
         then b
         else
          if i0 - j =? one
          then a
          else if j - i0 =? one then a else 0) 1%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i0 j : nat =>
         if i0 =? j
         then b
         else
          if i0 - j =? one
          then a
          else if j - i0 =? one then a else 0) 1%nat 0%nat). omega. omega. }rewrite H6.
assert (0 =? 0=true). { auto. }rewrite H7.
assert (1 =? 0=false). { auto. }rewrite H8.
assert (1 - 0 =? one=true). { auto. }rewrite H9.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i 0=(fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i 0%nat). omega. omega. } rewrite H10.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i 1=   (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j : nat =>
         if i0 <=? j
         then
          1 / a * (-1) ^ (i0 + j) *
          (Mk i0 (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j) * (Mk j (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i 1%nat). omega. omega. }rewrite H11.
assert (i <=? 0=false). { apply leb_correct_conv. omega. } rewrite H12.
assert ( i=1%nat \/ (1<i)%nat). { omega. } destruct H13.
+ rewrite H13.
  assert (1 <=? 1=true). { apply leb_correct. omega. } rewrite H14.
  assert ((1 + 0)%nat= 1%nat). { auto. } rewrite H15.
  assert ((1 + 1)%nat = 2%nat). { auto. } rewrite H16.
  assert ( (-1) ^ 1 =-1). { nra. } rewrite H17.
  assert ( (-1)^2= 1). { nra. } rewrite H18.
  assert (mult (1/a * -1 * (Mk 0 (b/a) * Mk (N - 1 - 1) (b/a)) * / Mk N (b/a))  b=
            (1/a * -1 * (Mk 0 (b/a) * Mk (N - 1 - 1) (b/a)) * / Mk N (b/a)) *  b). { reflexivity. } rewrite H19.
  assert (1/a * -1 * (Mk 0 (b/a) * Mk (N - 1 - 1) (b/a)) * / Mk N (b/a) *b=
         (- b/a)* Mk 0 (b/a) * Mk (N - 1 - 1) (b/a) * ( (/ Mk N (b/a)))). { nra. } rewrite H20.
  assert (mult (1/a * 1 * (Mk 1 (b/a) * Mk (N - 1 - 1) (b/a) * / Mk N (b/a)))  a=
          (1/a * 1 * (Mk 1 (b/a) * Mk (N - 1 - 1) (b/a) * / Mk N (b/a))) * a). { reflexivity. } rewrite H21.
  assert (1/a * 1 * (Mk 1 (b/a) * Mk (N - 1 - 1) (b/a) * (/ Mk N (b/a))) *a=
           ( /a * a)* Mk (N - 1 - 1) (b/a)* (Mk 1 (b/a) * (/ Mk N (b/a)))). { nra. } rewrite H22. 
  assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H23.
  assert (- b / a * Mk 0 (b / a) * Mk (N - 1 - 1) (b / a) * / Mk N (b / a) +1 * Mk (N - 1 - 1) (b / a) * (Mk 1 (b / a) * / Mk N (b / a))=
             Mk (N - 1 - 1) (b / a) * ( (-b/a) * Mk 0 (b/a) + Mk 1 (b/a)) * (/ Mk N (b/a))). { nra. } rewrite H24.
  assert ((- b / a * Mk 0 (b / a) + Mk 1 (b / a))=0).
  { assert (Mk 0 (b/a) =1).  {  apply Mk_B0. } rewrite H25.
    assert (Mk 1 (b/a) = b/a). { apply Mk_B1. } rewrite H26.
    nra.
  } rewrite H25. nra.
+ assert (i <=? 1=false). { apply leb_correct_conv. omega. } rewrite H14.
  assert (Mk 0 (b/a)=1). { apply Mk_B0. } rewrite H15.
  assert (Mk 1 (b/a)=b/a). { apply Mk_B1. } rewrite H16.
  assert ((i + 0)%nat= i). { nia. } rewrite H17.
  assert ((-1) ^ (i + 1)= (-1)^i * (-1)^1). { apply pow_add. } rewrite H18.
  assert (mult  (1/a * (-1) ^ i * (1 * Mk (N - i - 1) (b/a)) * / Mk N (b/a))  b=
             (1/a * (-1) ^ i * (1 * Mk (N - i - 1) (b/a)) * / Mk N (b/a)) * b). { reflexivity. } rewrite H19.
  assert (1/a* (-1) ^ i * (1 * Mk (N - i - 1) (b/a)) * / Mk N (b/a) *b=
          ( (b/a) * (-1)^i * Mk (N - i - 1) (b/a)) * ( (/ Mk N (b/a)))). { nra. } rewrite H20.
  assert (mult  (1/a * ((-1) ^ i * (-1) ^ 1) * ((b/a) * Mk (N - i - 1) (b/a)) *   / Mk N (b/a)) a=
          (1/a * ((-1) ^ i * (-1) ^ 1) * ((b/a) * Mk (N - i - 1) (b/a)) *   / Mk N (b/a)) * a). { reflexivity. } rewrite H21.
  assert (1/a * ((-1) ^ i * (-1) ^ 1) * ((b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a) * a=
            ( (/a * a)* (-b/a) * (-1)^i * Mk (N - i - 1) (b/a))  * ( (/ Mk N (b/a)))). { nra. } rewrite H22.
  assert (1=/a * a ). { apply Rinv_l_sym. nra.  } rewrite <- H23. nra.
Qed. 


Lemma Ah_prop_13(a b:R): forall (i j N:nat), (2<N)%nat -> (i<>j)%nat -> j=1%nat -> (0<i<pred N)%nat -> 0< a ->  Mk N (b/a) <> 0 -> sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A N a b ) i
        l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0  2 = 0.
Proof.
intros.
assert (sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 2 =sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 1%nat + sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 2%nat 2%nat).
{ apply (sum_n_m_Chasles  (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 1%nat 2%nat). omega. omega. } rewrite H5.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 1 =sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 0%nat + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 1%nat 1%nat).
{ apply (sum_n_m_Chasles (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 0%nat 1%nat). omega. omega. }rewrite H6.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 0=(fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat). } rewrite H7.
assert (sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 1 1= (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 1%nat).
{ apply (sum_n_n (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 1%nat). } rewrite H8.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 2 2=(fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 2%nat).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 2%nat). } rewrite H9.
unfold Ah.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0)) 0 1= (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 0%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 0%nat 1%nat). omega. omega. } rewrite H10.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0)) 1 1= (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 1%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 1%nat 1%nat). omega. omega. } rewrite H11.
assert (  coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0)) 2 1=  (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 2%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) 2%nat 1%nat). omega. omega. } rewrite H12.
assert ( 0 =? 1=false). { auto. } rewrite H13.
assert (0 - 1 =? one=false).  { auto. } rewrite H14.
assert (1 - 0 =? one=true). { auto. } rewrite H15.
assert ( 1 =? 1=true). { auto. }rewrite H16.
assert (2 =? 1=false). { auto. }rewrite H17.
assert (2 - 1 =? one=true). { auto. } rewrite H18.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i 0=(fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i 0%nat). omega. omega. } rewrite H19.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i 1= (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i 1%nat). omega. omega. }rewrite H20.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i 2=  (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i 2%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i 2%nat). omega. omega. } rewrite H21.
assert (i <=? 0=false). { apply leb_correct_conv. omega. }rewrite H22.
assert ( i <=? 1=false). { apply leb_correct_conv. omega. } rewrite H23.
assert ( i=2%nat \/ (2< i)%nat).  { omega. } destruct H24.
+ rewrite H24.
  assert (2 <=? 2=true). { apply leb_correct. omega. } rewrite H25.
  assert ( (-1) ^ (2 + 0) = 1). { assert ((2 + 0)%nat =2%nat). { auto. } rewrite H26. nra. } rewrite H26.
  assert ((-1) ^ (2 + 1)= -1). { assert ((2 + 1)%nat = 3%nat). { auto. }rewrite H27. nra. } rewrite H27.
  assert ((-1) ^ (2 + 2)= 1). { assert ((2 + 2)%nat= 4%nat). { auto. }rewrite H28. nra. } rewrite H28. 
  assert (mult (1/a * 1 * (Mk 0 (b/a) * Mk (N - 2 - 1) (b/a)) * / Mk N (b/a))  a= 
           (1/a * 1 * (Mk 0 (b/a) * Mk (N - 2 - 1) (b/a)) * / Mk N (b/a)) * a). { reflexivity. } rewrite H29.
  assert (1/a* 1 * (Mk 0 (b/a) * Mk (N - 2 - 1) (b/a)) * / Mk N (b/a) *a=
          ((/a * a) * Mk (N - 2 - 1) (b/a)) * ( Mk 0 (b/a) * (/ Mk N (b/a)))). { nra. } rewrite H30.
  assert (mult (1/a* -1 * (Mk 1 (b/a) * Mk (N - 2 - 1) (b/a)) * / Mk N (b/a)) b =
              (1/a * -1 * (Mk 1 (b/a) * Mk (N - 2 - 1) (b/a)) * / Mk N (b/a)) * b). { reflexivity. } rewrite H31.
  assert (1/a * -1 * (Mk 1 (b/a) * Mk (N - 2 - 1) (b/a)) * / Mk N (b/a) *b=
             (- b/a) * Mk (N - 2 - 1) (b/a) * ( ( Mk 1 (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H32.
  assert (mult (1/a* 1 * (Mk 2 (b/a) * Mk (N - 2 - 1) (b/a) * / Mk N (b/a)))  a=
            (1/a * 1 * (Mk 2 (b/a) * Mk (N - 2 - 1) (b/a) * / Mk N (b/a))) * a). { reflexivity. } rewrite H33.
  assert (1/a * 1 * (Mk 2 (b/a) * Mk (N - 2 - 1) (b/a) * / Mk N (b/a)) *a=
           ((/a* a)) * Mk (N - 2 - 1) (b/a) * ( Mk 2 (b/a) * (/ Mk N (b/a)))). { nra. } rewrite H34.
  assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H35.
  assert (1 * Mk (N - 2 - 1) (b / a) * (Mk 0 (b / a) * / Mk N (b / a)) +
            - b / a * Mk (N - 2 - 1) (b / a) * (Mk 1 (b / a) * / Mk N (b / a)) +
            1 * Mk (N - 2 - 1) (b / a) * (Mk 2 (b / a) * / Mk N (b / a))=
           Mk (N - 2 - 1) (b / a) * (Mk 0 (b/a) + (-b/a) * Mk 1 (b/a) + Mk 2 (b/a)) * (/Mk N (b/a))).
  { nra. } rewrite H36.
  assert ((Mk 0 (b / a) + - b / a * Mk 1 (b / a) + Mk 2 (b / a))=0).
  { assert ( Mk 2 (b/a) = (b/a) * Mk 1 (b/a) - Mk 0 (b/a)). { apply Mk_recurr. } nra. } rewrite H37. nra.

+ assert (i <=? 2=false). { apply leb_correct_conv. omega. }rewrite H25.
  assert (mult  (1/a * (-1) ^ (i + 0) * (Mk 0 (b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a)) a=
          (1/a * (-1) ^ (i + 0) * (Mk 0 (b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a)) * a). { reflexivity. } rewrite H26.
  assert (1/a * (-1) ^ (i + 0) * (Mk 0 (b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a) * (a)=
          (/a * a) * Mk (N - i - 1) (b/a) * ( ((-1) ^ (i + 0) * Mk 0 (b/a) ) * (/ Mk N (b/a)))). { nra. } rewrite H27.
  assert (mult  (1/a* (-1) ^ (i + 1) * (Mk 1 (b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a)) b=
           (1/a * (-1) ^ (i + 1) * (Mk 1 (b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a)) * b). { reflexivity. } rewrite H28.
  assert (1/a * (-1) ^ (i + 1) * (Mk 1 (b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a) * b=
              (b/a) * Mk (N - i - 1) (b/a) * ( ( (-1) ^ (i + 1)  * Mk 1 (b/a)) * (/ Mk N (b/a)))). { nra. }rewrite H29.
  assert (mult  (1/a * (-1) ^ (i + 2) * (Mk 2 (b/a) * Mk (N - i - 1) (b/a)) * / Mk N (b/a)) a=
             (1/a * (-1) ^ (i + 2) * (Mk 2 (b/a) * Mk (N - i - 1) (b/a)) * / Mk N (b/a)) *  a). { reflexivity. }rewrite H30.
  assert (1/a * (-1) ^ (i + 2) * (Mk 2 (b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a) * a =
           (/a * a) * Mk (N - i - 1) (b/a) * ( ( (-1) ^ (i + 2) *Mk 2 (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H31.
  assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H32.
  assert ((-1) ^ (i + 0)= (-1)^i * (-1)^0). { apply pow_add. } rewrite H33.
  assert ((-1) ^ (i + 1) =(-1)^i * (-1)^1). { apply pow_add. } rewrite H34.
  assert ((-1) ^ (i + 2)= (-1)^i * (-1)^2). { apply pow_add. }rewrite H35. 
  assert (1 * Mk (N - i - 1) (b / a) * ((-1) ^ i * (-1) ^ 0 * Mk 0 (b / a) * / Mk N (b / a)) +
            b / a * Mk (N - i - 1) (b / a) * ((-1) ^ i * (-1) ^ 1 * Mk 1 (b / a) * / Mk N (b / a)) +
            1 * Mk (N - i - 1) (b / a) * ((-1) ^ i * (-1) ^ 2 * Mk 2 (b / a) * / Mk N (b / a))=
           Mk (N - i - 1) (b / a) * (-1)^ i * ((-1) ^ 0 * Mk 0 (b / a) + (-1) ^ 1 * (b/a) *Mk 1 (b / a) + (-1) ^ 2 * Mk 2 (b / a)) * (/ Mk N (b/a))).
  { nra.  } rewrite H36.
  assert (((-1) ^ 0 * Mk 0 (b / a) + (-1) ^ 1 * (b / a) * Mk 1 (b / a) + (-1) ^ 2 * Mk 2 (b / a))=0).
  { simpl. assert (Mk 0 (b/a) =1). { apply Mk_B0. } rewrite H37.
    assert (Mk 1 (b / a)=b/a). { apply Mk_B1. } rewrite H38.
    assert (Mk 2 (b/a)= (b/a) * Mk 1 (b/a) - Mk 0 (b/a)). { apply Mk_recurr. } rewrite H39. rewrite H37. rewrite H38. nra.
  } rewrite H37. nra.
Qed.


Lemma size_prop_21(a b:R): forall (j N:nat), (2<N)%nat ->  (1<j<pred N)%nat -> 0<a -> Mk (N - pred j - 1) (b/a)= Mk (N- (pred (j+1)))%nat (b/a).
Proof.
intros. assert (pred (j + 1)=j). { omega. } rewrite H2.
assert ((N - pred j - 1)%nat = (N- (pred j +1))%nat). { omega. } rewrite H3.
assert ((pred j + 1)%nat = j). { omega. } rewrite H4. reflexivity.
Qed.

Lemma size_prop_22 (a b:R) : forall (j N:nat), (2<N)%nat ->  (1<j<pred N)%nat -> 0<a -> Mk (N - j - 1) (b/a) = Mk (N - (j+1))%nat (b/a).
Proof.
intros. assert ((N - j - 1)%nat = (N - (j + 1))%nat). { omega. }rewrite H2. reflexivity.
Qed.


Lemma size_prop_23 (a b:R) : forall (j N:nat), (2<N)%nat ->  (1<j<pred N)%nat -> 0<a -> Mk (N - S j - 1) (b/a) = Mk (N - S(j+1))%nat (b/a).
Proof.
intros. assert ((N - S j - 1)%nat = (N - S (j + 1))%nat). { omega. } rewrite H2. reflexivity.
Qed.

Lemma size_prop_24 : forall (i j N:nat), (2<N)%nat -> (0<i<pred N)%nat -> (1<j<pred N)%nat ->(i + pred j)%nat = ((i-1) + pred (j+1))%nat.
Proof.
intros. omega.
Qed.
 
Lemma size_prop_25: forall (i j N:nat), (2<N)%nat -> (0<i<pred N)%nat -> (1<j<pred N)%nat ->(i + j)%nat = ((i-1)+ (j+1))%nat.
Proof.
intros. omega.
Qed.  

Lemma size_prop_26: forall (i j N:nat), (2<N)%nat -> (0<i<pred N)%nat -> (1<j<pred N)%nat ->(i + S j)%nat = ( (i-1)+ S (j+1))%nat.
Proof.
intros. omega.
Qed.
   
Lemma Ah_prop_14 (a b:R) :forall (i j N:nat), (2<N)%nat -> 0<a -> Mk N (b/a) <> 0 ->(0<i<pred N)%nat -> (1<j<pred N)%nat -> i <> j ->  
sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A N a b ) i
        l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
  (pred j) (S j) = 0.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
          (pred j) (S j)=sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (pred j) j + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (S j) (S j)).
{ apply (sum_n_m_Chasles  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j) j (S j)). omega. omega. } rewrite H5.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
          (pred j) j =sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (pred j) (pred j) + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (S (pred j )) j).
{ apply (sum_n_m_Chasles    (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j) (pred j) j). omega. omega. } rewrite H6.
assert ((S (pred j))=j). { omega. } rewrite H7.
assert (sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
            (pred j) (pred j)=(fun l : nat =>
             mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (pred j)).
{ apply (sum_n_n (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (pred j)). } rewrite H8.
assert (sum_n_m  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) j j =(fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) j).
{ apply (sum_n_n (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) j). } rewrite H9.
assert (sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
        (S j) (S j)=(fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
        (S j) ).
{ apply (sum_n_n (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (S j) ). } rewrite H10.
unfold Ah.
assert (coeff_mat Hierarchy.zero
         (mk_matrix N N
            (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else if i0 - j0 =? one then a else if j0 - i0 =? one then a else 0)) 
         (pred j) j=  (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else if i0 - j0 =? one then a else if j0 - i0 =? one then a else 0) (pred j) j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
               if i0 =? j0
               then b
               else
                if i0 - j0 =? one
                then a
                else if j0 - i0 =? one then a else 0) (pred j) j). omega. omega. } rewrite H11.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0)) j j=(fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) j j).
{ apply (coeff_mat_bij 0 (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) j j). omega. omega. }  rewrite H12.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0)) 
     (S j) j=(fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) (S j) j).
{ apply (coeff_mat_bij 0 (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else if j0 - i0 =? one then a else 0) (S j) j). omega. omega. } rewrite H13.
assert (pred j =? j=false). { assert((pred j =? j) = false <-> (pred j) <> j). { apply beq_nat_false_iff. } destruct H14. apply H15. omega. } rewrite H14.
assert ( pred j - j =? one=false). { assert ((pred j - j)%nat = 0%nat). { apply obvio_2. omega. } rewrite H15. auto. } rewrite H15.
assert (j - pred j =? one=true). { assert ((j - pred j)%nat = 1%nat). { omega. }rewrite H16. auto. }  rewrite H16.
assert (j =? j=true). { symmetry. apply beq_nat_refl. } rewrite H17.
assert (S j =? j=false). { assert ((S j =? j) = false <-> S j <> j). { apply beq_nat_false_iff. } destruct H18. apply H19. omega.  } rewrite H18.
assert (S j - j =? one=true). { assert ((S j - j)%nat = 1%nat). { omega. } rewrite H19. auto. } rewrite H19.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i (pred j)= (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (pred j)).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (pred j)). omega. omega. } rewrite H20.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i j =(fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i j). omega. omega. } rewrite H21.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i (S j)= (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (S j)).
{ apply (coeff_mat_bij Hierarchy.zero(fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (S j)). omega. omega. }rewrite H22.
assert ( (i<j)%nat \/ (i>j)%nat). { omega. } destruct H23.
+ assert (i <=? pred j=true). { apply leb_correct. omega. } rewrite H24.
  assert ( i <=? j=true). { apply leb_correct. omega. }rewrite H25.
  assert (i <=? S j =true). { apply leb_correct. omega. } rewrite H26.
  assert (mult  (1/a* (-1) ^ (i + pred j) * (Mk i (b/a) * Mk (N - pred j - 1) (b/a) * / Mk N (b/a)))  a=
           (1/a * (-1) ^ (i + pred j) * (Mk i (b/a) * Mk (N - pred j - 1) (b/a) * / Mk N (b/a))) * a). { reflexivity. } rewrite H27.
  assert (1/a * (-1) ^ (i + pred j) *(Mk i (b/a) * Mk (N - pred j - 1) (b/a) * / Mk N (b/a)) *a=
          (/a * a)* Mk i (b/a) * ( ((-1) ^ (i + pred j) * Mk (N - pred j - 1) (b/a)) * (/ Mk N (b/a)))). { nra. }rewrite H28.
  assert (mult  (1/a* (-1) ^ (i + j) *   (Mk i (b/a) * Mk (N - j - 1) (b/a) * / Mk N (b/a)))  b=
            (1/a * (-1) ^ (i + j) *   (Mk i (b/a) * Mk (N - j - 1) (b/a) * / Mk N (b/a))) * b). { reflexivity. }rewrite H29.
  assert (1/a * (-1) ^ (i + j) *(Mk i (b/a) * Mk (N - j - 1) (b/a) * / Mk N (b/a)) *b=
            (b/a)* Mk i (b/a) * ( ((-1) ^ (i + j)  * Mk (N - j - 1) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H30.
  assert (mult  (1/a * (-1) ^ (i + S j) *   (Mk i (b/a) * Mk (N - S j - 1) (b/a) * / Mk N (b/a)))  a=
          (1/a * (-1) ^ (i + S j) *   (Mk i (b/a) * Mk (N - S j - 1) (b/a) * / Mk N (b/a))) * a). { reflexivity. } rewrite H31.
  assert (1/a * (-1) ^ (i + S j) *(Mk i (b/a) * Mk (N - S j - 1) (b/a) * / Mk N (b/a)) *a=
          (/a * a)* Mk i (b/a) * ( ( (-1) ^ (i + S j)*Mk (N - S j - 1) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H32.
  assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H33.
  assert (1 * Mk i (b/a) *((-1) ^ (i + pred j) * Mk (N - pred j - 1) (b/a) * / Mk N (b/a)) +
            (b/a) * Mk i (b/a) *((-1) ^ (i + j)  * Mk (N - j - 1) (b/a) * / Mk N (b/a)) +
            1 * Mk i (b/a) *((-1) ^ (i + S j) * Mk (N - S j - 1) (b/a) * / Mk N (b/a))=
           1* Mk i (b/a) * ( ((-1) ^ (i + pred j) * Mk (N - pred j - 1) (b/a)+
            (-1) ^ (i + j) * (b/a) * Mk (N - j - 1) (b/a) + (-1) ^ (i + S j) * Mk (N - S j - 1) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H34.
  assert (((-1) ^ (i + pred j) * Mk (N - pred j - 1) (b/a) +  (-1) ^ (i + j) * (b/a) * Mk (N - j - 1) (b/a) +  (-1) ^ (i + S j) * Mk (N - S j - 1) (b/a))=0).
  { assert (Mk (N - pred j - 1) (b/a)= Mk (N- (pred (j+1)))%nat (b/a)). { apply size_prop_21. apply H. apply H3. nra. }rewrite H35.
    assert (Mk (N - j - 1) (b/a) = Mk (N - (j+1))%nat (b/a)). { apply size_prop_22. apply H. apply H3. nra.   } rewrite H36.
    assert ( Mk (N - S j - 1) (b/a) = Mk (N - S(j+1))%nat (b/a)). { apply size_prop_23. apply H. apply H3.  nra. } rewrite H37.
    assert ((i + pred j)%nat = ((i-1) + pred (j+1))%nat). { apply (size_prop_24 i j N). apply H. apply H2. apply H3. } rewrite H38.
    assert ((i + j)%nat = ((i-1)+ (j+1))%nat). { apply (size_prop_25 i j N). apply H. apply H2. apply H3. } rewrite H39.
    assert ((i + S j)%nat = ( (i-1)+ S (j+1))%nat). { apply (size_prop_26 i j N). apply H. apply H2. apply H3. }rewrite H40. 
    assert ((-1) ^ (i - 1 + pred (j + 1)) = (-1)^ (i-1)%nat * (-1)^ (pred (j+1))%nat). { apply pow_add. } rewrite H41.
    assert ((-1) ^ (i - 1 + (j + 1))= (-1)^ (i-1)%nat * (-1)^ (j+1)%nat). { apply pow_add. }rewrite H42.
    assert ((-1) ^ (i - 1 + S (j + 1))= (-1)^ (i-1)%nat * (-1)^ (S (j+1))). { apply pow_add. }rewrite H43.
    assert ((-1) ^ (i - 1) * (-1) ^ pred (j + 1) * Mk (N - pred (j + 1)) (b/a) +
            (-1) ^ (i - 1) * (-1) ^ (j + 1) * (b/a) * Mk (N - (j + 1)) (b/a) +
            (-1) ^ (i - 1) * (-1) ^ S (j + 1) * Mk (N - S (j + 1)) (b/a)= ( (-1)^ (i-1)%nat) *
            ((-1) ^ pred (j + 1) * Mk (N - pred (j + 1)) (b/a)+ (-1) ^ (j + 1) * (b/a) * Mk (N - (j + 1)) (b/a)
              +(-1) ^ S (j + 1) * Mk (N - S (j + 1)) (b/a))). { nra. } rewrite H44.
    assert (((-1) ^ pred (j + 1) * Mk (N - pred (j + 1)) (b/a) + (-1) ^ (j + 1) * (b/a) * Mk (N - (j + 1)) (b/a) +
              (-1) ^ S (j + 1) * Mk (N - S (j + 1)) (b/a))=0). { apply Mk_prop_1. apply H. nia. } rewrite H45. nra.
  } rewrite H35. nra.
+ assert (i <=? pred j=false). { apply leb_correct_conv. omega. }rewrite H24.
  assert (i <=? j=false). { apply leb_correct_conv. omega. }rewrite H25.
  assert ( i = S j \/ (i> S j)%nat). { omega. } destruct H26.
  - rewrite H26.
    assert (S j <=? S j=true). { apply leb_correct. omega. } rewrite H27.
    assert (mult  (1/a * (-1) ^ (S j + pred j) *   (Mk (pred j) (b/a) * Mk (N - S j - 1) (b/a)) * / Mk N (b/a)) a=
             (1/a * (-1) ^ (S j + pred j) *   (Mk (pred j) (b/a) * Mk (N - S j - 1) (b/a)) * / Mk N (b/a)) * a). { reflexivity. } rewrite H28.
    assert (1/a * (-1) ^ (S j + pred j) *(Mk (pred j) (b/a) * Mk (N - S j - 1) (b/a)) * / Mk N (b/a) * a=
            (/a * a)*  Mk (N - S j - 1) (b/a) * ( ((-1) ^ (S j + pred j) * Mk (pred j) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H29.
    assert (mult  (1/a * (-1) ^ (S j + j) * (Mk j (b/a) * Mk (N - S j - 1) (b/a)) */ Mk N (b/a)) b=
              (1/a* (-1) ^ (S j + j) * (Mk j (b/a) * Mk (N - S j - 1) (b/a)) */ Mk N (b/a)) * b). { reflexivity. } rewrite H30.
    assert (1/a * (-1) ^ (S j + j) * (Mk j (b/a) * Mk (N - S j - 1) (b/a)) */ Mk N (b/a) * b=
              (b/a)*  Mk (N - S j - 1) (b/a) * ( ((-1) ^ (S j + j) *Mk j (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H31.
    assert (mult  (1/a* (-1) ^ (S j + S j) *   (Mk (S j) (b/a) * Mk (N - S j - 1) (b/a) * / Mk N (b/a)))  a=
              (1/a* (-1) ^ (S j + S j) *   (Mk (S j) (b/a) * Mk (N - S j - 1) (b/a) * / Mk N (b/a))) * a). { reflexivity. }rewrite H32.
    assert (1/a * (-1) ^ (S j + S j) *(Mk (S j) (b/a) * Mk (N - S j - 1) (b/a) * / Mk N (b/a)) *a=
             (/a * a)*  Mk (N - S j - 1) (b/a)  * ( ( (-1) ^ (S j + S j)* Mk (S j) (b/a)) * (/ Mk N (b/a)))). { nra. }rewrite H33.
    assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H34.
    assert ( 1 * Mk (N - S j - 1) (b/a) *((-1) ^ (S j + pred j) * Mk (pred j) (b/a) * / Mk N (b/a)) +
            (b/a) * Mk (N - S j - 1) (b/a) *((-1) ^ (S j + j)  * Mk j (b/a) * / Mk N (b/a)) +
            1 * Mk (N - S j - 1) (b/a) *((-1) ^ (S j + S j) * Mk (S j) (b/a) * / Mk N (b/a))=
            ( 1*  Mk (N - S j - 1) (b/a)) * ( ((-1) ^ (S j + pred j) * Mk (pred j) (b/a)+
              (-1) ^ (S j + j) * (b/a) * Mk j (b/a) + (-1) ^ (S j + S j) * Mk (S j) (b/a) ) * (/ Mk N (b/a)))). { nra. }rewrite H35.
    assert (((-1) ^ (S j + pred j) * Mk (pred j) (b/a) +  (-1) ^ (S j + j) * (b/a) * Mk j (b/a) +  (-1) ^ (S j + S j) * Mk (S j) (b/a))=0).
    { assert ((-1) ^ (S j + pred j)= (-1)^ (S j) * (-1)^ (pred j)). { apply pow_add. } rewrite H36.
      assert ((-1) ^ (S j + j) = (-1)^ (S j) * (-1)^j). { apply pow_add. } rewrite H37.
      assert ((-1) ^ (S j + S j)= (-1)^ ( S j) * (-1)^ (S j)). { apply pow_add. } rewrite H38. 
      assert ((-1) ^ S j * (-1) ^ pred j * Mk (pred j) (b/a) +(-1) ^ S j * (-1) ^ j * (b/a) * Mk j (b/a) +
                  (-1) ^ S j * (-1) ^ S j * Mk (S j) (b/a) = (-1)^ (S j) * 
                ( (-1) ^ pred j * Mk (pred j) (b/a) + (-1) ^ j * (b/a) * Mk j (b/a) + (-1) ^ S j * Mk (S j) (b/a))). { nra. } rewrite H39.
      assert (((-1) ^ pred j * Mk (pred j) (b/a) + (-1) ^ j * (b/a) * Mk j (b/a) +
                  (-1) ^ S j * Mk (S j) (b/a)) = 0). { apply Mk_prop_2. nia. } rewrite H40. nra.
    } rewrite H36. nra.
  - assert (i <=? S j=false). { apply leb_correct_conv. omega. } rewrite H27.
    assert (mult  (1/a * (-1) ^ (i + pred j) *   (Mk (pred j) (b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a)) a=
              (1/a * (-1) ^ (i + pred j) *   (Mk (pred j) (b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a)) *a). { reflexivity. }rewrite H28.
    assert (1/a* (-1) ^ (i + pred j) *(Mk (pred j) (b/a) * Mk (N - i - 1) (b/a)) * / Mk N (b/a) *a=
              (/a * a) *  Mk (N - i - 1) (b/a) * ( ( (-1) ^ (i + pred j) * Mk (pred j) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H29.
    assert (mult  (1/a * (-1) ^ (i + j) * (Mk j (b/a) * Mk (N - i - 1) (b/a)) * / Mk N (b/a)) b =
              (1/a * (-1) ^ (i + j) * (Mk j (b/a) * Mk (N - i - 1) (b/a)) * / Mk N (b/a)) * b). { reflexivity. }rewrite H30.
    assert (1/a * (-1) ^ (i + j) * (Mk j (b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a) * b =
               (b/a)*  Mk (N - i - 1) (b/a) * ( (  (-1) ^ (i + j) * Mk j (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H31.
    assert (mult  (1/a * (-1) ^ (i + S j) * (Mk (S j) (b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a)) a=
               (1/a * (-1) ^ (i + S j) * (Mk (S j) (b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a)) * a). { reflexivity. } rewrite H32.
    assert (1/a* (-1) ^ (i + S j) * (Mk (S j) (b/a) * Mk (N - i - 1) (b/a)) */ Mk N (b/a) * a=
               (/a * a)*  Mk (N - i - 1) (b/a) * ( (  (-1) ^ (i + S j) * Mk (S j) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H33.
    assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H34.
    assert (1 * Mk (N - i - 1) (b/a) *((-1) ^ (i + pred j) * Mk (pred j) (b/a) * / Mk N (b/a)) +
            (b/a) * Mk (N - i - 1) (b/a) *((-1) ^ (i + j)  * Mk j (b/a) * / Mk N (b/a)) +
            1* Mk (N - i - 1) (b/a) *((-1) ^ (i + S j) * Mk (S j) (b/a) * / Mk N (b/a))=
             1*  Mk (N - i - 1) (b/a) * ( ((-1) ^ (i + pred j) * Mk (pred j) (b/a)+
              (-1) ^ (i + j) * (b/a) * Mk j (b/a) + (-1) ^ (i + S j) * Mk (S j) (b/a) ) * (/ Mk N (b/a)))). { nra. } rewrite H35.
    assert (((-1) ^ (i + pred j) * Mk (pred j) (b/a) +  (-1) ^ (i + j) * (b/a) * Mk j (b/a) + (-1) ^ (i + S j) * Mk (S j) (b/a))=0).
    { assert ((-1) ^ (i + pred j) = (-1)^ i * (-1)^ (pred j)). { apply pow_add. } rewrite H36.
      assert ((-1) ^ (i + j)= (-1)^i * (-1)^j). { apply pow_add. } rewrite H37.
      assert ((-1) ^ (i + S j) = (-1)^i * (-1)^ (S j)). { apply pow_add. }rewrite H38.
      assert ((-1) ^ i * (-1) ^ pred j * Mk (pred j) (b/a) +(-1) ^ i * (-1) ^ j * (b/a) * Mk j (b/a) +
                (-1) ^ i * (-1) ^ S j * Mk (S j) (b/a)= (-1)^ i * 
            ( (-1) ^ pred j * Mk (pred j) (b/a) + (-1) ^ j * (b/a) * Mk j (b/a) + (-1) ^ S j * Mk (S j) (b/a))). { nra. }rewrite H39.
      assert (((-1) ^ pred j * Mk (pred j) (b/a) + (-1) ^ j * (b/a) * Mk j (b/a) + (-1) ^ S j * Mk (S j) (b/a))=0). { apply Mk_prop_2. nia. } rewrite H40. nra.
    } rewrite H36. nra.
Qed.


Lemma size_prop_27 (a b:R): forall (N:nat), (2<N)%nat -> 0<a -> Mk (N - (N - 3) - 1) (b/a) = Mk 2 (b/a).
Proof.
intros. assert ((N - (N - 3) - 1)%nat = 2%nat). { omega. }rewrite H1. reflexivity.
Qed.

Lemma size_prop_28 (a b:R): forall (N:nat), (2<N)%nat -> 0<a -> Mk (N - (N - 2) - 1) (b/a) = Mk 1 (b/a).
Proof.
intros. assert ((N - (N - 2) - 1)%nat = 1%nat). { omega. } rewrite H1. reflexivity.
Qed.

Lemma size_prop_29 (a b:R): forall (N:nat), (2<N)%nat -> 0<a ->  Mk (N - pred N - 1) (b/a) = Mk 0 (b/a).
Proof.
intros. assert ((N - pred N - 1)%nat = 0%nat). { omega. } rewrite H1. reflexivity.
Qed.

Lemma Ah_prop_15 (a b:R): forall (i j N:nat), (2<N)%nat -> (0 < i < pred N)%nat -> i <> j -> j= (N-2)%nat-> 0<a -> Mk N (b/a) <> 0-> 
sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A N a b ) i
        l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l
        (N - 2))) (N - 3) (pred N)=0.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
          (N - 3) (pred N)=sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat (N-2)%nat + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (S (N-2)%nat) (pred N)).
{ apply (sum_n_m_Chasles    (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))  (N-3)%nat (N-2)%nat (pred N)). omega. omega. }rewrite H5.
assert ((S (N - 2))= pred N). { omega.  }rewrite H6.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
          (N - 3) (N - 2)=sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat (N-3)%nat + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (S (N-3)%nat) (N-2)%nat).
{ apply (sum_n_m_Chasles  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat (N-3)%nat (N-2)%nat). omega. omega. }rewrite H7.
assert ((S (N - 3))= (N-2)%nat). { omega. }rewrite H8.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
          (N - 3) (N - 3) = (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat). } rewrite H9.
assert (sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
            (N - 2) (N - 2)= (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-2)%nat).
{ apply (sum_n_n  (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-2)%nat). } rewrite H10.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
          (pred N) (pred N)=  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (pred N)).
{ apply (sum_n_n  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (pred N)). } rewrite H11.
unfold Ah.
assert ( coeff_mat Hierarchy.zero
         (mk_matrix N N
            (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0)) 
         (N - 3) (N - 2)= (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0) (N-3)%nat (N-2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0) (N-3)%nat (N-2)%nat). omega. omega. } rewrite H12.
assert (coeff_mat Hierarchy.zero
         (mk_matrix N N
            (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0)) 
         (N - 2) (N - 2)=  (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0) (N-2)%nat (N-2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0) (N-2)%nat (N-2)%nat). omega. omega. }rewrite H13.
assert (coeff_mat Hierarchy.zero
         (mk_matrix N N
            (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0))
         (pred N) (N - 2)=(fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0) (pred N) (N-2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0) (pred N) (N-2)%nat). omega. omega. } rewrite H14.
assert ( N - 3 =? N - 2=false). { assert ((N - 3 =? N - 2) = false <-> (N-3)%nat <> (N-2)%nat). { apply beq_nat_false_iff. } destruct H15. apply H16. omega. } rewrite H15.
assert (N - 3 - (N - 2) =? one=false). { assert ((N - 3 - (N - 2))%nat =0%nat). { apply obvio_2. omega. } rewrite H16. auto. } rewrite H16.
assert (N - 2 - (N - 3) =? one=true). { assert ((N - 2 - (N - 3))%nat = 1%nat). { omega. } rewrite H17. auto. } rewrite H17.
assert (N - 2 =? N - 2=true). { symmetry. apply beq_nat_refl. }rewrite H18.
assert (pred N =? N - 2=false). { assert ((pred N =? N - 2) = false <-> pred N <> (N-2)%nat). { apply beq_nat_false_iff. } destruct H19. apply H20. omega. } rewrite H19.
assert ( pred N - (N - 2) =? one=true). { assert ((pred N - (N - 2))%nat= 1%nat). { omega. } rewrite H20. auto. } rewrite H20.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i (N - 3)=  (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (N - 3)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (N - 3)%nat). omega. omega. } rewrite H21.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i (N - 2)=  (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (N - 2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (N - 2)%nat). omega. omega. }rewrite H22.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i (pred N)= (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (pred N)).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (pred N)). omega. omega. } rewrite H23.
assert ( i <=? pred N=true). { apply leb_correct. omega. } rewrite H24.
assert (i <=? N - 2=true). { apply leb_correct. omega. } rewrite H25.
assert ( i <=? N - 3=true). { apply leb_correct. omega. } rewrite H26.
assert (mult  (1/a * (-1) ^ (i + (N - 3)) *   (Mk i (b/a) * Mk (N - (N - 3) - 1) (b/a) * / Mk N (b/a)))  a=
           (1/a * (-1) ^ (i + (N - 3)) *   (Mk i (b/a) * Mk (N - (N - 3) - 1) (b/a) * / Mk N (b/a))) * a).  { reflexivity. } rewrite H27.
assert (1/a * (-1) ^ (i + (N - 3)) *(Mk i (b/a) * Mk (N - (N - 3) - 1) (b/a) * / Mk N (b/a)) *a=
         (/a * a) * Mk i (b/a) * ( (  (-1) ^ (i + (N - 3))*Mk (N - (N - 3) - 1) (b/a)) * (/ Mk N (b/a)))). { nra. }rewrite H28.
assert ( mult  (1/a * (-1) ^ (i + (N - 2)) *   (Mk i (b/a) * Mk (N - (N - 2) - 1) (b/a) * / Mk N (b/a)))  b=
        (1/a * (-1) ^ (i + (N - 2)) *   (Mk i (b/a) * Mk (N - (N - 2) - 1) (b/a) * / Mk N (b/a))) * b). { reflexivity. }rewrite H29.
assert ( 1/a * (-1) ^ (i + (N - 2)) *(Mk i (b/a) * Mk (N - (N - 2) - 1) (b/a) * / Mk N (b/a)) *b =
           (b/a) * Mk i (b/a) * ( ((-1) ^ (i + (N - 2))  * Mk (N - (N - 2) - 1) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H30.
assert (mult  (1/a * (-1) ^ (i + pred N) * (Mk i (b/a) * Mk (N - pred N - 1) (b/a) * / Mk N (b/a)))  a=
           (1/a * (-1) ^ (i + pred N) * (Mk i (b/a) * Mk (N - pred N - 1) (b/a) * / Mk N (b/a))) *  a). { reflexivity. }rewrite H31.
assert (1/a * (-1) ^ (i + pred N) *(Mk i (b/a) * Mk (N - pred N - 1) (b/a) * / Mk N (b/a)) *a=
         (/a * a)* Mk i (b/a)  * ( ( (-1) ^ (i + pred N) * Mk (N - pred N - 1) (b/a)) * (/ Mk N (b/a)))). { nra. }rewrite H32.
assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H33.
assert (1 * Mk i (b/a) *((-1) ^ (i + (N - 3)) * Mk (N - (N - 3) - 1) (b/a) * / Mk N (b/a)) +
          (b/a) * Mk i (b/a) *((-1) ^ (i + (N - 2))  * Mk (N - (N - 2) - 1) (b/a) * / Mk N (b/a)) +
         1 * Mk i (b/a) *((-1) ^ (i + pred N) * Mk (N - pred N - 1) (b/a) * / Mk N (b/a)) =
          1 * Mk i (b/a) * ( ( (-1) ^ (i + (N - 3)) * Mk (N - (N - 3) - 1) (b/a)+
          (-1) ^ (i + (N - 2)) * (b/a) * Mk (N - (N - 2) - 1) (b/a) + (-1) ^ (i + pred N) * Mk (N - pred N - 1) (b/a)) * (/ Mk N (b/a)))). 
{ nra. } rewrite H34.
assert (((-1) ^ (i + (N - 3)) * Mk (N - (N - 3) - 1) (b/a) +  (-1) ^ (i + (N - 2)) * (b/a) * Mk (N - (N - 2) - 1) (b/a) +
            (-1) ^ (i + pred N) * Mk (N - pred N - 1) (b/a))=0).
{ assert (Mk (N - (N - 3) - 1) (b/a) = Mk 2 (b/a)). { apply size_prop_27. apply H.  nra. } rewrite H35.
  assert (Mk (N - (N - 2) - 1) (b/a) = Mk 1 (b/a)). { apply size_prop_28. apply H.  nra. } rewrite H36.
  assert ( Mk (N - pred N - 1) (b/a) = Mk 0 (b/a)). { apply size_prop_29. apply H.  nra. } rewrite H37.
  assert ((i + (N - 2))%nat = ((i+(N-3))+1)%nat). { omega. } rewrite H38.
  assert ((i + pred N)%nat = ((i+(N-3))+2)%nat). { omega. } rewrite H39.
  assert ((-1) ^ (i + (N - 3) + 1)= (-1) ^ (i + (N - 3)) * (-1)^1). { apply pow_add. }rewrite H40.
  assert ((-1) ^ (i + (N - 3) + 2)= (-1) ^ (i + (N - 3)) * (-1)^2). { apply pow_add. } rewrite H41.
  assert ((-1) ^ (i + (N - 3)) * Mk 2 (b/a) +(-1) ^ (i + (N - 3)) * (-1) ^ 1 * (b/a) * Mk 1 (b/a) +
              (-1) ^ (i + (N - 3)) * (-1) ^ 2 * Mk 0 (b/a)= (-1) ^ (i + (N - 3)) * 
          (Mk 2 (b/a) + (-1) *  (b/a) * Mk 1 (b/a) +  Mk 0 (b/a))). { nra. } rewrite H42.
  assert ((Mk 2 (b/a) + -1 * (b/a) * Mk 1 (b/a) + Mk 0 (b/a))=0).
  { assert (Mk 0 (b/a) =1). { apply Mk_B0. } rewrite H43.
    assert ( Mk 1 (b/a)=b/a). {  apply Mk_B1. } rewrite H44.
    assert ( Mk 2 (b/a) = (b/a) * Mk 1 (b/a) - Mk 0 (b/a)). { apply Mk_recurr. } rewrite H45. rewrite H43. rewrite H44. nra.
  } rewrite H43. nra.
} rewrite H35. nra.
Qed.


Lemma Ah_prop_16 (a b:R) : forall (N:nat), (N=3%nat)-> 0<a -> Mk 3 (b/a) <> 0 -> sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A 3 a b)
        (pred N) l)
     (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0
  2 = 0.
Proof.
intros.
assert (sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A 3 a b) (pred N) l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0 2 =sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A 3 a b) (pred N) l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat 1%nat + sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A 3 a b) (pred N) l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 2%nat 2%nat).
{ apply (sum_n_m_Chasles  (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A 3 a b) (pred N) l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat 1%nat 2%nat). omega. omega. }rewrite H2.
assert (sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A 3 a b) 
              (pred N) l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0 1 =sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A 3 a b) 
              (pred N) l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat 0%nat + sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A 3 a b) 
              (pred N) l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 1%nat 1%nat).
{ apply (sum_n_m_Chasles  (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A 3 a b) 
              (pred N) l)
           (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1))  0%nat 0%nat 1%nat). omega. omega. }rewrite H3.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A 3 a b) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0 0 =  (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A 3 a b) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat).
{ apply (sum_n_n (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A 3 a b) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 0%nat). } rewrite H4.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A 3 a b) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 1 1=   (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A 3 a b) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1))  1%nat).
{ apply (sum_n_n (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A 3 a b) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1))  1%nat). } rewrite H5.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A 3 a b) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 2 2= (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A 3 a b) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 2%nat).
{ apply (sum_n_n (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A 3 a b) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah  3 a b a ) l 1)) 2%nat). } rewrite H6.
unfold Ah.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0)) 0 1=(fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then 1
          else if j - i =? one then a else 0) 0%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 0%nat 1%nat). omega. omega. }rewrite H7.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0)) 1 1=  (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 1%nat 1%nat).
{ apply (coeff_mat_bij 0 (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 1%nat 1%nat). omega. omega. } rewrite H8.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0)) 2 1=  (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 2%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 2%nat 1%nat). omega. omega. }rewrite H9.
assert (0 =? 1=false). { auto. } rewrite H10.
assert ( 0 - 1 =? one=false). { assert ( (0 - 1)%nat = 0%nat). { apply obvio_2. omega. } rewrite H11. auto. } rewrite H11.
assert (1 - 0 =? one =true). { auto. } rewrite H12.
assert ( 1 =? 1=true). { auto. }rewrite H13.
assert ( 2 =? 1=false). { auto. }rewrite H14.
assert (2 - 1 =? one=true). { auto. } rewrite H15.
unfold inverse_A. rewrite H.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a))) (pred 3) 0=(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) (pred 3) 0%nat).
{ apply (coeff_mat_bij  Hierarchy.zero(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) (pred 3) 0%nat). omega. omega. } rewrite H16.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a))) (pred 3) 1=(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) (pred 3) 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) (pred 3) 1%nat). omega. omega. } rewrite H17.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 3 3
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a))) (pred 3) 2=   (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) (pred 3) 2%nat).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (3 - j - 1) (b / a) * / Mk 3 (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (3 - i - 1) (b / a)) *
          / Mk 3 (b / a)) (pred 3) 2%nat). omega. omega. }rewrite H18.
assert ( pred 3 <=? 0 = false). { apply leb_correct_conv. omega. } rewrite H19.
assert (pred 3 <=? 1=false). { apply leb_correct_conv. omega. }rewrite H20.
assert (pred 3 <=? 2=true). { apply leb_correct. omega. }rewrite H21.
assert ((3 - pred 3 - 1)%nat = 0%nat). { auto. } rewrite H22.
assert ((3 - 2 - 1)%nat = 0%nat). { auto. }rewrite H23.
assert ( (-1) ^ (pred 3 + 0)=1). { assert (pred 3=2%nat). { auto. }rewrite H24. simpl. nra. }rewrite H24.
assert ((-1) ^ (pred 3 + 1)=-1). { simpl. nra. }rewrite H25.
assert ((-1) ^ (pred 3 + 2)=1). { simpl. nra. }rewrite H26.
assert (mult (1 / a * 1 * (Mk 0 (b / a) * Mk 0 (b / a)) * / Mk 3 (b / a)) a=
          (1 / a * 1 * (Mk 0 (b / a) * Mk 0 (b / a)) * / Mk 3 (b / a)) * a). { reflexivity. } rewrite H27.
assert (1 / a * 1 * (Mk 0 (b / a) * Mk 0 (b / a)) * / Mk 3 (b / a) * a= 
              (/a * a) * Mk 0 (b/a) * Mk 0 (b/a) * (/ Mk 3 (b/a))). { nra. } rewrite H28.
assert (mult (1 / a * -1 * (Mk 1 (b / a) * Mk 0 (b / a)) * / Mk 3 (b / a)) b= 
                  (1 / a * -1 * (Mk 1 (b / a) * Mk 0 (b / a)) * / Mk 3 (b / a)) * b). { reflexivity. } rewrite H29.
assert (1 / a * -1 * (Mk 1 (b / a) * Mk 0 (b / a)) * / Mk 3 (b / a) * b= (-b/a) * Mk 1 (b/a) * Mk 0 (b/a) * (/ Mk 3 (b/a))).
{ nra. } rewrite H30.
assert (mult (1 / a * 1 * (Mk (pred 3) (b / a) * Mk 0 (b / a) * / Mk 3 (b / a))) a = 
            (1 / a * 1 * (Mk (pred 3) (b / a) * Mk 0 (b / a) * / Mk 3 (b / a))) * a). { reflexivity. } rewrite H31.
assert (1 / a * 1 * (Mk (pred 3) (b / a) * Mk 0 (b / a) * / Mk 3 (b / a)) * a =
              (/a * a) * Mk (pred 3) (b/a) * Mk 0 (b/a) * (/ Mk 3 (b/a))). { nra. } rewrite H32.
assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H33. 
assert (1 * Mk 0 (b / a) * Mk 0 (b / a) * / Mk 3 (b / a) +
            - b / a * Mk 1 (b / a) * Mk 0 (b / a) * / Mk 3 (b / a) +
            1 * Mk (pred 3) (b / a) * Mk 0 (b / a) * / Mk 3 (b / a)=
          Mk 0 (b/a) * (Mk 0 (b/a) + (-b/a) * Mk 1 (b/a) + Mk (pred 3) (b/a))* (/ Mk 3 (b/a))). {  nra. } rewrite H34.
assert ((Mk 0 (b / a) + - b / a * Mk 1 (b / a) + Mk (pred 3) (b / a)) =0).
{ assert (pred 3 = 2%nat). { auto. } rewrite H35. 
  assert ( Mk 2 (b/a) = (b/a) * Mk 1 (b/a) - Mk 0 (b/a)). { apply Mk_recurr.  } rewrite H36.
  assert (Mk 0 (b/a) = 1). { apply Mk_B0. } rewrite H37.
  assert (Mk 1 (b/a) = b/a). { apply Mk_B1. } rewrite H38. nra.
} rewrite H35. nra.
Qed.


Lemma size_prop_32: forall N:nat, (2< N)%nat ->  ((-1) ^ (pred N + (N - 2)) =-1).
Proof.
intros.
assert ((pred N + (N - 2))%nat = ( 2* (N-2) +1)%nat). { omega. }rewrite H0. 
assert ((-1) ^ (2 * (N - 2) + 1)= (-1)^ (2 * (N - 2))%nat * (-1)^1). { apply pow_add. }rewrite H1. 
assert ((-1) ^ (2 * (N - 2)) =1). { apply pow_1_even. } rewrite H2. nra.
Qed.

Lemma size_prop_33 (a b:R): forall N:nat, (2< N)%nat -> 0<a -> Mk N (b/a) = (-1)^ (pred 1) * Mk (N-0)%nat (b/a).
Proof.
intros. simpl. assert ((N - 0)%nat = N). { omega. } rewrite H1. nra.
Qed.

Lemma size_prop_34 (a b:R): forall N:nat, (2< N)%nat -> 0 < a-> (-b/a) * Mk (pred N) (b/a) = (-1)^1 * (b/a) * Mk (N-1)%nat (b/a).
Proof.
intros.
simpl. assert (pred N = (N-1)%nat). { omega. }rewrite H1. nra.
Qed.

Lemma size_prop_35: forall N:nat , (2<N)%nat -> pred N = (N - 1)%nat.
Proof.
intros. omega.
Qed.

Lemma size_prop_36: forall N:nat, (2<N)%nat ->(-1) ^ (pred N + (N - 3)) =1.
Proof.
intros. assert ((pred N + (N - 3))%nat = (2* (N-2))%nat). { omega. } rewrite H0. apply pow_1_even.
Qed.


Lemma size_prop_37: forall N:nat, (2<N)%nat ->(-1) ^ (pred N + (N - 2))=-1.
Proof.
intros. assert ((pred N + (N - 2))%nat= (2* (N-2) + 1)%nat). { omega. }rewrite H0. 
assert ( (-1) ^ (2 * (N - 2) + 1)= (-1)^ (2 * (N - 2)) * (-1)^1). { apply pow_add. } rewrite H1.
assert ((-1) ^ (2 * (N - 2))=1). { apply pow_1_even. } rewrite H2. nra.
Qed.

Lemma size_prop_38:forall N:nat, (2<N)%nat ->(-1) ^ (pred N + pred N)=1.
Proof.
intros. assert ( (pred N + pred N)%nat = (2* (pred N))%nat). { omega. } rewrite H0. apply pow_1_even.
Qed.

Lemma Ah_prop_17 (a b:R) : forall (N:nat), (2<N)%nat ->  0<a -> Mk N (b/a) <> 0 -> sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A N a b )
        (pred N) l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l
        (N - 2))) (N - 3) (pred N) = 0.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
          (N - 3) (pred N)= sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat (N-2)%nat + sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (S (N-2)%nat) (pred N)).
{ apply (sum_n_m_Chasles  (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat (N-2)%nat (pred N)). omega. omega. } rewrite H2.
assert ((S (N - 2)) = pred N). { omega. } rewrite H3.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
          (N - 3) (N - 2)=sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat (N-3)%nat + 
          sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (S (N-3)%nat) (N-2)%nat).
{ apply (sum_n_m_Chasles  (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat (N-3)%nat (N-2)%nat). omega. omega. }rewrite H4.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
          (N - 3) (N - 3)= (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat).
{ apply (sum_n_n (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-3)%nat). } rewrite H5.
assert ((S (N - 3)) = (N-2)%nat). { omega. }rewrite H6.
assert (sum_n_m
            (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                  (pred N) l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
            (N - 2) (N - 2)= (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                  (pred N) l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-2)%nat).
{ apply (sum_n_n (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                  (pred N) l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (N-2)%nat). } rewrite H7.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
          (pred N) (pred N)= (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (pred N)).
{ apply (sum_n_n (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2))) (pred N)). } rewrite H8.
unfold Ah.
assert ( coeff_mat Hierarchy.zero
         (mk_matrix N N
            (fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0)) 
         (N - 3) (N - 2)=(fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0) (N-3)%nat (N-2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
             if i =? j
             then b
             else
              if i - j =? one
              then a
              else if j - i =? one then a else 0) (N-3)%nat (N-2)%nat). omega. omega. }rewrite H9.
assert (coeff_mat Hierarchy.zero
           (mk_matrix N N
              (fun i j : nat =>
               if i =? j
               then b
               else
                if i - j =? one
                then a
                else if j - i =? one then a else 0)) 
           (N - 2) (N - 2)= (fun i j : nat =>
               if i =? j
               then b
               else
                if i - j =? one
                then a
                else if j - i =? one then a else 0) (N-2)%nat (N-2)%nat). 
{ apply ( coeff_mat_bij Hierarchy.zero (fun i j : nat =>
               if i =? j
               then b
               else
                if i - j =? one
                then a
                else if j - i =? one then a else 0) (N-2)%nat (N-2)%nat). omega. omega. } rewrite H10.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0)) 
     (pred N) (N - 2)=(fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) (pred N) (N-2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) (pred N) (N-2)%nat). omega. omega. } rewrite H11.
assert ( N - 3 =? N - 2=false). { assert ((N - 3 =? N - 2) = false <-> (N-3)%nat <> (N-2)%nat). { apply beq_nat_false_iff. } destruct H12. apply H13. omega. } rewrite H12.
assert ( N - 3 - (N - 2) =? one=false). { assert ((N - 3 - (N - 2))%nat = 0%nat). { apply obvio_2. omega. } rewrite H13. auto. } rewrite H13.
assert (N - 2 - (N - 3) =? one =true). { assert ((N - 2 - (N - 3))%nat = 1%nat). { omega. } rewrite H14. auto. } rewrite H14.
assert (N - 2 =? N - 2=true). { symmetry. apply beq_nat_refl. } rewrite H15.
assert ( pred N =? N - 2=false). { assert ((pred N =? N - 2) = false <-> pred N <> (N-2)%nat). { apply beq_nat_false_iff. }destruct H16. apply H17. omega. } rewrite H16.
assert (  pred N - (N - 2) =? one=true). { assert ((pred N - (N - 2))%nat = 1%nat). { omega. }rewrite H17. auto. }rewrite H17.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) (pred N) (N - 3)= (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) (N - 3)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) (N - 3)%nat). omega. omega. }rewrite H18.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) (pred N) (N - 2)=  (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) (N - 2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) (N - 2)%nat). omega. omega. } rewrite H19.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) (pred N) (pred N)=(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) (pred N)).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) (pred N)). omega. omega. } rewrite H20.
assert (pred N <=? N - 3=false). { apply leb_correct_conv. omega. } rewrite H21.
assert (pred N <=? N - 2=false). { apply leb_correct_conv. omega. } rewrite H22.
assert ( pred N <=? pred N=true). { apply leb_correct. omega. }rewrite H23.
assert (mult  (1/a* (-1) ^ (pred N + (N - 3)) *   (Mk (N - 3 ) (b/a) * Mk (N - pred N-1) (b/a)) * / Mk N (b/a)) a=
         (1/a * (-1) ^ (pred N + (N - 3)) *   (Mk (N - 3) (b/a) * Mk (N - pred N-1) (b/a)) * / Mk N (b/a)) *a). { reflexivity. } rewrite H24.
assert (1/a * (-1) ^ (pred N + (N - 3)) *(Mk (N - 3) (b/a) * Mk (N - pred N-1) (b/a)) */ Mk N (b/a) * a=
         (/a * a) * ( ((-1) ^ (pred N + (N - 3)) * Mk (N - 3) (b/a) * Mk (N - pred N-1) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H25.
assert (mult  (1/a * (-1) ^ (pred N + (N - 2)) *   (Mk (N - 2) (b/a) * Mk (N - pred N-1) (b/a)) *  / Mk N (b/a)) b=
           (1/a * (-1) ^ (pred N + (N - 2)) *   (Mk (N - 2) (b/a) * Mk (N - pred N-1) (b/a)) *  / Mk N (b/a))*b). { reflexivity. } rewrite H26.
assert (1/a * (-1) ^ (pred N + (N - 2)) *(Mk (N - 2 ) (b/a) * Mk (N - pred N-1) (b/a)) * / Mk N (b/a) * b=
          (b/a) * ( ( (-1) ^ (pred N + (N - 2)) *Mk (N - 2) (b/a) * Mk (N - pred N-1) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H27.
assert (mult  (1/a * (-1) ^ (pred N + pred N) *   (Mk (pred N) (b/a) * Mk (N - pred N-1) (b/a) * / Mk N (b/a))) a=
           (1/a * (-1) ^ (pred N + pred N) *   (Mk (pred N ) (b/a) * Mk (N - pred N-1) (b/a) * / Mk N (b/a))) *  a). { reflexivity. } rewrite H28.
assert ( (1/a * (-1) ^ (pred N + pred N) *   (Mk (pred N ) (b/a) * Mk (N - pred N-1) (b/a) * / Mk N (b/a))) *  a=
          (/a * a) * ( ( (-1) ^ (pred N + pred N)  * Mk (pred N) (b/a) *  Mk (N - pred N-1) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H29.
assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H30.
assert (1 *((-1) ^ (pred N + (N - 3)) * Mk (N - 3) (b/a) * Mk (N - pred N-1) (b/a) * / Mk N (b/a)) +
       (b/a) *((-1) ^ (pred N + (N - 2))  * Mk (N - 2) (b/a) * Mk (N - pred N-1) (b/a) * / Mk N (b/a)) +
        1 *((-1) ^ (pred N + pred N) * Mk (pred N) (b/a) * Mk (N - pred N-1) (b/a) * / Mk N (b/a))=
         Mk (N - pred N-1) (b/a) * ( ((-1) ^ (pred N + (N - 3)) * Mk (N - 3) (b/a) )+
          (-1) ^ (pred N + (N - 2)) * (b/a) * Mk (N - 2) (b/a)+(-1) ^ (pred N + pred N) * Mk (pred N) (b/a) ) * (/Mk N (b/a))).
{ nra. } rewrite H31.
assert (((-1) ^ (pred N + (N - 3)) * Mk (N - 3) (b/a) + (-1) ^ (pred N + (N - 2)) * (b/a) * Mk (N - 2) (b/a) +
              (-1) ^ (pred N + pred N) * Mk (pred N) (b/a)) =0).
{ assert ((-1) ^ (pred N + (N - 3)) =1). { apply size_prop_36. apply H.  }rewrite H32.
  assert ((-1) ^ (pred N + (N - 2))=-1). { apply size_prop_37. apply H.  }rewrite H33.
  assert ((-1) ^ (pred N + pred N)=1). { apply size_prop_38. apply H.  }rewrite H34.
  assert ((pred N) = (N-1)%nat). { apply size_prop_35. apply H. } rewrite H35.
  assert (-1 * (b/a) * Mk (N - 2) (b/a)= (-b/a) *  Mk (N - 2) (b/a)). { nra. }rewrite H36.
  assert (-1 * Mk (N - 3) (b/a) + (b/a) * Mk (N - 2) (b/a) + -1 * Mk (N - 1) (b/a)=0 -> 
            1 * Mk (N - 3) (b/a) + (-b/a) * Mk (N - 2) (b/a) + 1 * Mk (N - 1) (b/a) = 0). { nra. }  apply H37.
  assert (-1 * Mk (N - 3) (b/a)= (-1)^ (S 2) * Mk (N-3)%nat (b/a)). { nra. } rewrite H38.
  assert ((b/a) * Mk (N - 2) (b/a)= (-1)^2 * (b/a) *  Mk (N - 2) (b/a)). {nra. }  rewrite H39.
  assert (-1 * Mk (N - 1) (b/a) = (-1)^ (pred 2) * Mk (N - 1) (b/a)). { simpl. nra. } rewrite H40.
  assert ((-1) ^ 3 * Mk (N - 3) (b/a) + (-1) ^ 2 * (b/a) * Mk (N - 2) (b/a) +(-1) ^ pred 2 * Mk (N - 1) (b/a)=
            (-1) ^ pred 2 * Mk (N - 1) (b/a)+ (-1) ^ 2 *(b/a) * Mk (N - 2) (b/a) + (-1) ^ 3 * Mk (N - 3) (b/a)). { nra. } rewrite H41.
  apply Mk_prop_1. apply H. nia. 
} rewrite H32. nra.
Qed.


Lemma Ah_prop_18(a b:R) : forall (N:nat) , (3<N)%nat -> 0<a -> Mk N (b/a) <> 0 -> sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N)
        l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0
  2 = 0.
Proof.
intros.
assert (sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 2 =sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 1%nat + sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 2%nat 2%nat).
{ apply (sum_n_m_Chasles  (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 1%nat 2%nat). omega. omega. }rewrite H2.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 1=sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 0%nat + sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 1%nat 1%nat).
{ apply (sum_n_m_Chasles  (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 0%nat 1%nat). omega. omega. }rewrite H3.
assert (sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A N a b ) 
              (pred N) l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 0=(fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A N a b ) 
              (pred N) l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat).
{ apply (sum_n_n (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A N a b ) 
              (pred N) l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat). } rewrite H4.
assert (sum_n_m
        (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A N a b ) 
              (pred N) l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 1 1=(fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A N a b ) 
              (pred N) l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 1%nat).
{ apply (sum_n_n (fun l : nat =>
         mult
           (coeff_mat Hierarchy.zero (inverse_A N a b ) 
              (pred N) l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 1%nat). } rewrite H5.
assert (sum_n_m
          (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 2 2 = (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 2%nat).
{ apply (sum_n_n (fun l : nat =>
           mult
             (coeff_mat Hierarchy.zero (inverse_A N a b ) 
                (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 2%nat). } rewrite H6.
unfold Ah.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0)) 0 1= (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 0%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 0%nat 1%nat). omega. omega. }rewrite H7.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0)) 1 1=(fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 1%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 1%nat 1%nat). omega. omega. }rewrite H8.
assert (  coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0)) 2 1=(fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 2%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one
          then a
          else if j - i =? one then a else 0) 2%nat 1%nat). omega. omega. }rewrite H9.
assert (0 =? 1=false). { auto. }rewrite H10.
assert (0 - 1 =? one=false). { auto. } rewrite H11.
assert (1 - 0 =? one=true). { auto. }rewrite H12.
assert (1 =? 1=true). { auto. }rewrite H13.
assert (2 =? 1=false). { auto. }rewrite H14.
assert ( 2 - 1 =? one=true). { auto. }rewrite H15.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) (pred N) 0=  (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) 0%nat).
{ apply (coeff_mat_bij  Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) 0%nat). omega. omega. } rewrite H16.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) (pred N) 1=  (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) 1%nat). omega. omega. }rewrite H17.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) (pred N) 2= (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) 2%nat).
{ apply (coeff_mat_bij  Hierarchy.zero(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) 2%nat). omega. omega. } rewrite H18.
assert (pred N <=? 0=false). { apply leb_correct_conv. omega. } rewrite H19.
assert (pred N <=? 1=false). { apply leb_correct_conv. omega. }rewrite H20.
assert (pred N <=? 2=false).  { apply leb_correct_conv. omega. } rewrite H21.
assert (mult  (1/a * (-1) ^ (pred N + 0) *   (Mk 0 (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a))  a=
        (1/a * (-1) ^ (pred N + 0) *   (Mk 0 (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a)) *  a). { reflexivity. }rewrite H22.
assert (1/a * (-1) ^ (pred N + 0) * (Mk 0 (b/a) * Mk (N - pred N - 1) (b/a)) */ Mk N (b/a) * a =
          ( /a * a) * Mk (N - pred N - 1) (b/a) * ( ((-1) ^ (pred N + 0)* Mk 0 (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H23.
assert (mult  (1/a * (-1) ^ (pred N + 1) *   (Mk 1 (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a))  b=
            (1/a * (-1) ^ (pred N + 1) *   (Mk 1 (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a)) * b). { reflexivity. } rewrite H24.
assert (1/a* (-1) ^ (pred N + 1) * (Mk 1 (b/a) * Mk (N - pred N - 1) (b/a)) */ Mk N (b/a) * b=
         ( b/a) * Mk (N - pred N - 1) (b/a) * ( ((-1) ^ (pred N + 1)  * Mk 1 (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H25.
assert (mult  (1/a * (-1) ^ (pred N + 2) *   (Mk 2 (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a))  a =
          (1/a * (-1) ^ (pred N + 2) *   (Mk 2 (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a)) * a). { reflexivity. } rewrite H26.
assert (1/a * (-1) ^ (pred N + 2) * (Mk 2 (b/a) * Mk (N - pred N - 1) (b/a)) */ Mk N (b/a) * a=
           ( /a * a) * Mk (N - pred N - 1) (b/a) * ( ((-1) ^ (pred N + 2)* Mk 2 (b/a) ) * (/ Mk N (b/a)))). { nra. } rewrite H27.
assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H28.
assert (1 * Mk (N - pred N - 1) (b/a) *((-1) ^ (pred N + 0) * Mk 0 (b/a) * / Mk N (b/a)) +
           (b/a) * Mk (N - pred N - 1) (b/a) *((-1) ^ (pred N + 1)  * Mk 1 (b/a) * / Mk N (b/a)) +
            1 * Mk (N - pred N - 1) (b/a) *((-1) ^ (pred N + 2) * Mk 2 (b/a) * / Mk N (b/a))=
           1 * Mk (N - pred N - 1) (b/a) * ( ( (-1) ^ (pred N + 0) * Mk 0 (b/a)+
          (-1) ^ (pred N + 1) * (b/a) * Mk 1 (b/a) + (-1) ^ (pred N + 2) * Mk 2 (b/a)) * (/ Mk N (b/a)))). { nra. }rewrite H29.
assert (((-1) ^ (pred N + 0) * Mk 0 (b/a) +  (-1) ^ (pred N + 1) * (b/a) * Mk 1 (b/a) +  (-1) ^ (pred N + 2) * Mk 2 (b/a))=0).
{ assert ((-1) ^ (pred N + 0)= (-1)^ (pred N) * (-1)^0). { apply pow_add. }rewrite H30.
  assert ((-1) ^ (pred N + 1) = (-1)^ (pred N) * (-1)^1). { apply pow_add. } rewrite H31.
  assert ((-1) ^ (pred N + 2)= (-1)^ (pred N) * (-1)^2). { apply pow_add. } rewrite H32.
  assert ((-1) ^ pred N * (-1) ^ 0 * Mk 0 (b/a) +(-1) ^ pred N * (-1) ^ 1 * (b/a) * Mk 1 (b/a) +(-1) ^ pred N * (-1) ^ 2 * Mk 2 (b/a)=
          (-1)^(pred N) * ( ((-1) ^ 0 * Mk 0 (b/a)+(-1) ^ 1 * (b/a) * Mk 1 (b/a) + (-1) ^ 2 * Mk 2 (b/a)))). { nra. } rewrite H33.
  simpl. assert (Mk 0 (b/a)=1). { apply Mk_B0. }rewrite H34.
  assert (Mk 1 (b/a)=(b/a)). { apply Mk_B1. } rewrite H35. 
  assert (Mk 2 (b/a)=(b/a) * Mk 1 (b/a) -Mk 0 (b/a)). { apply Mk_recurr. } rewrite H36. rewrite H34. rewrite H35. nra.
} rewrite H30. nra.
Qed.



Lemma Ah_prop_19 (a b:R) : forall (i j N:nat), (2<N)%nat ->i <> j -> i = pred N ->  (1 < j < pred N)%nat -> 0<a -> Mk N (b/a) <> 0 ->sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (inverse_A N a b ) i
        l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
  (pred j) (S j) = 0.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
          (pred j) (S j)=sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j) j +  sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (S j) (S j)).
{ apply (sum_n_m_Chasles  (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (pred j) j (S j)). omega. omega. } rewrite H5.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
          (pred j) j =sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (pred j) (pred j) + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (S (pred j)) j).
{ apply (sum_n_m_Chasles (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j) (pred j) j). omega. omega. }rewrite H6.
assert ((S (pred j))=j). { omega. } rewrite H7.
assert (sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
        (pred j) (pred j)=(fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j)).
{ apply (sum_n_n (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j)). } rewrite H8.
assert (sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) j j= (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) j ).
{ apply (sum_n_n (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) j ). } rewrite H9.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
          (S j) (S j)=(fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
          (S j)).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
          (S j)). } rewrite H10.
unfold Ah.
assert (coeff_mat Hierarchy.zero
         (mk_matrix N N
            (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0))
         (pred j) j=(fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0) (pred j) j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0) (pred j) j). omega. omega. }rewrite H11.
assert ( coeff_mat Hierarchy.zero
         (mk_matrix N N
            (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0)) j j=  (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0) j j).
{ apply (coeff_mat_bij 0 (fun i0 j0 : nat =>
             if i0 =? j0
             then b
             else
              if i0 - j0 =? one
              then a
              else if j0 - i0 =? one then a else 0) j j). omega. omega. } rewrite H12.
assert ( coeff_mat Hierarchy.zero
           (mk_matrix N N
              (fun i0 j0 : nat =>
               if i0 =? j0
               then b
               else
                if i0 - j0 =? one
                then a
                else if j0 - i0 =? one then a else 0)) 
           (S j) j= (fun i0 j0 : nat =>
               if i0 =? j0
               then b
               else
                if i0 - j0 =? one
                then a
                else if j0 - i0 =? one then a else 0) (S j) j).
{ apply (coeff_mat_bij 0 (fun i0 j0 : nat =>
               if i0 =? j0
               then b
               else
                if i0 - j0 =? one
                then a
                else if j0 - i0 =? one then a else 0) (S j) j). omega. omega. }rewrite H13.
assert (pred j =? j=false). { assert ((pred j =? j) = false <-> pred j <> j). {  apply beq_nat_false_iff. } destruct H14. apply H15. omega. } rewrite H14.
assert ( pred j - j =? one=false). { assert ((pred j - j)%nat = 0%nat). { apply obvio_2. omega. }rewrite H15. auto. } rewrite H15.
assert ( j - pred j =? one=true). { assert ((j - pred j)%nat =1%nat). { omega. } rewrite H16. auto. }rewrite H16.
assert ( j =? j=true). { symmetry. apply beq_nat_refl. } rewrite H17.
assert (S j =? j=false). { assert ((S j =? j) = false <-> S j <> j).  { apply beq_nat_false_iff. } destruct H18. apply H19. omega. }rewrite H18.
assert (S j - j =? one=true). { assert ((S j - j)%nat = 1%nat). { omega. }rewrite H19. auto. } rewrite H19. 
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i (pred j)=  (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (pred j)).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (pred j)). omega. omega. }rewrite H20.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i j= (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i j). omega. omega. } rewrite H21.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a))) i (S j)=  (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (S j)).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
         if i0 <=? j0
         then
          1 / a * (-1) ^ (i0 + j0) *
          (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
          / Mk N (b / a)) i (S j)). omega. omega. } rewrite H22. rewrite H1.
assert ( pred N <=? pred j=false). { apply leb_correct_conv. omega. } rewrite H23.
assert ( pred N <=? j=false). { apply leb_correct_conv. omega. } rewrite H24.
assert ( S j = pred N \/ (S j < pred N)%nat). { omega. } destruct H25.
+ rewrite H25.
  assert (pred N <=? pred N=true). { apply leb_correct. omega. }rewrite H26.
  assert (j = (N-2)%nat). { omega. } rewrite H27.
  assert ( pred (N - 2)= (N-3)%nat). { omega. } rewrite H28.
  assert ((-1) ^ (pred N + pred N) =1). { assert ((pred N + pred N)%nat= (2* (N-1))%nat). { omega. } rewrite H29. apply pow_1_even. } rewrite H29.
  assert ((-1) ^ (pred N + (N - 2))=-1). { assert ((pred N + (N - 2))%nat = S (2 * (N-2))%nat). { omega. } rewrite H30. apply pow_1_odd. } rewrite H30.
  assert ((-1) ^ (pred N + (N - 3))=1). { assert ((pred N + (N - 3))%nat = (2 * (N-2))%nat). { omega. } rewrite H31. apply pow_1_even. } rewrite H31.
  assert ((N - pred N)%nat = 1%nat). { omega. } rewrite H32.
  assert ((1 - 1)%nat =0%nat). { auto. } rewrite H33.
  assert (mult (1/a* 1 * (Mk (N - 3) (b/a) * Mk 0 (b/a)) * / Mk N (b/a))  a=
             (1/a * 1 * (Mk (N - 3) (b/a) * Mk 0 (b/a)) * / Mk N (b/a)) * a). { reflexivity. }rewrite H34.
  assert (1/a * 1 * (Mk (N - 3) (b/a) * Mk 0 (b/a)) * / Mk N (b/a) *a =
          ( /a * a) * Mk 0 (b/a) * ( Mk (N - 3) (b/a) * (/ Mk N (b/a)))). { nra. }rewrite H35.
  assert (mult (1/a * -1 * (Mk (N - 2) (b/a) * Mk 0 (b/a)) * / Mk N (b/a))  b=
            (1/a * -1 * (Mk (N - 2) (b/a) * Mk 0 (b/a)) * / Mk N (b/a)) * b). { reflexivity. } rewrite H36.
  assert (1/a * -1 * (Mk (N - 2) (b/a) * Mk 0 (b/a)) * / Mk N (b/a) *b =
           ( b/a) * Mk 0 (b/a) * ( (-1*Mk (N - 2) (b/a))* (/ Mk N (b/a)))). { nra. } rewrite H37.
  assert (mult (1/a * 1 * (Mk (pred N) (b/a) * Mk 0 (b/a) * / Mk N (b/a)))  a=
            (1/a * 1 * (Mk (pred N) (b/a) * Mk 0 (b/a) * / Mk N (b/a))) *  a). { reflexivity. } rewrite H38.
  assert (1/a * 1 * (Mk (pred N) (b/a) * Mk 0 (b/a) * / Mk N (b/a)) *a=
             ( /a * a) * Mk 0 (b/a) * ( Mk (pred N) (b/a) * (/ Mk N (b/a)))). { nra. } rewrite H39.
  assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H40.
  assert (1 * Mk 0 (b/a) * (Mk (N - 3) (b/a) * / Mk N (b/a)) +
            (b/a) * Mk 0 (b/a) *(-1 * Mk (N - 2) (b/a) * / Mk N (b/a)) +
            1 * Mk 0 (b/a) * (Mk (pred N) (b/a) * / Mk N (b/a))=
             1 * Mk 0 (b/a) * ( ((Mk (N - 3) (b/a)+-1 * (b/a) * Mk (N - 2) (b/a) + Mk (pred N) (b/a)) * (/ Mk N (b/a))))). { nra. } rewrite H41.
  assert ((Mk (N - 3) (b/a) + -1 * (b/a) * Mk (N - 2) (b/a) + Mk (pred N) (b/a))=0).
  { assert ( pred N = (N-1)%nat). { apply size_prop_35. apply H. } rewrite H42.
    assert ( -1 * (b/a) * Mk (N - 2) (b/a)= (-b/a)* Mk (N-2)%nat (b/a)). { nra. }rewrite H43.
    assert (- Mk (N - 1) (b/a) + (b/a) * Mk (N - 2) (b/a) + - Mk (N - 3) (b/a)=0 ->
                Mk (N - 3) (b/a) + (-b/a) * Mk (N - 2) (b/a) + Mk (N - 1) (b/a) = 0). { nra. } apply H44.
    assert ( - Mk (N - 1) (b/a)= (-1)^ (pred 2) * Mk (N - 1) (b/a)). { simpl. nra. } rewrite H45.
    assert ((b/a) * Mk (N - 2) (b/a)= (-1)^ (2) * (b/a) * Mk (N - 2) (b/a)). { nra. } rewrite H46.
    assert (- Mk (N - 3) (b/a)= (-1)^ (S 2) *  Mk (N - 3) (b/a)). { nra. }rewrite H47. apply Mk_prop_1. apply H. nia.
  } rewrite H42. nra.
+ assert (pred N <=? S j=false). { apply leb_correct_conv. omega. }rewrite H26.
  assert (mult (1/a * (-1) ^ (pred N + pred j) *   (Mk (pred j) (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a)) a=
            (1/a * (-1) ^ (pred N + pred j) *   (Mk (pred j) (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a)) * a). { reflexivity. } rewrite H27.
  assert (1/a * (-1) ^ (pred N + pred j) *(Mk (pred j) (b/a) * Mk (N - pred N - 1) (b/a)) */ Mk N (b/a) * a =
         ( /a* a) * Mk (N - pred N - 1) (b/a)* ( ((-1) ^ (pred N + pred j)* Mk (pred j) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H28.
  assert (mult  (1/a* (-1) ^ (pred N + j) * (Mk j (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a))  b=
            (1/a * (-1) ^ (pred N + j) * (Mk j (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a)) *  b). { reflexivity. } rewrite H29.
  assert (1/a * (-1) ^ (pred N + j) * (Mk j (b/a) * Mk (N - pred N - 1) (b/a)) */ Mk N (b/a) * b=
             ( b/a) * Mk (N - pred N - 1) (b/a) * ( ((-1) ^ (pred N + j) * Mk j (b/a) ) * (/ Mk N (b/a)))). { nra. } rewrite H30.
  assert (mult  (1/a * (-1) ^ (pred N + S j) * (Mk (S j) (b/a) * Mk (N - pred N - 1) (b/a)) *    / Mk N (b/a)) a=
          (1/a* (-1) ^ (pred N + S j) * (Mk (S j) (b/a) * Mk (N - pred N - 1) (b/a)) *    / Mk N (b/a)) * a). { reflexivity. }rewrite H31.
  assert (1/a * (-1) ^ (pred N + S j) *(Mk (S j) (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a) * a =
             ( /a * a) * Mk (N - pred N - 1) (b/a) * ( ((-1) ^ (pred N + S j) * Mk (S j) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H32.
  assert (1 = /a * a). { apply Rinv_l_sym. nra. } rewrite <- H33.
  assert (1 * Mk (N - pred N - 1) (b/a) *((-1) ^ (pred N + pred j) * Mk (pred j) (b/a) * / Mk N (b/a)) +
            (b/a) * Mk (N - pred N - 1) (b/a) *((-1) ^ (pred N + j) * Mk j (b/a) * / Mk N (b/a)) +
            1 * Mk (N - pred N - 1) (b/a) *((-1) ^ (pred N + S j) * Mk (S j) (b/a) * / Mk N (b/a))=
          ( 1 * Mk (N - pred N - 1) (b/a)) * ( ((-1) ^ (pred N + pred j) * Mk (pred j) (b/a) +
            (-1) ^ (pred N + j) * (b/a) * Mk j (b/a) + (-1) ^ (pred N + S j) * Mk (S j) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H34.
  assert ((-1) ^ (pred N + pred j)= (-1)^ (pred N) * (-1)^ (pred j)). { apply pow_add. }rewrite H35.
  assert ((-1) ^ (pred N + j)= (-1)^ (pred N) * (-1)^ (j)). { apply pow_add. } rewrite H36.
  assert ((-1) ^ (pred N + S j)= (-1)^ (pred N) * (-1)^ (S j)). { apply pow_add. }rewrite H37.
  assert (((-1) ^ pred N * (-1) ^ pred j * Mk (pred j) (b/a) +  (-1) ^ pred N * (-1) ^ j * (b/a) * Mk j (b/a) +
              (-1) ^ pred N * (-1) ^ S j * Mk (S j) (b/a))= (-1)^ (pred N) * ((-1) ^ pred j * Mk (pred j) (b/a)+
          (-1) ^ j * (b/a) * Mk j (b/a) + (-1) ^ S j * Mk (S j) (b/a))). { nra. } rewrite H38.
  assert (((-1) ^ pred j * Mk (pred j) (b/a) + (-1) ^ j * (b/a) * Mk j (b/a) +  (-1) ^ S j * Mk (S j) (b/a))=0). { apply Mk_prop_2. nia. }
  rewrite H39. nra.
Qed.

Lemma Ah_prop_20 (a b:R): forall (N:nat) , (2<N)%nat -> 0<a -> Mk N (b/a) <> 0 -> sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0 1 = 0.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0 1=sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0%nat 0%nat + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 1%nat 1%nat).
{ apply (sum_n_m_Chasles (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0%nat 0%nat 1%nat). omega. omega. } rewrite H2.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0 0=(fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0%nat).
{ apply (sum_n_n (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0%nat). } rewrite H3.
assert (sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 1 1=(fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 1%nat).
{ apply (sum_n_n (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) (pred N) l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 1%nat). } rewrite H4.
unfold Ah.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0))
     0 0= (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0) 0%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0) 0%nat 0%nat). omega. omega. } rewrite H5.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0))
     1 0=  (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0) 1%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0) 1%nat 0%nat). omega. omega. } rewrite H6.
assert (0 =? 0=true). { auto. } rewrite H7.
assert (1 =? 0=false). { auto. } rewrite H8.
assert (1 - 0 =? one=true). { auto. }rewrite H9.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) (pred N) 0=   (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) 0%nat).
{ apply (coeff_mat_bij  Hierarchy.zero(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) 0%nat). omega. omega. } rewrite H10.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) (pred N) 1= (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) (pred N) 1%nat). omega. omega. }rewrite H11.
assert (pred N <=? 0=false). { apply leb_correct_conv. omega. }rewrite H12.
assert (pred N <=? 1=false). { apply leb_correct_conv. omega.  } rewrite H13.
assert (mult  (1/a * (-1) ^ (pred N + 0) * (Mk 0 (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a))  b=
          (1/a * (-1) ^ (pred N + 0) * (Mk 0 (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a)) *  b).  { reflexivity. } rewrite H14.
assert (1/a * (-1) ^ (pred N + 0) * (Mk 0 (b/a) * Mk (N - pred N - 1) (b/a)) */ Mk N (b/a) * b=
          ( b/a) * Mk (N - pred N - 1) (b/a) * ( ((-1) ^ (pred N + 0)  *Mk 0 (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H15.
assert (mult  (1/a * (-1) ^ (pred N + 1) * (Mk 1 (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a))  a=
             (1/a * (-1) ^ (pred N + 1) * (Mk 1 (b/a) * Mk (N - pred N - 1) (b/a)) * / Mk N (b/a)) * a). { reflexivity. } rewrite H16.
assert (1/a * (-1) ^ (pred N + 1) * (Mk 1 (b/a) * Mk (N - pred N - 1) (b/a)) */ Mk N (b/a) * a=
          ( /a * a) * Mk (N - pred N - 1) (b/a) * ( ((-1) ^ (pred N + 1) *Mk 1 (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H17.
assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H18.
assert ((b/a)* Mk (N - pred N - 1) (b/a) *((-1) ^ (pred N + 0)  * Mk 0 (b/a) * / Mk N (b/a)) +
            1 * Mk (N - pred N - 1) (b/a) *((-1) ^ (pred N + 1) * Mk 1 (b/a) * / Mk N (b/a))=
           ( 1 * Mk (N - pred N - 1) (b/a)) * ( ((-1) ^ (pred N + 0) * (b/a) * Mk 0 (b/a)+ (-1) ^ (pred N + 1) * Mk 1 (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H19.
assert ((-1) ^ (pred N + 0) * (b/a) * Mk 0 (b/a) +  (-1) ^ (pred N + 1) * Mk 1 (b/a)=0).
{ assert ((-1) ^ (pred N + 0)= (-1)^ (pred N) * (-1)^0). { apply pow_add. } rewrite H20.
  assert ((-1) ^ (pred N + 1)= (-1)^ (pred N) * (-1)^1). { apply pow_add. } rewrite H21.
  assert ( (-1) ^ pred N * (-1) ^ 0 * (b/a) * Mk 0 (b/a) +(-1) ^ pred N * (-1) ^ 1 * Mk 1 (b/a)=
           (-1) ^ (pred N) * ( (-1) ^ 0 * (b/a) * Mk 0 (b/a) + (-1) ^ 1 * Mk 1 (b/a))). { nra. } rewrite H22.  
  assert (Mk 0 (b/a)=1). { apply Mk_B0. } rewrite H23.
  assert (Mk 1 (b/a)=b/a). { apply Mk_B1. }rewrite H24.
  simpl. nra.
} rewrite H20. nra.
Qed.

Lemma size_prop_39 (a b:R): forall N:nat, (3< N)%nat ->0<a -> Mk N (b/a) <> 0 -> Mk (N - 1 - 1) (b/a) = Mk (N - 2) (b/a).
Proof.
intros. assert ((N - 1 - 1)%nat = (N - 2)%nat). { omega. }rewrite H2. reflexivity. 
Qed.

Lemma size_prop_40 (a b:R) : forall N:nat, (3< N)%nat ->0< a -> Mk N (b/a) <> 0 -> Mk (N - 2 - 1) (b/a) = Mk (N - 3) (b/a).
Proof.
intros. assert ((N - 2 - 1)%nat = (N - 3)%nat). { omega. } rewrite H2. reflexivity.
Qed.


Lemma Ah_prop_21 (a b:R): forall (N:nat), (3< N)%nat ->  0<a -> Mk N (b/a) <> 0 -> sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 2 = 1.
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 2=sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 1%nat + sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 2%nat 2%nat).
{ apply (sum_n_m_Chasles (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
             (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 1%nat 2%nat). omega. omega. } rewrite H2.
assert (sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 1=sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1))  0%nat 0%nat + sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 1%nat 1%nat).
{ apply (sum_n_m_Chasles  (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 0%nat 1%nat). omega. omega. } rewrite H3.
assert (sum_n_m
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 0 = (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat).
{ apply (sum_n_n (fun l : nat =>
         mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
           (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat). } rewrite H4.
assert (sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 1 1=(fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 1%nat).
{ apply (sum_n_n (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 1%nat). } rewrite H5.
assert (sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 2 2=(fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 2%nat).
{ apply (sum_n_n (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (inverse_A N a b ) 1 l)
     (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 2%nat). } rewrite H6.
unfold Ah.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0))
     0 1=  (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0) 0%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0) 0%nat 1%nat). omega. omega. } rewrite H7.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0))
     1 1= (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0) 1%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero  (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0) 1%nat 1%nat). omega. omega. } rewrite H8.
assert ( coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0))
     2 1= (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0) 2%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i =? j
         then b
         else
          if i - j =? one then a else if j - i =? one then a else 0) 2%nat 1%nat). omega. omega. }rewrite H9.
assert (0 =? 1=false). { auto. } rewrite H10.
assert ( 0 - 1 =? one=false). { auto. } rewrite H11.
assert (1 - 0 =? one=true). { auto. } rewrite H12.
assert ( 1 =? 1=true). { auto. } rewrite H13.
assert (2 =? 1=false). { auto. } rewrite H14.
assert ( 2 - 1 =? one=true). { auto. } rewrite H15.
unfold inverse_A.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) 1 0=(fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 1%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 1%nat 0%nat). omega. omega. } rewrite H16.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) 1 1=  (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 1%nat 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 1%nat 1%nat). omega. omega. } rewrite H17.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a))) 1 2=  (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 1%nat 2%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
         if i <=? j
         then
          1 / a * (-1) ^ (i + j) *
          (Mk i (b / a) * Mk (N - j - 1) (b / a) * / Mk N (b / a))
         else
          1 / a * (-1) ^ (i + j) * (Mk j (b / a) * Mk (N - i - 1) (b / a)) *
          / Mk N (b / a)) 1%nat 2%nat). omega. omega. }rewrite H18.
assert ( 1 <=? 0=false). { auto. }rewrite H19.
assert ( 1 <=? 1=true). {  auto. } rewrite H20.
assert (1 <=? 2=true). { auto.  } rewrite H21.
assert ((-1) ^ (1 + 0)=-1). { simpl. nra. } rewrite H22.
assert ((-1) ^ (1 + 1)=1). { simpl. nra. }rewrite H23.
assert ((-1) ^ (1 + 2)=-1). { simpl. nra. }rewrite H24.
assert (mult (1/a * -1 * (Mk 0 (b/a) * Mk (N - 1 - 1) (b/a)) * / Mk N (b/a))  a=
        (1/a* -1 * (Mk 0 (b/a) * Mk (N - 1 - 1) (b/a)) * / Mk N (b/a)) *  a). { reflexivity. } rewrite H25.
assert (1/a * -1 * (Mk 0 (b/a) * Mk (N - 1 - 1) (b/a)) * / Mk N (b/a) *a=
          ( /a * a) * ( ( -1 * Mk 0 (b/a)*Mk (N - 1 - 1) (b/a))* (/ Mk N (b/a)))). { nra. }rewrite H26.
assert (mult (1/a * 1 * (Mk 1 (b/a) * Mk (N - 1 - 1) (b/a) * / Mk N (b/a)))  b=
          (1/a * 1 * (Mk 1 (b/a) * Mk (N - 1 - 1) (b/a) * / Mk N (b/a))) * b). { reflexivity. } rewrite H27.
assert (1/a * 1 * (Mk 1 (b/a) * Mk (N - 1 - 1) (b/a) * / Mk N (b/a)) *b=
           ( b/a) * ( ( Mk 1 (b/a) *  Mk (N - 1 - 1) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H28.
assert (mult (1/a * -1 * (Mk 1 (b/a) * Mk (N - 2 - 1) (b/a) * / Mk N (b/a)))  a=
          (1/a * -1 * (Mk 1 (b/a) * Mk (N - 2 - 1) (b/a) * / Mk N (b/a))) * a). { reflexivity. } rewrite H29.
assert (1/a * -1 * (Mk 1 (b/a) * Mk (N - 2 - 1) (b/a) * / Mk N (b/a)) *a=
          ( /a * a) * ( (-1 * Mk 1 (b/a) * Mk (N - 2 - 1) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H30.
assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H31.
assert (1 *(-1 * Mk 0 (b/a) * Mk (N - 1 - 1) (b/a) * / Mk N (b/a)) +
            (b/a) *( Mk 1 (b/a) * Mk (N - 1 - 1) (b/a) * / Mk N (b/a)) +
            1 *(-1 * Mk 1 (b/a) * Mk (N - 2 - 1) (b/a) * / Mk N (b/a))=
         ( 1 * ( ( (-1 * Mk 0 (b/a)+ (b/a) * Mk 1 (b/a)) * Mk (N - 1 - 1) (b/a)+ 
            -1 * Mk 1 (b/a) * Mk (N - 2 - 1) (b/a) ) * (/ Mk N (b/a))))). { nra. } rewrite H32.
assert ( Mk 0 (b/a) =1). { apply Mk_B0. }rewrite H33.
assert (Mk 1 (b/a)=b/a). { apply Mk_B1. } rewrite H34.
assert ((-1 * 1 + ( b/a) * (b/a)) * Mk (N - 1 - 1) (b/a)= ((b/a)^2 -1) * Mk (N - 1 - 1) (b/a)). { nra. }rewrite H35.
assert (-1 * (b/a) * Mk (N - 2 - 1) (b/a)= (-b/a)*  Mk (N - 2 - 1) (b/a)). { nra. }rewrite H36.
assert (Mk (N - 1 - 1) (b/a)= Mk (N-2)%nat (b/a)).  { apply size_prop_39. apply H. nra. nra.  } rewrite H37.
assert (Mk (N - 2 - 1) (b/a)= Mk (N-3)%nat (b/a)). { apply size_prop_40. apply H. nra. nra.  } rewrite H38.
assert (1 *((((b / a) ^ 2 - 1) * Mk (N - 2) (b / a) + - b / a * Mk (N - 3) (b / a)) * / Mk N (b / a))= 
                  ((((b / a) ^ 2 - 1) * Mk (N - 2) (b / a) + - b / a * Mk (N - 3) (b / a)) * / Mk N (b / a))). { nra. } rewrite H39.
apply Rmult_eq_reg_r with (Mk N (b/a)). 
assert (1 * Mk N (b / a)= Mk N (b/a)). { nra. } rewrite H40.
assert ((((b / a) ^ 2 - 1) * Mk (N - 2) (b / a) + - b / a * Mk (N - 3) (b / a)) * / Mk N (b / a) *Mk N (b / a)=
                  (((b / a) ^ 2 - 1) * Mk (N - 2) (b / a) + - b / a * Mk (N - 3) (b / a)) * (Mk N (b/a) * (/ Mk N (b/a)))). { nra. } rewrite H41.
assert ((Mk N (b / a) * / Mk N (b / a))=1). { apply Rinv_r. nra. } rewrite H42.
assert (Mk N (b/a) = (b/a) * Mk (N-1) (b/a) - Mk (N-2) (b/a)).
{ apply Mk_recurr. } rewrite H43.
assert (Mk (N-1) (b/a) = (b/a)* Mk ((N-1)-1)%nat (b/a)- Mk ((N-1)-2)%nat (b/a)). { apply Mk_recurr. } rewrite H44.
assert ( ((N-1)-1)%nat = (N-2)%nat). { apply size_Nm1. auto. } rewrite H45.
assert ( ((N-1)-2)%nat= (N-3)%nat). { apply size_Nm2. auto. } rewrite H46. nra.
nra.
Qed.
 
 
Lemma sum_const_zero : forall (n m:nat) ,(n <= m)%nat->sum_n_m (fun _ =>0 ) n m=0.
Proof.
intros.
induction n. induction m. 
+  cut(sum_n_m (fun _ : nat => 0) 0 0 = sum_n (fun _ : nat => 0) 0%nat).
  - intros. rewrite H0. apply sum_O.
  - unfold sum_n. reflexivity.
+ cut(sum_n_m (fun _ : nat => 0) 0 (S m) = sum_n_m (fun _ : nat => 0) 0 m + (fun _ : nat => 0) (S m)).
  - intros. rewrite H0. rewrite IHm. nra. omega.
  - apply (sum_n_Sm (fun _ : nat => 0) 0 m). omega.
+ cut(sum_n_m (fun _ : nat => 0) n m -((fun _: nat =>0) n) =sum_n_m (fun _ : nat => 0) (S n) m).
  - intros. rewrite <- H0. rewrite IHn. nra. omega.
  - cut( sum_n_m (fun _ : nat => 0) n m= (fun _ : nat => 0) n + sum_n_m (fun _ : nat => 0) (S n) m).
    * intros.  rewrite H0. nra.  
    * apply (sum_Sn_m (fun _ : nat => 0) n m).  omega.
Qed. 

Lemma invertible_check_1 (a b:R) : forall (N:nat), (2<N)%nat -> 0<a -> Mk N (b/a) <> 0 -> Mmult (inverse_A N a b ) (Ah N a b a ) = identity N. 
Proof.
intros.
unfold Mmult. unfold identity.
apply (mk_matrix_ext N N (fun i j : nat =>
               sum_n
                 (fun l : nat =>
                  mult (coeff_mat Hierarchy.zero (inverse_A N a b ) i l)
                    (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 
                 (pred N)) (fun i j : nat => if i =? j then 1 else 0)).
intros. 
assert ( i=0%nat \/ (0<i<(pred N))%nat \/ i=pred N). { omega. } destruct H4.
+ assert ( i=j \/ i<> j). { omega. } destruct H5.
  - rewrite <-H5. rewrite H4. 
    assert (0 =? 0 =true). { auto. } rewrite H6. unfold sum_n.
    assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 0   (pred N)= sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 0%nat 1%nat + sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 2%nat (pred N)).
    { apply (sum_n_m_Chasles   (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 0%nat 1%nat (pred N)). omega. omega. }
    rewrite H7.
    assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 2  (pred N)=0).
    { assert (sum_n_m (fun l:nat => 0) 2%nat (pred N)=0). { apply sum_const_zero. omega. } rewrite <- H8.
      apply sum_n_m_ext_loc. intros.
      assert ((coeff_mat Hierarchy.zero (Ah N a b a ) k 0) = 0). { apply Ah_j_0. omega. omega. } rewrite H10.
      apply (mult_zero_r  (coeff_mat Hierarchy.zero  (inverse_A N a b ) 0 k)). 
    } rewrite H8.
    assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 0 1 + 0 = sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 0 1 ). { nra. } rewrite H9.
    assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 0 1= sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 0%nat 0%nat + sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 1%nat 1%nat).
    { apply (sum_n_m_Chasles  (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 0%nat 0%nat 1%nat). omega. omega. } rewrite H10.
    assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 0 0= (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 0%nat).
    { apply (sum_n_n (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 0 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 0)) 0%nat). } rewrite H11.
    assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero
                      (inverse_A N a b ) 0 l)
                   (coeff_mat Hierarchy.zero
                      (Ah N a b a ) l 0)) 1 1=  (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero
                      (inverse_A N a b ) 0 l)
                   (coeff_mat Hierarchy.zero
                      (Ah N a b a ) l 0))  1%nat). 
    { apply (sum_n_n (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero
                      (inverse_A N a b ) 0 l)
                   (coeff_mat Hierarchy.zero
                      (Ah N a b a ) l 0))  1%nat). } rewrite H12.
    unfold Ah.
    assert (coeff_mat  Hierarchy.zero
             (mk_matrix N N
                (fun i0 j0 : nat =>
                 if i0 =? j0
                 then b
                 else
                  if i0 - j0 =? one
                  then a
                  else
                   if j0 - i0 =? one
                   then a
                   else 0)) 0 0=  (fun i0 j0 : nat =>
                 if i0 =? j0
                 then b
                 else
                  if i0 - j0 =? one
                  then a
                  else
                   if j0 - i0 =? one
                   then a
                   else 0) 0%nat 0%nat).
    { apply (coeff_mat_bij  Hierarchy.zero (fun i0 j0 : nat =>
                 if i0 =? j0
                 then b
                 else
                  if i0 - j0 =? one
                  then a
                  else
                   if j0 - i0 =? one
                   then a
                   else 0) 0%nat 0%nat). omega. omega. } rewrite H13.
    assert (coeff_mat  Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else
           if j0 - i0 =? one
           then a
           else 0)) 1 0= (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else
           if j0 - i0 =? one
           then a
           else 0) 1%nat 0%nat). 
    { apply (coeff_mat_bij  Hierarchy.zero  (fun i0 j0 : nat =>
         if i0 =? j0
         then b
         else
          if i0 - j0 =? one
          then a
          else
           if j0 - i0 =? one
           then a
           else 0) 1%nat 0%nat). omega. omega. } rewrite H14.
    assert (   0 =? 0=true). { auto. } rewrite H15. assert (1 =? 0=false). { auto. } rewrite H16.
    assert (1 - 0 =? one=true). { auto. } rewrite H17. unfold inverse_A. 
    assert (coeff_mat Hierarchy.zero
             (mk_matrix N N
                (fun i0 j0 : nat =>
                 if i0 <=? j0
                 then
                  1 / a * (-1) ^ (i0 + j0) *
                  (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
                 else
                  1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
                  / Mk N (b / a))) 0 0=(fun i0 j0 : nat =>
                 if i0 <=? j0
                 then
                  1 / a * (-1) ^ (i0 + j0) *
                  (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
                 else
                  1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
                  / Mk N (b / a)) 0%nat 0%nat).
    { apply (coeff_mat_bij Hierarchy.zero   (fun i0 j0 : nat =>
                 if i0 <=? j0
                 then
                  1 / a * (-1) ^ (i0 + j0) *
                  (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
                 else
                  1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
                  / Mk N (b / a)) 0%nat 0%nat). omega. omega. } rewrite H18.
    assert (coeff_mat Hierarchy.zero
             (mk_matrix N N
                (fun i0 j0 : nat =>
                 if i0 <=? j0
                 then
                  1 / a * (-1) ^ (i0 + j0) *
                  (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
                 else
                  1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
                   / Mk N (b / a))) 0 1=(fun i0 j0 : nat =>
                 if i0 <=? j0
                 then
                  1 / a * (-1) ^ (i0 + j0) *
                  (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
                 else
                  1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
                   / Mk N (b / a)) 0%nat 1%nat).
    { apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
                 if i0 <=? j0
                 then
                  1 / a * (-1) ^ (i0 + j0) *
                  (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
                 else
                  1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
                   / Mk N (b / a)) 0%nat 1%nat). omega. omega. } rewrite H19.
    assert (0 <=? 0=true). { auto. } rewrite H20.
    assert (0 <=? 1=true). { auto. } rewrite H21.
    assert ((0 + 0)%nat = 0%nat). { omega. } rewrite H22.
    assert ((-1) ^ 0=1). { nra. } rewrite H23.
    assert( (0 + 1)%nat = 1%nat). { omega. } rewrite H24.
    assert ((-1) ^ 1=-1). { nra. } rewrite H25.
    assert ((N - 0 - 1)%nat = (N-1)%nat). { omega. } rewrite H26.
    assert ((N - 1 - 1)%nat = (N-2)%nat). { omega. } rewrite H27.
    assert (mult (1 / a * 1 * (Mk 0 (b / a) * Mk (N - 1) (b / a) * / Mk N (b / a))) b=
                  (1 / a * 1 * (Mk 0 (b / a) * Mk (N - 1) (b / a) * / Mk N (b / a))) * b). { reflexivity. } rewrite H28.
    assert (1 / a * 1 * (Mk 0 (b / a) * Mk (N - 1) (b / a) * / Mk N (b / a)) * b=
                  (b/a) * Mk 0 (b/a) * Mk (N-1) (b/a) * (/ Mk N (b/a) )). { nra. } rewrite H29.
    assert (mult (1 / a * -1 * (Mk 0 (b / a) * Mk (N - 2) (b / a) * / Mk N (b / a))) a=
                    (1 / a * -1 * (Mk 0 (b / a) * Mk (N - 2) (b / a) * / Mk N (b / a))) * a). { reflexivity. } rewrite H30.
    assert (1 / a * -1 * (Mk 0 (b / a) * Mk (N - 2) (b / a) * / Mk N (b / a)) * a =
              (/a * a) * -1 *Mk 0 (b/a) * Mk (N-2) (b/a) * (/ Mk N (b/a))). { nra. } rewrite H31.
    assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H32.
    assert (Mk 0 (b/a) =1). { apply Mk_B0. } rewrite H33.
    assert (b / a * 1 * Mk (N - 1) (b / a) * / Mk N (b / a) +1 * -1 * 1 * Mk (N - 2) (b / a) * / Mk N (b / a) =
             ((b / a * 1 * Mk (N - 1) (b / a)  +1 * -1 * 1 * Mk (N - 2) (b / a)) *(/Mk N (b/a)))). { nra.  } rewrite H34.
    apply Rmult_eq_reg_r with (Mk N (b/a)). 
    assert ((b / a * 1 * Mk (N - 1) (b / a) + 1 * -1 * 1 * Mk (N - 2) (b / a)) * / Mk N (b / a) *Mk N (b / a)=
                  (b / a * 1 * Mk (N - 1) (b / a) + 1 * -1 * 1 * Mk (N - 2) (b / a)) * (Mk N (b/a) * (/ Mk N (b/a)))). { nra. } rewrite H35.
    assert ( (Mk N (b/a) * (/ Mk N (b/a)))=1). { apply Rinv_r. nra. } rewrite H36.
    assert (Mk N (b/a) = (b/a) * Mk (N-1) (b/a) - Mk (N-2) (b/a)). { apply Mk_recurr. } rewrite H37. nra. nra. 

  - assert ( i=?j=false). { assert (i =? j = false <-> i <> j). { apply (beq_nat_false_iff i j). } destruct H6. apply H7. apply H5. } rewrite H6.
    unfold sum_n.
    assert ( j=1%nat \/ (1<j)%nat). { omega. } destruct H7.
    * rewrite H4. 
      assert ( N=3%nat \/ (3<N)%nat). { omega. } destruct H8.
      (* N=3 case *)
      rewrite H8.
      assert ((pred 3)=2%nat). { omega. } rewrite H9. apply (Ah_prop_1 a b i j N). omega. omega. omega. nra.
      (* 3<N case *)
      assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0
                (pred N)= sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat 2%nat + sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 3%nat (pred N)).
      { apply (sum_n_m_Chasles  (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  0%nat 2%nat (pred N)). omega. omega. }
      rewrite H9.
      assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 3
                (pred N)= 0).
      { assert (sum_n_m (fun l:nat => 0) 3%nat (pred N) =0). { apply sum_const_zero. omega. }
        rewrite <-H10.
        apply sum_n_m_ext_loc. intros.
        assert ( (coeff_mat Hierarchy.zero (Ah N a b a ) k j)=0).
        { rewrite H7. apply Ah_j_1. omega. omega. } rewrite H12. apply (mult_zero_r  (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 k)). 
      } 
      rewrite H10.
      assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0
              2 + 0=sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0
              2). { nra. }rewrite H11. apply Ah_prop_2. auto. omega. nra.
      rewrite H4. 
   * assert ( (1<j<pred N)%nat \/ j = pred N). { omega. } destruct H8.
     (* 1<j<N-1 case *)
      assert ( (1<j<(N-2)%nat)%nat \/ j = (N-2)%nat). { omega. } destruct H9.
      (* 1<j<N-2*)
      assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0
              (pred N)= sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat (pred (pred j)) + sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (S(pred (pred j))) (pred N)).
      { apply (sum_n_m_Chasles   (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat (pred (pred j)) (pred N)). omega. omega. }
      rewrite H10.
      assert ((S (pred (pred j))) = pred j). { omega. } rewrite H11.
      assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
                (pred j) (pred N)= sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j) (S j) + sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (S (S j)) (pred N)).
      { apply (sum_n_m_Chasles  (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j) (S j) (pred N)). omega. omega. }
       rewrite H12.
       assert (sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                        l)
                     (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0
                  (pred (pred j))= 0).
      { assert (sum_n_m (fun l:nat => 0) 0%nat (pred (pred j))=0). { apply sum_const_zero. omega. } rewrite <-H13.
        apply sum_n_m_ext_loc. intros.
        assert ( (coeff_mat Hierarchy.zero (Ah N a b a ) k j) = 0). { apply Ah_pred_j. omega. omega. omega. } rewrite H15.
        apply (mult_zero_r (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 k)). 
      }  rewrite H13.
      assert ( sum_n_m
                 (fun l : nat =>
                  mult
                    (coeff_mat Hierarchy.zero 
                       (inverse_A N a b ) 0 l)
                    (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
                 (S (S j)) (pred N)=0).
      { assert (sum_n_m (fun l:nat => 0) (S (S j)) (pred N) = 0). { apply sum_const_zero. omega. } rewrite<-H14.
        apply sum_n_m_ext_loc. intros.
        assert ((coeff_mat Hierarchy.zero (Ah N a b a ) k j) = 0). 
        { apply Ah_Sj. omega. omega. omega. } rewrite H16.
        apply (mult_zero_r (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 k)).
      } rewrite H14.
      assert (0 +
                (sum_n_m
                   (fun l : nat =>
                    mult
                      (coeff_mat Hierarchy.zero 
                         (inverse_A N a b ) 0 l)
                      (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
                   (pred j) (S j) + 0) =sum_n_m
                   (fun l : nat =>
                    mult
                      (coeff_mat Hierarchy.zero 
                         (inverse_A N a b ) 0 l)
                      (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
                   (pred j) (S j)). { nra. } rewrite H15.
      apply Ah_prop_3. omega. omega. nra.
      (* j= N-2*)
      assert (N=3%nat \/ (3<N)%nat). { omega. } destruct H10.
      (*N=3 case *)
      rewrite H10.
      assert ((pred 3)=2%nat). { omega. } rewrite H11. apply (Ah_prop_1 a b i j N). omega. omega. omega. nra.
      rewrite H9.
      (* 3<N case *)
      assert (sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                        l)
                     (coeff_mat Hierarchy.zero (Ah N a b a ) l
                        (N - 2))) 0 (pred N) = sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                        l)
                     (coeff_mat Hierarchy.zero (Ah N a b a ) l
                        (N - 2))) 0%nat (N-4)%nat + sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                        l)
                     (coeff_mat Hierarchy.zero (Ah N a b a ) l
                        (N - 2))) (S (N-4)%nat) (pred N)).
      { apply (sum_n_m_Chasles  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                        l)
                     (coeff_mat Hierarchy.zero (Ah N a b a ) l
                        (N - 2))) 0%nat (N-4)%nat (pred N)). omega. omega. }
      rewrite H11.
      assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l
                      (N - 2))) 0 (N - 4)=0).
      { assert (sum_n_m (fun l:nat => 0) 0%nat (N-4)%nat = 0). { apply sum_const_zero. omega. } 
        rewrite<-H12. apply sum_n_m_ext_loc. intros.
        assert ((coeff_mat Hierarchy.zero (Ah N a b a ) k (N - 2))=0).
        { apply Ah_j_Nminus2. auto. omega. omega. }
        rewrite H14. apply (mult_zero_r (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 k)). 
      } rewrite H12.
      assert (0 +
              sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l
                      (N - 2))) (S (N - 4)) (pred N)= sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l
                      (N - 2))) (S (N - 4)) (pred N)). { nra. } rewrite H13.
      assert ( (S (N - 4))= (N-3)%nat). { omega. } rewrite H14.
     apply Ah_prop_4. omega.  nra. 
    (* j= pred N*)
    rewrite H8.
    assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l
                    (pred N))) 0 (pred N)=sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l
                    (pred N))) 0%nat (N-3)%nat + sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l
                    (pred N))) (S (N-3)%nat) (pred N)).
     { apply (sum_n_m_Chasles  (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l
                    (pred N))) 0%nat (N-3)%nat (pred N)). omega. omega. } rewrite H9.
      assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l
                      (pred N))) 0 (N - 3)=0).
      { assert (sum_n_m (fun l:nat => 0) 0%nat (N-3)%nat = 0). { apply sum_const_zero. omega. } rewrite <-H10.
        apply sum_n_m_ext_loc. intros.
        assert ( (coeff_mat Hierarchy.zero (Ah N a b a ) k (pred N))=0).
        { apply Ah_j_predN. omega. omega. } rewrite H12.
        apply (mult_zero_r  (coeff_mat Hierarchy.zero (inverse_A N a b ) 0 k)). 
      } rewrite H10.
      assert ( (S (N - 3)) = (N-2)%nat). { omega. }rewrite H11.
      assert (0 +
                sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                        l)
                     (coeff_mat Hierarchy.zero (Ah N a b a ) l
                        (pred N))) (N - 2) (pred N)= sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero (inverse_A N a b ) 0
                        l)
                     (coeff_mat Hierarchy.zero (Ah N a b a ) l
                        (pred N))) (N - 2) (pred N)). { nra. } rewrite H12.
       apply Ah_prop_5. omega. nra.
+ destruct H4.
  - assert ( i=j \/ i<> j). { omega. } destruct H5. 
    * rewrite H5. assert ( j =? j=true). { symmetry. apply (beq_nat_refl j). } rewrite H6. unfold sum_n.
      assert (i=1%nat \/ (1<i)%nat). { omega. } destruct H7.
      rewrite H5 in H7. rewrite H7.
      assert ( N=3%nat \/ (3<N)%nat). { omega. } destruct H8.
      { rewrite H8. assert ( pred 3 = 2%nat). { omega. } rewrite H9. apply Ah_prop_9. omega. rewrite H8 in H1. nra. nra.  }
      { assert (sum_n_m  (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 1 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 1)) 0 (pred N)= sum_n_m  (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 1 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 1)) 0%nat 2%nat + sum_n_m  (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero
                    (inverse_A N a b ) 1 l)
                 (coeff_mat Hierarchy.zero
                    (Ah N a b a ) l 1)) 3%nat (pred N)).
         { apply (sum_n_m_Chasles (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 1 l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l 1)) 0%nat 2%nat (pred N)). omega. omega. } rewrite H9.
         assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero
                      (inverse_A N a b ) 1 l)
                   (coeff_mat Hierarchy.zero
                      (Ah N a b a ) l 1)) 3 
                (pred N) =0). 
         { assert (sum_n_m (fun l:nat => 0) 3%nat (pred N) =0). { apply sum_const_zero. omega. } rewrite <-H10.
         apply sum_n_m_ext_loc. intros.
         assert ( coeff_mat Hierarchy.zero  (Ah N a b a ) k 1= 0). { apply Ah_j_1. omega. omega. } rewrite H12.
         apply ( mult_zero_r (coeff_mat Hierarchy.zero  (inverse_A N a b ) 1 k)). } rewrite H10.
         assert (sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 1 l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l 1)) 0 2 + 0 =sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 1 l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l 1)) 0 2 ). { nra. }rewrite H11. apply Ah_prop_21. omega.  nra. nra.
      }
      assert ( (1<i<(N-2)%nat)%nat \/ i= (N-2)%nat). { omega. } destruct H8.
      assert ( sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero
                      (inverse_A N a b ) j l)
                   (coeff_mat Hierarchy.zero
                      (Ah N a b a ) l j)) 0 
                (pred N)=  sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero
                      (inverse_A N a b ) j l)
                   (coeff_mat Hierarchy.zero
                      (Ah N a b a ) l j)) 0%nat (pred (pred i)) +  sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero
                      (inverse_A N a b ) j l)
                   (coeff_mat Hierarchy.zero
                      (Ah N a b a ) l j)) (S (pred (pred i))) (pred N)). 
      { apply (sum_n_m_Chasles (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero
                      (inverse_A N a b ) j l)
                   (coeff_mat Hierarchy.zero
                      (Ah N a b a ) l j)) 0%nat (pred (pred i)) (pred N)). omega. omega. } rewrite H9.
      assert ( S (pred (pred i)) = pred i). { omega. } rewrite H10.
      assert (sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) j l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l j)) 0 (pred (pred i))=0). 
      { rewrite H5. 
        assert (sum_n_m (fun l:nat => 0) 0%nat (pred (pred j)) = 0). { apply sum_const_zero. omega. } rewrite <-H11.
        apply sum_n_m_ext_loc. intros.
        assert ((coeff_mat Hierarchy.zero (Ah N a b a ) k j) = 0). { apply Ah_pred_j. omega. omega. omega. } rewrite H13.
        apply (mult_zero_r (coeff_mat Hierarchy.zero (inverse_A N a b ) j   k)).
      } rewrite H11.
      assert (sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) j l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l j)) (pred i)
                  (pred N)= sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) j l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l j)) (pred i) ( S i) + sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) j l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l j)) (S (S i)) (pred N)).
      { apply (sum_n_m_Chasles (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) j l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l j)) (pred i) (S i) (pred N)). omega. omega. } rewrite H12.
      assert (  sum_n_m
                 (fun l : nat =>
                  mult
                    (coeff_mat Hierarchy.zero
                       (inverse_A N a b ) j l)
                    (coeff_mat Hierarchy.zero
                       (Ah N a b a ) l j)) 
                 (S (S i)) (pred N) = 0). 
      { rewrite H5. assert (sum_n_m (fun l:nat => 0) (S (S j)) (pred N) = 0). { apply sum_const_zero. omega. } rewrite <- H13.
        apply sum_n_m_ext_loc. intros.
        assert ( (coeff_mat Hierarchy.zero (Ah N a b a ) k j) = 0). { apply Ah_Sj. omega. omega. omega. } rewrite H15.
        apply (mult_zero_r (coeff_mat Hierarchy.zero (inverse_A N a b ) j  k)).
      } rewrite H13.
      assert (0 +
                  (sum_n_m
                     (fun l : nat =>
                      mult
                        (coeff_mat Hierarchy.zero
                           (inverse_A N a b ) j l)
                        (coeff_mat Hierarchy.zero
                           (Ah N a b a ) l j)) 
                     (pred i) (S i) + 0)= sum_n_m
                     (fun l : nat =>
                      mult
                        (coeff_mat Hierarchy.zero
                           (inverse_A N a b ) j l)
                        (coeff_mat Hierarchy.zero
                           (Ah N a b a ) l j)) 
                     (pred i) (S i)). { nra. } rewrite H14. 
      rewrite <-H5. apply Ah_prop_10. omega. omega. nra. nra. 
      rewrite H5 in H8. rewrite H8.
      assert (N=3%nat \/ (3<N)%nat). { omega. } destruct H9.
      (* N=3 case *)
      rewrite H9. assert ( (pred 3)= 2%nat). { omega. } rewrite H10. assert ( (3 - 2)%nat =1%nat). { omega. } rewrite H11.
      apply Ah_prop_10. omega. omega. rewrite H9 in H1. nra. nra.
      (* (3<N) case *)
      assert (sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 
                        (N - 2) l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l (N - 2))) 0
                  (pred N) = sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 
                        (N - 2) l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l (N - 2))) 0%nat (N-4)%nat + sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 
                        (N - 2) l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l (N - 2))) (S (N-4)) (pred N)).
        { apply (sum_n_m_Chasles (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 
                        (N - 2) l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l (N - 2))) 0%nat (N-4)%nat (pred N)). omega. omega. } rewrite H10.
        assert ((S (N - 4))= (N-3)%nat). { omega. } rewrite H11.
        assert (sum_n_m
                    (fun l : nat =>
                     mult
                       (coeff_mat Hierarchy.zero
                          (inverse_A N a b ) 
                          (N - 2) l)
                       (coeff_mat Hierarchy.zero
                          (Ah N a b a ) l (N - 2))) 0 (N - 4) =0). 
        { assert (sum_n_m (fun l:nat => 0) 0%nat (N-4)%nat =0). { apply sum_const_zero. omega. } rewrite <- H12. 
          apply sum_n_m_ext_loc. intros.
          assert ((coeff_mat Hierarchy.zero (Ah N a b a ) k (N - 2))=0). { apply Ah_j_Nminus2. auto. omega. omega. } rewrite H14.
          apply (mult_zero_r (coeff_mat Hierarchy.zero (inverse_A N a b ) (N - 2) k)).
        } rewrite H12. 
        assert (0 +
                    sum_n_m
                      (fun l : nat =>
                       mult
                         (coeff_mat Hierarchy.zero
                            (inverse_A N a b ) 
                            (N - 2) l)
                         (coeff_mat Hierarchy.zero
                            (Ah N a b a ) l (N - 2)))
                      (N - 3) (pred N)= sum_n_m
                      (fun l : nat =>
                       mult
                         (coeff_mat Hierarchy.zero
                            (inverse_A N a b ) 
                            (N - 2) l)
                         (coeff_mat Hierarchy.zero
                         (Ah N a b a ) l (N - 2)))
                 (N - 3) (pred N)). { nra. } rewrite H13. apply Ah_prop_11. omega.  nra. nra.
    * assert ( i=?j=false). { assert ( (i =? j) = false <-> i <> j). { apply (beq_nat_false_iff i j). } destruct H6. apply H7. omega. }
      rewrite H6. unfold sum_n.
      assert (j=0%nat \/ (0<j)%nat). { omega. } destruct H7.
      (* j=0 case *)
      rewrite H7.
      assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0
                (pred N)= sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0%nat 1%nat + sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 2%nat (pred N)).
      { apply (sum_n_m_Chasles (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 0))  0%nat 1%nat (pred N)). omega. omega. } rewrite H8.
      assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 2
              (pred N)=0).
      { assert ( sum_n_m (fun l:nat => 0) 2%nat (pred N) =0). { apply sum_const_zero. omega. }
        rewrite <- H9. apply sum_n_m_ext_loc. intros.
        assert ( (coeff_mat Hierarchy.zero (Ah N a b a ) k 0) = 0). { apply Ah_j_0. omega. omega. } rewrite H11.
        apply (mult_zero_r (coeff_mat Hierarchy.zero (inverse_A N a b ) i k)).
      } rewrite H9.
      assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0 1 +0=sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0 1). { nra. } rewrite H10. apply Ah_prop_12. omega. nra. nra.
     assert (j=1%nat \/ (1<j)%nat). { omega. } destruct H8.
     (*j=1 case *)
     rewrite H8.
     assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0
                (pred N) = sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 2%nat + sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 3%nat (pred N)).
     { apply (sum_n_m_Chasles    (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 2%nat (pred N)). omega. omega. } rewrite H9.
     assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 3
              (pred N)=0).
     { assert (sum_n_m (fun l:nat => 0) 3%nat (pred N)=0). { apply sum_const_zero. omega. } rewrite <-H10.
       apply sum_n_m_ext_loc. intros.
       assert (  (coeff_mat Hierarchy.zero (Ah N a b a ) k 1) = 0). { apply Ah_j_1. omega. omega. } rewrite H12.
       apply (mult_zero_r (coeff_mat Hierarchy.zero (inverse_A N a b ) i k)).
     } rewrite H10.
     assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 2 +  0=sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 2 ). { nra. } rewrite H11.
     apply (Ah_prop_13 a b  i j N). omega. omega. omega. omega. nra. nra.
     assert ( (1<j<pred N)%nat \/ j= pred N). { omega. } destruct H9.
     (* 1<j<pred N *)
     assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0
              (pred N)=sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat (pred (pred j)) + sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (S (pred (pred j))) (pred N)).
     { apply (sum_n_m_Chasles  (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat (pred (pred j)) (pred N)). omega. omega. }
      rewrite H10.
      assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0
                (pred (pred j))=0).
      { assert (sum_n_m (fun l:nat => 0) 0%nat (pred (pred j)) = 0). { apply sum_const_zero. omega. } rewrite <- H11.
        apply sum_n_m_ext_loc. intros.
        assert ( (coeff_mat Hierarchy.zero (Ah N a b a ) k j) = 0). { apply Ah_pred_j. omega. omega. omega. } rewrite H13.
        apply (mult_zero_r (coeff_mat Hierarchy.zero (inverse_A N a b ) i k)). 
      } rewrite H11.
      assert ((S (pred (pred j)))= pred j). { omega. } rewrite H12.
      assert ((1<j< (N-2)%nat)%nat \/ j= (N-2)%nat). { omega. } destruct H13.
      (* 1<j< N-2 *)
      assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
                (pred j) (pred N)=sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j) (S j) + sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (S ( S j)) (pred N)).
     { apply (sum_n_m_Chasles    (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j) (S j) (pred N)). omega. omega. } rewrite H14.
      assert (sum_n_m
               (fun l : nat =>
                mult
                  (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                     l)
                  (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
               (S (S j)) (pred N)=0).
      { assert ( sum_n_m (fun l:nat => 0) (S (S j)) (pred N) = 0). { apply sum_const_zero. omega. } rewrite <-H15.
        apply sum_n_m_ext_loc. intros.
        assert ( (coeff_mat Hierarchy.zero (Ah N a b a ) k j) = 0). { apply Ah_Sj. omega. omega. omega. } rewrite H17.
        apply (mult_zero_r  (coeff_mat Hierarchy.zero (inverse_A N a b ) i k)). 
      } rewrite H15.
      assert (0 +
                (sum_n_m
                   (fun l : nat =>
                    mult
                      (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                         l)
                      (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
                   (pred j) (S j) + 0)=sum_n_m
                   (fun l : nat =>
                    mult
                      (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                         l)
                      (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
                   (pred j) (S j)). { nra. } rewrite H16. apply Ah_prop_14. omega. nra. nra.  omega. omega. omega.
      rewrite H13.
      assert ((pred (N - 2))= (N-3)%nat). { omega. } rewrite H14.
      assert (0 +
              sum_n_m
              (fun l : nat =>
                 mult 
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
                (N - 3) (pred N)=sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
                (N - 3) (pred N)).  { nra. }rewrite H15. apply (Ah_prop_15 a b i j). omega. omega. omega. omega. nra. nra.
      (* j= pred N*)
      rewrite H9.
      assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l
                      (pred N))) 0 (pred N)= sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l
                      (pred N))) 0%nat (N-3)%nat + sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l
                      (pred N))) (S (N-3)%nat) (pred N)).
      { apply (sum_n_m_Chasles  (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l
                      (pred N))) 0%nat (N-3)%nat (pred N)). omega. omega. } rewrite H10.
      assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l
                    (pred N))) 0 (N - 3)=0).
      { assert ( sum_n_m (fun l:nat => 0) 0%nat (N-3)%nat= 0). { apply sum_const_zero. omega. } rewrite <- H11.
        apply sum_n_m_ext_loc. intros.
        assert ( (coeff_mat Hierarchy.zero (Ah N a b a ) k (pred N))=0). { apply Ah_j_predN. omega. omega. }
        rewrite H13. apply (mult_zero_r  (coeff_mat Hierarchy.zero (inverse_A N a b ) i k)). 
      } rewrite H11.
      assert (  (S (N - 3))= (N-2)%nat). { omega. } rewrite H12.
      assert (0 +
              sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l
                      (pred N))) (N - 2) (pred N) =sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l
                      (pred N))) (N - 2) (pred N)). { nra. } rewrite H13. apply Ah_prop_7. omega. omega. omega. omega. nra. 
  - assert ( i=j \/ i<>j). { omega. } destruct H5.
    * rewrite <-H5. rewrite H4.
      assert ( pred N =? pred N =true). { symmetry. apply (beq_nat_refl (pred N)). }  rewrite H6. unfold sum_n.
      assert (sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 
                        (pred N) l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l (pred N))) 0
                  (pred N)= sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 
                        (pred N) l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l (pred N))) 0%nat (N-3)%nat + sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 
                        (pred N) l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l (pred N))) (S (N-3)) (pred N)).
      { apply (sum_n_m_Chasles (fun l : nat =>
                       mult
                         (coeff_mat Hierarchy.zero
                            (inverse_A N a b ) 
                            (pred N) l)
                         (coeff_mat Hierarchy.zero
                            (Ah N a b a ) l (pred N))) 0%nat (N-3)%nat (pred N)). omega. omega. } rewrite H7.
        assert (S (N-3)%nat = (N-2)%nat). { omega. } rewrite H8.
        assert (sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 
                        (pred N) l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l (pred N))) 0
                  (N - 3) = 0).
        { assert ( sum_n_m (fun l:nat => 0) 0%nat (N-3)%nat = 0). { apply sum_const_zero. omega. } rewrite <-H9.
        apply sum_n_m_ext_loc. intros.
        assert (coeff_mat Hierarchy.zero  (Ah N a b a ) k (pred N)=0). { apply Ah_j_predN. omega. omega. } rewrite H11. 
        apply (mult_zero_r (coeff_mat Hierarchy.zero  (inverse_A N a b ) (pred N) k)).
        } rewrite H9.
        assert (0 +
                  sum_n_m
                    (fun l : nat =>
                     mult
                       (coeff_mat Hierarchy.zero
                          (inverse_A N a b ) 
                          (pred N) l)
                       (coeff_mat Hierarchy.zero
                          (Ah N a b a ) l (pred N)))
                    (N - 2) (pred N)= sum_n_m
                    (fun l : nat =>
                     mult
                       (coeff_mat Hierarchy.zero
                          (inverse_A N a b ) 
                          (pred N) l)
                       (coeff_mat Hierarchy.zero
                          (Ah N a b a ) l (pred N)))
                    (N - 2) (pred N)). { nra. } rewrite H10.
        assert (sum_n_m
                    (fun l : nat =>
                     mult
                       (coeff_mat Hierarchy.zero
                          (inverse_A N a b ) 
                          (pred N) l)
                       (coeff_mat Hierarchy.zero
                          (Ah N a b a ) l (pred N)))
                    (N - 2) (pred N)= sum_n_m
                    (fun l : nat =>
                     mult
                       (coeff_mat Hierarchy.zero
                          (inverse_A N a b ) 
                          (pred N) l)
                       (coeff_mat Hierarchy.zero
                          (Ah N a b a ) l (pred N))) (N-2)%nat (N-2)%nat + sum_n_m
                    (fun l : nat =>
                     mult
                       (coeff_mat Hierarchy.zero
                          (inverse_A N a b ) 
                          (pred N) l)
                       (coeff_mat Hierarchy.zero
                          (Ah N a b a ) l (pred N))) (S (N-2)) (pred N)). 
        { apply (sum_n_m_Chasles  (fun l : nat =>
                     mult
                       (coeff_mat Hierarchy.zero
                          (inverse_A N a b ) 
                          (pred N) l)
                       (coeff_mat Hierarchy.zero
                          (Ah N a b a ) l (pred N))) (N-2)%nat (N-2)%nat (pred N)). omega. omega. } rewrite H11.
        assert ( S (N-2) = pred N). { omega. } rewrite H12.
        assert (sum_n_m
                    (fun l : nat =>
                     mult
                       (coeff_mat Hierarchy.zero
                          (inverse_A N a b ) 
                          (pred N) l)
                       (coeff_mat Hierarchy.zero
                          (Ah N a b a ) l (pred N)))
                    (N - 2) (N - 2)= (fun l : nat =>
                     mult
                       (coeff_mat Hierarchy.zero
                          (inverse_A N a b ) 
                          (pred N) l)
                       (coeff_mat Hierarchy.zero
                          (Ah N a b a ) l (pred N))) (N-2)%nat).
        { apply (sum_n_n (fun l : nat =>
                     mult
                       (coeff_mat Hierarchy.zero
                          (inverse_A N a b ) 
                          (pred N) l)
                       (coeff_mat Hierarchy.zero
                          (Ah N a b a ) l (pred N))) (N-2)%nat). } rewrite H13.
        assert (sum_n_m
                  (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 
                        (pred N) l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l (pred N)))
                  (pred N) (pred N)= (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 
                        (pred N) l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l (pred N))) (pred N)).
        { apply (sum_n_n (fun l : nat =>
                   mult
                     (coeff_mat Hierarchy.zero
                        (inverse_A N a b ) 
                        (pred N) l)
                     (coeff_mat Hierarchy.zero
                        (Ah N a b a ) l (pred N))) (pred N)). } rewrite H14.
        unfold Ah.
        assert ( coeff_mat Hierarchy.zero
                   (mk_matrix N N
                      (fun i0 j0 : nat =>
                       if i0 =? j0
                       then b
                       else
                        if i0 - j0 =? one
                        then a
                        else
                         if j0 - i0 =? one
                         then a
                         else 0)) (N - 2)  (pred N)= (fun i0 j0 : nat =>
                       if i0 =? j0
                       then b
                       else
                        if i0 - j0 =? one
                        then a
                        else
                         if j0 - i0 =? one
                         then a
                         else 0) (N-2)%nat (pred N)).
        { apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
                       if i0 =? j0
                       then b
                       else
                        if i0 - j0 =? one
                        then a
                        else
                         if j0 - i0 =? one
                         then a
                         else 0) (N-2)%nat (pred N)). omega. omega. } rewrite H15.
        assert (coeff_mat Hierarchy.zero
                   (mk_matrix N N
                      (fun i0 j0 : nat =>
                       if i0 =? j0
                       then b
                       else
                        if i0 - j0 =? one
                        then a
                        else
                         if j0 - i0 =? one
                         then a
                         else 0)) (pred N)  (pred N)= (fun i0 j0 : nat =>
                       if i0 =? j0
                       then b
                       else
                        if i0 - j0 =? one
                        then a
                        else
                         if j0 - i0 =? one
                         then a
                         else 0) (pred N) (pred N)).
        { apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
                       if i0 =? j0
                       then b
                       else
                        if i0 - j0 =? one
                        then a
                        else
                         if j0 - i0 =? one
                         then a
                         else 0) (pred N) (pred N)). omega. omega. } rewrite H16.
        assert (pred N =? pred N=true). { symmetry. apply (beq_nat_refl (pred N)). } rewrite H17. 
        assert (N - 2 =? pred N=false). { assert ((N - 2 =? pred N) = false <-> (N-2)%nat <> (pred N)). { apply (beq_nat_false_iff (N-2)%nat (pred N)). } destruct H18. apply H19. omega. }
        rewrite H18. assert (N - 2 - pred N =? one= false). { assert ((N - 2 - pred N =? one) = false <-> (N - 2 - pred N)%nat <> one). { apply (beq_nat_false_iff  (N - 2 - pred N)%nat one). }
        destruct H19. apply H20. assert ((N - 2 - pred N)%nat = 0%nat). { apply obvio_2. omega. } rewrite H21. discriminate. } rewrite H19.
        assert (pred N - (N - 2) =? one=true). { assert ((pred N - (N - 2))%nat=one). { assert( pred N = (N-1)%nat). { omega. } rewrite H20. 
        assert ((N - 1 - (N - 2))%nat =1%nat). { omega. } rewrite H21. reflexivity. }
        rewrite H20. auto. } rewrite H20. unfold inverse_A.
        assert (coeff_mat Hierarchy.zero
                 (mk_matrix N N
                    (fun i0 j0 : nat =>
                     if i0 <=? j0
                     then
                      1 / a * (-1) ^ (i0 + j0) *
                      (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
                     else
                      1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
                      / Mk N (b / a))) (pred N) (N - 2)= (fun i0 j0 : nat =>
                     if i0 <=? j0
                     then
                      1 / a * (-1) ^ (i0 + j0) *
                      (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
                     else
                      1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
                      / Mk N (b / a)) (pred N) (N - 2)%nat).
       { apply (coeff_mat_bij Hierarchy.zero  (fun i0 j0 : nat =>
                     if i0 <=? j0
                     then
                      1 / a * (-1) ^ (i0 + j0) *
                      (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
                     else
                      1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
                      / Mk N (b / a)) (pred N) (N - 2)%nat). omega. omega. } rewrite H21.
       assert (coeff_mat Hierarchy.zero
                 (mk_matrix N N
                    (fun i0 j0 : nat =>
                     if i0 <=? j0
                     then
                      1 / a * (-1) ^ (i0 + j0) *
                      (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
                     else
                      1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
                      / Mk N (b / a))) (pred N) (pred N)=(fun i0 j0 : nat =>
                     if i0 <=? j0
                     then
                      1 / a * (-1) ^ (i0 + j0) *
                      (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
                     else
                      1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
                      / Mk N (b / a)) (pred N) (pred N)).
      { apply (coeff_mat_bij  Hierarchy.zero (fun i0 j0 : nat =>
                     if i0 <=? j0
                     then
                      1 / a * (-1) ^ (i0 + j0) *
                      (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
                     else
                      1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) *
                      / Mk N (b / a)) (pred N) (pred N)). omega. omega. } rewrite H22.
      assert (pred N <=? pred N=true). { apply leb_correct. omega. } rewrite H23.
      assert (pred N <=? N - 2=false). { assert ( pred N <=? N - 2=false <-> ((N-2)%nat < (pred N))%nat). { apply leb_iff_conv. } destruct H24. apply H25. omega. } rewrite H24.
      assert ((N - pred N - 1)%nat =0%nat). { omega. } rewrite H25. 
      assert ( Mk 0 (b/a)=1). { apply Mk_B0. }rewrite H26.
      assert ((-1) ^ (pred N + pred N)= 1). { assert ((pred N + pred N)%nat = (2* (pred N))%nat). { omega. } rewrite H27. apply pow_1_even. } rewrite H27.
      assert ((-1) ^ (pred N + (N - 2)) =-1). { apply size_prop_32. apply H. } rewrite H28.
      assert (mult (1/a * -1 * (Mk (N - 2) (b/a) * 1) * / Mk N (b/a))  a=
              (1/a * -1 * (Mk (N - 2) (b/a) * 1) * / Mk N (b/a)) *  a). { reflexivity. } rewrite H29. 
      assert (1/a * -1 * (Mk (N - 2) (b/a) * 1) * / Mk N (b/a) *a =
                ( /a * a) * ( (-1 * Mk (N - 2) (b/a)) * (/ Mk N (b/a)))). { nra. } rewrite H30.
      assert (mult (1/a* 1 * (Mk (pred N) (b/a) * 1 * / Mk N (b/a)))  b=
              (1/a * 1 * (Mk (pred N) (b/a) * 1 * / Mk N (b/a))) *  b). { reflexivity. } rewrite H31.
      assert (1/a * 1 * (Mk (pred N) (b/a) * 1 * / Mk N (b/a)) *b=
               ( b/a) * ( ( Mk (pred N) (b/a))  * (/ Mk N (b/a)))). { nra. } rewrite H32.
      assert (1= /a * a). { apply Rinv_l_sym. nra. } rewrite <- H33.
      assert (1 * (-1 * Mk (N - 2) (b/a) * / Mk N (b/a)) + (b/a) * (Mk (pred N) (b/a) * / Mk N (b/a))=
                (-1 * Mk (N - 2) (b/a) + (b/a)* Mk (pred N) (b/a)) * (/ Mk N (b/a))). { nra. } rewrite H34.
      assert (Mk N (b/a) = -1 * Mk (N - 2) (b/a) + (b/a) * Mk (pred N) (b/a)).
      { assert (Mk N (b/a) + (1* 1 * Mk (N - 2) (b/a)) + ( (-b/a) * Mk (pred N) (b/a))=0 -> Mk N (b/a) = -1 * Mk (N - 2) (b/a) + (b/a) * Mk (pred N) (b/a)). { nra. } apply H35.
        assert ( Mk N (b/a) = (-1)^ (pred 1) * Mk (N-0)%nat (b/a)). { apply size_prop_33.  apply H. nra. } rewrite H36.
        assert (1 * 1 * Mk (N - 2) (b/a)=  (-1)^ (S 1) * Mk (N-2) (b/a)). { nra. } rewrite H37.
        assert ((-b/a) * Mk (pred N) (b/a) = (-1)^1 * (b/a) * Mk (N-1)%nat (b/a)). { apply size_prop_34. apply H.  nra. } rewrite H38.
        assert ((-1) ^ pred 1 * Mk (N - 0) (b/a) + (-1) ^ 2 * Mk (N - 2) (b/a) +(-1) ^ 1 * (b/a) * Mk (N - 1) (b/a)=
                  (-1) ^ pred 1 * Mk (N - 0) (b/a) + (-1) ^ 1 * (b/a) * Mk (N - 1) (b/a)+(-1) ^ 2 * Mk (N - 2) (b/a)). { nra. } rewrite  H39.
        apply Mk_prop_1. apply H. nia.
      } rewrite <-H35. apply Rinv_r. nra.
    * assert (i =? j = false). { assert ((i =? j) = false <-> i <> j). { apply (beq_nat_false_iff i j). } destruct H6. apply H7. omega. }
      rewrite H6. 
      assert ( j=0%nat \/ (0<j)%nat). { omega. } destruct H7.
      (* j=0 case *)
      rewrite H7. unfold sum_n.
      assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0
                (pred N)= sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0%nat 1%nat + sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 2%nat (pred N)).
    { apply (sum_n_m_Chasles  (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0%nat 1%nat (pred N)). omega. omega. } rewrite H8.
    assert (sum_n_m
            (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                  l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 2
            (pred N)=0).
   { assert ( sum_n_m (fun l:nat => 0) 2%nat (pred N)=0). { apply sum_const_zero. omega. }
     rewrite <- H9. apply sum_n_m_ext_loc. intros.
     assert ((coeff_mat Hierarchy.zero (Ah N a b a ) k 0) =0). { apply Ah_j_0. omega. omega. } rewrite H11.
     apply (mult_zero_r (coeff_mat Hierarchy.zero (inverse_A N a b ) i k)).
   } rewrite H9.
   assert (sum_n_m
            (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                  l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0
            1 + 0=sum_n_m
            (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                  l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l 0)) 0 1 ). { nra. } rewrite H10.
    rewrite H4. apply Ah_prop_20. apply H. nra. nra.
    assert ( j=1%nat \/ (1<j)%nat). { omega. } destruct H8.
    (* j=1 case *)
    rewrite H8.
    assert (N=3%nat \/ (3<N)%nat). { omega. } destruct H9.
    (* N=3 *)
    rewrite H9.
    assert ((pred 3)=2%nat). { omega. }rewrite H10. rewrite H4. unfold sum_n. apply Ah_prop_16. omega. nra. rewrite H9 in H1. nra.
    (* 3<N *)
    unfold sum_n.
    assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0
                (pred N)=sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 2%nat + sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 3%nat (pred N)).
    { apply (sum_n_m_Chasles (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0%nat 2%nat (pred N)). omega. omega. } rewrite H10.
    assert (sum_n_m
            (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                  l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 3
            (pred N)=0).
    { assert (sum_n_m (fun l:nat => 0) 3%nat (pred N)=0). { apply sum_const_zero. omega. } 
      rewrite <- H11. apply sum_n_m_ext_loc. intros.
      assert ( (coeff_mat Hierarchy.zero (Ah N a b a ) k 1)=0). { apply Ah_j_1. omega. omega. }
      rewrite H13. apply (mult_zero_r  (coeff_mat Hierarchy.zero (inverse_A N a b ) i k)).
    } rewrite H11.
    assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 2 + 0 =sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l 1)) 0 2). { nra. } rewrite H12. rewrite H4.
    apply Ah_prop_18. omega. nra. nra.
    assert ((1<j<(pred N))%nat \/ j = pred N). { omega. } destruct H9. unfold sum_n.
    assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0
              (pred N) =sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat (pred (pred j)) + sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (S (pred (pred j))) (pred N)).
    { apply (sum_n_m_Chasles   (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat (pred (pred j)) (pred N)). omega. omega. }
     rewrite H10.
     assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0
                (pred (pred j))=0).
    { assert (sum_n_m (fun l:nat => 0) 0%nat (pred (pred j)) =0). { apply sum_const_zero. omega. } rewrite <-H11.
      apply sum_n_m_ext_loc. intros.
      assert ( (coeff_mat Hierarchy.zero (Ah N a b a ) k j)=0). { apply Ah_pred_j. omega. omega. omega. } rewrite H13.
      apply (mult_zero_r  (coeff_mat Hierarchy.zero (inverse_A N a b ) i k)).
     } rewrite H11.
     assert (  (S (pred (pred j)))= pred j). { omega. } rewrite H12.
     assert ( (1<j<(N-2)%nat)%nat \/ j= (N-2)%nat). { omega. } destruct H13.
     (* 1< j < N-2 *)
     assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
              (pred j) (pred N)=sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (pred j) (S j) + sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (S (S j)) (pred N)).
    { apply (sum_n_m_Chasles (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  (pred j) (S j) (pred N)). omega. omega. } rewrite H14.
    assert ( sum_n_m
               (fun l : nat =>
                mult
                  (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                     l)
                  (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
               (S (S j)) (pred N)=0).
    { assert(sum_n_m (fun l:nat => 0) (S (S j)) (pred N) =0). { apply sum_const_zero. omega. } rewrite <- H15.
      apply sum_n_m_ext_loc. intros.
      assert (  (coeff_mat Hierarchy.zero (Ah N a b a ) k j) = 0). { apply Ah_Sj. omega. omega. omega. } rewrite H17.
      apply (mult_zero_r (coeff_mat Hierarchy.zero (inverse_A N a b ) i k)).
    } rewrite H15.
    assert (0 +
            (sum_n_m
               (fun l : nat =>
                mult
                  (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                     l)
                  (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
               (pred j) (S j) + 0)=sum_n_m
               (fun l : nat =>
                mult
                  (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                     l)
                  (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
               (pred j) (S j)). { nra. } rewrite H16. apply Ah_prop_19. omega. omega. omega. omega. nra. nra.
   (* j=N-2 *)
   rewrite H13.
   assert ((pred (N - 2))= (N-3)%nat). { omega. } rewrite H14.
   assert (0 +
            sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
              (N - 3) (pred N)=sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l (N - 2)))
              (N - 3) (pred N)). { nra. } rewrite H15. rewrite H4. apply Ah_prop_17. omega.  nra. nra.
    (* j=pred N *)
    unfold sum_n.
    assert (sum_n_m
            (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                  l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0
            (pred N)=sum_n_m
            (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                  l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0%nat (N-3)%nat +sum_n_m
            (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                  l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) (S (N-3)%nat) (pred N)).
    { apply (sum_n_m_Chasles  (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                  l)
               (coeff_mat Hierarchy.zero (Ah N a b a ) l j))  0%nat (N-3)%nat (pred N)). omega. omega. } rewrite H10.
    assert ((S (N - 3))= (N-2)%nat). { omega. } rewrite H11.
    assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                    l)
                 (coeff_mat Hierarchy.zero (Ah N a b a ) l j)) 0
              (N - 3)=0).
    { assert ( sum_n_m (fun l:nat => 0) 0%nat (N-3)%nat = 0).  { apply sum_const_zero. omega. }
      rewrite <- H12. apply sum_n_m_ext_loc. intros.
      assert ( (coeff_mat Hierarchy.zero (Ah N a b a ) k j) = 0). { rewrite H9. apply Ah_j_predN. omega. omega. } rewrite H14.
      apply (mult_zero_r (coeff_mat Hierarchy.zero (inverse_A N a b ) i k)).
    } rewrite H12. 
    assert (0 +
              sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
                (N - 2) (pred N)= sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (inverse_A N a b ) i
                      l)
                   (coeff_mat Hierarchy.zero (Ah N a b a ) l j))
                (N - 2) (pred N)). { nra. } rewrite H13. apply Ah_prop_7. omega. omega. omega. apply H5. nra.
Qed.


Hypothesis inverse_property: forall (N:nat) (A: matrix N N) (B:matrix N N), Mmult A B = identity N -> Mmult B A = identity N.

Lemma invertible_check_2 (a b:R): forall (N:nat), (2<N)%nat -> (0< a) -> Mk N (b/a) <> 0 ->  Mmult (Ah N a b a ) (inverse_A N a b ) = identity N.
Proof.
intros.
apply (inverse_property N (inverse_A N a b )  (Ah N a b a ) ).
apply invertible_check_1. omega. nra. nra.
Qed.

Lemma invertible_check (a b:R) : forall (N:nat), (2<N)%nat -> 0<a ->
    Mk N (b/a) <> 0 -> invertible N (Ah N a b a ) (inverse_A N a b ).
Proof.
intros.
unfold invertible.
split.
+ apply invertible_check_1. omega. nra. nra.
+ apply invertible_check_2. omega. nra. nra.
Qed.

