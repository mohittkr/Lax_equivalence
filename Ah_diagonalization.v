(********** Formalizing the diagonalization of Ah (a, b, a), i.e., Ah= S L S^{-1},
            L is a diagonal matrix with eigen values along the diagonal
            S is the eigen matrix 
            We also prove that S is orthogonal matrix, i.e., S^{-1}=S^T
***************************************************************************)
Require Import Reals Psatz Omega.
Require Import Coquelicot.Hierarchy.
Require Import Ah_properties.
Require Import Eigen_system.
Require Import linear_algebra.
Require Import Coq.Init.Nat.
Require Import Arith.Even.
Require Import R_sqrt Rpower.


(* Proof that A= S L S^{-1} *)

Definition Lam (N:nat) (a b:R):= mk_matrix N N (fun i j => if (eqb i j) then (coeff_mat 0 (Lambda i N a b a) 0%nat 0%nat) else 0).


Definition Sm (N:nat) (a b:R) := mk_matrix N N (fun i j => coeff_mat 0 (Eigen_vec j N a b a) i 0%nat).

Definition Stranspose (N:nat) (a b:R):= mat_transpose N (Sm N a b).


(* Proof that S is invertible and SS^{T}=I and S^{T}S=I *)

Lemma even_1: forall i j:nat, (i>j)%nat -> even (i-j) -> even (i+j+2).
Proof.
intros.
assert (even (i + j + 2) <-> Nat.Even (i+j+2)). { apply even_equiv. }
destruct H1. apply H2.
assert ( even (i-j) <-> Nat.Even (i-j)). { apply even_equiv. } destruct H3.
specialize (H3 H0).
unfold Nat.Even. unfold Nat.Even in H2. destruct H3.
exists ((j+x+1)%nat).
assert ( (2 * (j + x + 1))%nat = (2 * j + 2*x + 2)%nat). { nia. } rewrite H5.
rewrite <-H3. assert ( (i>j)%nat -> (i + j + 2)%nat = (2 * j + (i - j) + 2)%nat). { intros. omega. }
specialize (H6 H). apply H6.
Qed.

Lemma odd_1: forall i j:nat, (i>j)%nat -> odd (i-j) -> odd (i+j+2).
Proof.
intros.
assert (odd (i + j + 2) <-> Nat.Odd (i+j+2)). { apply odd_equiv. }
destruct H1. apply H2.
assert ( odd (i-j) <-> Nat.Odd (i-j)). { apply odd_equiv. } destruct H3.
specialize (H3 H0).
unfold Nat.Odd. unfold Nat.Odd in H3. destruct H3.
exists ( (j+x+1)%nat).
assert ((2 * (j + x + 1) + 1)%nat= (2* j + (2*x+1)+2)%nat). { omega. } rewrite H5. rewrite <-H3.
omega.
Qed.

Lemma even_2: forall i j:nat, (i<j)%nat -> even (j-i) -> even (i+j+2).
Proof.
intros.
assert (even (i + j + 2) <-> Nat.Even (i+j+2)). { apply even_equiv. }
destruct H1. apply H2.
assert ( even (j-i) <-> Nat.Even (j-i)). { apply even_equiv. } destruct H3.
specialize (H3 H0).
unfold Nat.Even. unfold Nat.Even in H3. destruct H3.
exists ((i+x+1)%nat).
assert ( (2 * (i + x + 1))%nat= (2* i + 2*x + 2)%nat). { nia. } rewrite H5.
rewrite <-H3. nia.
Qed.

Lemma odd_2: forall i j:nat, (i<j)%nat -> odd (j-i) -> odd (i+j+2).
Proof.
intros.
assert (odd (i + j + 2) <-> Nat.Odd (i+j+2)). { apply odd_equiv. }
destruct H1. apply H2.
assert ( odd (j-i) <-> Nat.Odd (j-i)). { apply odd_equiv. } destruct H3.
specialize (H3 H0).
unfold Nat.Odd. unfold Nat.Odd in H3. destruct H3.
exists ( (i+x+1)%nat).
assert ((2 * (i + x + 1) + 1)%nat= (2* i + (2*x+1)+2)%nat). { omega. } rewrite H5. rewrite <-H3.
omega.
Qed.

Lemma even_3: forall i j:nat, (i>j)%nat -> Nat.Even (i+j+2)-> ~odd (i+j+2).
Proof.
intros. unfold not. apply (not_even_and_odd (i+j+2)).
assert (even (i+j+2) <-> Nat.Even (i+j+2)). { apply even_equiv. } destruct H1. apply H2. apply H0.
Qed.

Lemma not_odd_and_even n : odd n -> even n -> False.
Proof.
  induction n.
  - intros Ev Od. inversion Ev.
  - intros Ev Od. inversion Od. inversion Ev. auto with arith.
Qed.

Lemma odd_4: forall i j:nat, (i>j)%nat -> Nat.Odd (i+j+2)-> ~even (i+j+2).
Proof.
intros. unfold not.  apply (not_odd_and_even (i+j+2)).
assert (odd (i+j+2) <-> Nat.Odd (i+j+2)). { apply odd_equiv. } destruct H1. apply H2. apply H0.
Qed.

Lemma even_4: forall i j:nat, (i<j)%nat -> Nat.Even (i+j+2)-> ~odd (i+j+2).
Proof.
intros. unfold not. apply (not_even_and_odd (i+j+2)).
assert (even (i+j+2) <-> Nat.Even (i+j+2)). { apply even_equiv. } destruct H1. apply H2. apply H0.
Qed.

Lemma odd_5: forall i j:nat, (i<j)%nat -> Nat.Odd (i+j+2)-> ~even (i+j+2).
Proof.
intros. unfold not.  apply (not_odd_and_even (i+j+2)).
assert (odd (i+j+2) <-> Nat.Odd (i+j+2)). { apply odd_equiv. } destruct H1. apply H2. apply H0.
Qed.


Hypothesis cos_series_sum: forall (a d:R) (N:nat), d <>0 -> sum_n_m (fun l:nat => cos (a+(INR l)*d)) 0 (pred N)= sin(INR N*d/2)* cos(a+INR(N-1)*d/2)*/ sin(d/2).

Lemma cos_series_sum_neg: forall (a d:R) (N:nat), d <>0 -> sum_n_m (fun l:nat => - cos (a+(INR l)*d)) 0 (pred N)= - sin(INR N*d/2)* cos(a+INR(N-1)*d/2)*/ sin(d/2).
Proof.
intros.
assert (sum_n_m (fun l : nat => - cos (a + INR l * d)) 0 (pred N)= - sum_n_m (fun l : nat => cos (a + INR l * d)) 0 (pred N)).
{ assert ( sum_n_m (fun l : nat => - cos (a + INR l * d)) 0 (pred N)= sum_n_m (fun l : nat => (-1)* cos (a + INR l * d)) 0 (pred N)).
  { apply sum_n_m_ext_loc. intros. nra. } 
  assert (- sum_n_m (fun l : nat => cos (a + INR l * d)) 0 (pred N)= (-1) * sum_n_m (fun l : nat => cos (a + INR l * d)) 0 (pred N)). { nra. }
  rewrite H0. rewrite H1.
  apply (sum_n_m_mult_l (-1) (fun l : nat => cos (a + INR l * d))).
} rewrite H0.
assert (- sin (INR N * d / 2) * cos (a + INR (N - 1) * d / 2) * / sin (d / 2)=
          - (sin (INR N * d / 2) * cos (a + INR (N - 1) * d / 2) * / sin (d / 2))). { nra. } rewrite H1.
apply Ropp_eq_compat. apply cos_series_sum. apply H. 
Qed.

Hypothesis sum_const: forall N:nat, (0<N)%nat -> sum_n_m (fun _ : nat => 1) 0 (pred N) = INR N.

Lemma sin_a_cos_b: forall a b:R, sin a * cos b = ( sin (a+b) + sin (a-b))/2.
Proof.
intros.
assert (sin (a + b)= sin a * cos b + cos a * sin b). { apply sin_plus. } 
assert (sin (a - b)= sin a * cos b - cos a * sin b). { apply sin_minus. }
rewrite H. rewrite H0. nra.
Qed.

Lemma sinA_sinB: forall (A B C: R), A*(sin(B))*(sin(C)) = (A*/2)*(cos(B-C) - cos(B+C)).
Proof.
  intros. rewrite cos_plus. assert((B-C) = B+(-C)). { intuition. }
  rewrite H. rewrite cos_plus. rewrite sin_antisym. rewrite <- cos_sym.
  assert(- (cos B * cos C - sin B * sin C) = -cos(B) * cos(C) + sin(B) * sin(C)).
  { symmetry. rewrite <- Rmult_1_r. assert(- (cos B * cos C - sin B * sin C) * 1 =
                                           -1*(cos B * cos C - sin B * sin C)).
    nra. rewrite H0. nra. }
  nra.
Qed.

Lemma cosA_cosB: forall (X0 Y0: R), cos(X0) * cos(Y0) = 1/2 * (cos(X0-Y0) + cos(X0+Y0)).
Proof.
  intros.
  assert(cos(X0-Y0) = cos X0 * cos Y0 + sin X0 * sin Y0). {apply cos_minus. } rewrite H.
  assert(cos(X0+Y0) = cos X0 * cos Y0 - sin X0 * sin Y0). {apply cos_plus. } rewrite H0.
  nra.
Qed.

Lemma sin_sqr_sum: forall (i N:nat), (2<N)%nat /\ (0<=i<N)%nat -> sum_n_m (fun l:nat => (2/(INR(N+1)))*sin(((INR l+1)* INR (i+1)*PI) */ INR (N+1)) ^2) 0 (pred N)=1.
Proof.
intros.
assert (sum_n_m
              (fun l : nat =>
               2 / INR (N + 1) *
               sin ((INR l + 1) * INR (i + 1) * PI * / INR (N + 1))
               ^ 2) 0 (pred N)= (2/INR(N+1)) * sum_n_m (fun l:nat => sin ((INR l + 1) * INR (i + 1) * PI * / INR (N + 1))^ 2) 0 (pred N)).
{ apply (sum_n_m_mult_l (2/INR(N+1)) (fun l:nat => sin ((INR l + 1) * INR (i + 1) * PI * / INR (N + 1))^ 2) 0 (pred N)). }
rewrite H0. 
assert (1= (2 / INR (N + 1)) * (/ (2 / INR (N + 1)))).
{ apply Rinv_r_sym. assert (0< 2 / INR (N + 1) -> 2 / INR (N + 1) <> 0). { nra. } apply H1.
  assert (2 / INR (N + 1)= 2 * (/ INR(N+1))). { nra. } rewrite H2. apply Rmult_lt_0_compat. nra. apply Rinv_0_lt_compat. apply lt_0_INR. omega.
} rewrite H1.
apply Rmult_eq_compat_l.
assert (/ (2 / INR (N + 1))= INR(N+1)/2). 
{ assert ((2 / INR (N + 1))= 2 * (/ INR (N+1))). { nra. } rewrite H2.
  assert (/ (2 * / INR (N + 1))= /2 * // INR (N + 1)). { apply Rinv_mult_distr. nra. assert (0 < / INR (N + 1)-> / INR (N + 1) <> 0). { nra. } apply H3.
  apply Rinv_0_lt_compat. apply lt_0_INR. omega. } rewrite H3.
  assert (/ / INR (N + 1)= INR (N+1)). { apply Rinv_involutive. assert (0< INR (N+1) ->INR (N + 1) <> 0). { nra. } apply H4. apply lt_0_INR. omega. } rewrite H4. nra.
} 
rewrite H2.
assert (sum_n_m
            (fun l : nat =>
             sin
               ((INR l +
                 2 / INR (N + 1) * (INR (N + 1) / 2)) *
                INR (i + 1) * PI * / INR (N + 1)) ^ 2) 0
            (pred N)= sum_n_m (fun l:nat=> 1/2 - (1/2)* cos (2* (INR(l+1)*INR(i+1)*PI*/(INR(N+1))))) 0 (pred N)).
{ apply sum_n_m_ext_loc.
  intros.
  assert (1 / 2 -1 / 2 *cos  (2 * (INR (k + 1) * INR (i + 1)*PI */ INR (N + 1)))= (1/2) * (1-cos  (2 * (INR (k + 1) * INR (i + 1)*PI* / INR (N + 1))))). { nra. } rewrite H4.
  assert ((1-cos  (2 * (INR (k + 1) * INR (i + 1)*PI* / INR (N + 1))))= 2*sin((INR (k + 1) * INR (i + 1)*PI* / INR (N + 1)))*sin((INR (k + 1) * INR (i + 1)*PI* / INR (N + 1)))).
  { symmetry. apply Rplus_eq_reg_l with (-1). 
    assert (-1 +(1 - cos (2 * (INR (k + 1) * INR (i + 1)*PI* / INR (N + 1))))=- cos (2 * (INR (k + 1) * INR (i + 1)*PI */ INR (N + 1)))). { nra. } rewrite H5.
    assert (-1 +2 * sin (INR (k + 1) * INR (i + 1)*PI* / INR (N + 1)) *sin (INR (k + 1) * INR (i + 1)*PI* / INR (N + 1))=
              -(1-2 * sin (INR (k + 1) * INR (i + 1)*PI* / INR (N + 1)) *sin (INR (k + 1) * INR (i + 1)*PI* / INR (N + 1)))). { nra. } rewrite H6.
    apply Ropp_eq_compat. symmetry. apply cos_2a_sin.
  } rewrite H5. 
  assert (1 / 2 *
              (2 * sin (INR (k + 1) * INR (i + 1)*PI* / INR (N + 1)) *
               sin (INR (k + 1) * INR (i + 1)*PI* / INR (N + 1)))= sin (INR (k + 1) * INR (i + 1)*PI* / INR (N + 1)) *
               sin (INR (k + 1) * INR (i + 1)*PI* / INR (N + 1))). { nra. } rewrite H6.
  assert(((INR k + 2 / INR (N + 1) * (INR (N + 1) / 2)) * INR (i + 1) * PI * / INR (N + 1))=
            (INR (k + 1) * INR (i + 1)*PI / INR (N + 1))).
  { assert (INR (k+1)= INR k + INR 1). { apply plus_INR. } rewrite H7. assert (INR 1 =1). { reflexivity. } rewrite H8.
    rewrite H1. 
  assert ((INR k + 2 / INR (N + 1) * / (2 / INR (N + 1))) *INR (i + 1) * PI / INR (N + 1)=
          (INR k + 2 / INR (N + 1) * / (2 / INR (N + 1))) *INR (i + 1) * PI* / INR (N + 1)). { nra. } rewrite H9. rewrite H2. reflexivity.
  } rewrite H7. nra.
} rewrite H3.
assert (sum_n_m
            (fun l : nat =>
             1 / 2 -
             1 / 2 *
             cos
               (2 *
                (INR (l + 1) * INR (i + 1) * PI * / INR (N + 1))))
                0 (pred N)= sum_n_m
                  (fun l : nat =>
                   1 / 2 + (-
                   (1 / 2 *
                   cos
                     (2 *
                      (INR (l + 1) * INR (i + 1) * PI * / INR (N + 1))))))
                  0 (pred N)). 
{ apply sum_n_m_ext_loc. intros. nra. }
rewrite H4.
assert (sum_n_m
  (fun l : nat =>
   1 / 2 +
   -
   (1 / 2 *
    cos
      (2 *
       (INR (l + 1) * INR (i + 1) * PI * / INR (N + 1)))))
  0 (pred N)= sum_n_m (fun l:nat => 1/2) 0%nat (pred N) + sum_n_m (fun l:nat => -
       (1 / 2 * cos  (2 * (INR (l + 1) * INR (i + 1) * PI * / INR (N + 1))))) 0 (pred N)).
{ apply (sum_n_m_plus (fun l:nat => 1/2) (fun l:nat => -
       (1 / 2 * cos  (2 * (INR (l + 1) * INR (i + 1) * PI * / INR (N + 1))))) 0%nat (pred N)). } rewrite H5.
assert (sum_n_m (fun _ : nat => 1 / 2) 0 (pred N)= (INR N)/2).
{ assert (sum_n_m (fun _ : nat => 1 / 2) 0 (pred N) = sum_n_m (fun _ : nat => (1 / 2) *1) 0 (pred N)).
  { apply sum_n_m_ext_loc. intros. nra. } rewrite H6.
  assert (sum_n_m (fun _ : nat => (1 / 2)*1) 0 (pred N)= (1/2) * sum_n_m (fun _: nat =>1) 0%nat (pred N)).
  { apply (sum_n_m_mult_l (1/2) (fun _: nat =>1) 0%nat (pred N)). } rewrite H7.
  assert (INR N / 2= (1/2)* INR N). { nra. } rewrite H8.
  apply Rmult_eq_compat_l.  apply sum_const. omega.
} rewrite H6.
assert (INR (N+1) = INR N + INR 1). { apply plus_INR. } rewrite H7. assert (INR 1 = 1). { reflexivity. } rewrite H8.
assert ( (INR N + 1) / 2= (INR N)/2 + 1/2). { nra. } rewrite H9.
apply Rplus_eq_compat_l.
assert (sum_n_m
  (fun l : nat =>
   -
   (1 / 2 *
    cos
      (2 *
       (INR (l + 1) * INR (i + 1) * PI * / (INR N + 1)))))
  0 (pred N)= sum_n_m (fun l:nat => (-1/2)*  cos (2 * (INR (l + 1) * INR (i + 1) * PI * / (INR N + 1)))) 0%nat (pred N)).
{ apply sum_n_ext_loc.
  intros. nra. 
} rewrite H10.
assert (sum_n_m
            (fun l : nat =>
             -1 / 2 *
             cos
               (2 *
                (INR (l + 1) * INR (i + 1) * PI * / (INR N + 1))))
            0 (pred N)= (-1/2) * sum_n_m(fun l:nat =>  cos  (2 * (INR (l + 1) * INR (i + 1) * PI * / (INR N + 1)))) 0%nat (pred N)).
{ apply (sum_n_m_mult_l (-1/2) (fun l:nat =>  cos  (2 * (INR (l + 1) * INR (i + 1) * PI * / (INR N + 1)))) 0%nat (pred N)). } rewrite H11.
assert (1 / 2= (-1/2) * (-1)). { nra. } rewrite H12.
apply Rmult_eq_compat_l.
assert (sum_n_m
  (fun l : nat =>
   cos
     (2 *
      (INR (l + 1) * INR (i + 1) * PI * / (INR N + 1))))
  0 (pred N)= sum_n_m (fun l:nat => cos ( ((2*PI*INR (i+1))*/INR (N+1))+  INR l * (2*PI*INR (i+1)*/INR (N+1)))) 0%nat (pred N)).
{ apply sum_n_m_ext_loc.
  intros. 
  assert ((2 * (INR (k + 1) * INR (i + 1) * PI * / (INR N + 1))) =(2 * PI * INR (i + 1) * / INR (N + 1) +
              INR k * (2 * PI * INR (i + 1) * / INR (N + 1)))). 
  { assert (INR (k+1)= INR k + INR 1). { apply plus_INR. } rewrite H14.
    assert (INR 1=1). { reflexivity. } rewrite H15.
    assert (INR k * (2 * PI * INR (i + 1) * / INR (N + 1))= 2* ( INR k * INR (i+1) * PI */ INR (N+1))). { nra. } rewrite H16.
    assert ( 2 * PI * INR (i + 1) * / INR (N + 1)= 2 * (1* INR (i+1) * PI */ INR (N+1))). { nra. } rewrite H17.
    assert (((INR k + 1) * INR (i + 1) * PI * / (INR N + 1))= (INR k + 1) * (INR (i + 1) * PI * / (INR N + 1))). { nra. } rewrite H18.
    assert ((INR k + 1) * (INR (i + 1) * PI * / (INR N + 1))= INR k * (INR (i + 1) * PI * / (INR N + 1))+ 1 * (INR (i + 1) * PI * / (INR N + 1))). { nra. } rewrite H19.
    assert (2 *(INR k * (INR (i + 1) * PI * / (INR N + 1)) + 1 * (INR (i + 1) * PI * / (INR N + 1)))=
              2* (INR k * (INR (i + 1) * PI * / (INR N + 1))) + 2* (1 * (INR (i + 1) * PI * / (INR N + 1)))).  { nra. } rewrite H20.
    assert (2 * (INR k * (INR (i + 1) * PI * / (INR N + 1)))=2 * (INR k * INR (i + 1) * PI * / INR (N + 1))).
    { apply Rmult_eq_compat_l. 
      assert (INR (N+1) = INR N + INR 1). { apply plus_INR. } rewrite H21. assert (INR 1=1). { reflexivity. } rewrite H22. nra.
    } rewrite H21.
    assert (2 * (1 * (INR (i + 1) * PI * / (INR N + 1)))=2 * (1 * INR (i + 1) * PI * / INR (N + 1))).
    { assert (INR (N+1)= INR N + INR 1). { apply plus_INR. } rewrite H22. assert (INR 1=1). { reflexivity. } rewrite H23. nra. } rewrite H22. nra.
   } rewrite H14. reflexivity.
}
rewrite H13.
assert (sum_n_m
            (fun l : nat =>
             cos
               (2 * PI * INR (i + 1) * / INR (N + 1) +
                INR l * (2 * PI * INR (i + 1) * / INR (N + 1))))
            0 (pred N)= sin(INR N*(2*PI*(INR (i+1))*/ INR (N+1))/2)* cos((2*PI*(INR (i+1)) */ INR (N+1))+INR(N-1)*(2* PI*(INR (i+1)) */INR (N+1))/2)*/ sin((2*PI*(INR (i+1)) */ INR (N+1))/2)).
{ apply (cos_series_sum (2*PI* (INR (i+1))*/ INR (N+1)) (2*PI* (INR (i+1))*/ INR (N+1)) N). 
  apply Rmult_integral_contrapositive_currified. apply Rmult_integral_contrapositive_currified.  apply Rmult_integral_contrapositive_currified.  nra. apply PI_neq0. 
  assert (0< INR (i+1) -> INR (i + 1) <> 0). { nra. } apply H14. apply lt_0_INR. omega.
  assert (0< / INR (N + 1) -> / INR (N + 1) <> 0). { nra. } apply H14.
  apply Rinv_0_lt_compat. apply lt_0_INR. omega.
} rewrite H14.
assert (cos
        (2 * PI * INR (i + 1) * / INR (N + 1) +
         INR (N - 1) *
         (2 * PI * INR (i + 1) * / INR (N + 1)) / 2)= cos (PI* INR (i+1))).
{ assert ((2 * PI * INR (i + 1) * / INR (N + 1) +
               INR (N - 1) *
               (2 * PI * INR (i + 1) * / INR (N + 1)) / 2)=  (PI * INR (i + 1))).
  { assert (INR (N - 1) *(2 * PI * INR (i + 1) * / INR (N + 1)) / 2= (INR (N-1) * PI * INR (i+1))/ INR (N+1)). { nra. } rewrite H15.
    assert (2 * PI * INR (i + 1) * / INR (N + 1) + INR (N - 1) * PI * INR (i + 1) / INR (N + 1)=
            (2 * PI * INR (i + 1) + INR (N - 1) * PI * INR (i + 1)) / INR (N+1)). { nra. } rewrite H16.
    assert ((2 * PI * INR (i + 1) + INR (N - 1) * PI * INR (i + 1))= PI * INR (i+1) * INR (N+1)).
    { assert ( INR (N+1) = INR N + INR 1). { apply plus_INR. } rewrite H17. assert ( INR 1 = 1). { reflexivity. }  rewrite H18.
      assert (INR (N - 1)= INR N - INR 1). { apply minus_INR. omega. } rewrite H19. assert ( INR 1 = 1). { reflexivity. } rewrite H20. nra.
    } rewrite H17.
    assert (PI * INR (i + 1) * INR (N + 1) / INR (N + 1)= PI * INR (i+1) * (INR (N+1) * (/ INR (N+1)))). { nra. }rewrite H18.
    assert ( 1 = (INR (N+1) * (/ INR (N+1)))). { apply Rinv_r_sym. assert (0< INR (N+1)-> INR (N + 1) <> 0). { nra. } apply H19. apply lt_0_INR. omega.  }
    rewrite <-H19.  nra.
  } rewrite H15. reflexivity.
} rewrite H15.
assert (sin
            (INR N *
             (2 * PI * INR (i + 1) * / INR (N + 1)) / 2) *
          cos (PI * INR (i + 1))= (sin( (PI * INR N * INR (i+1))/INR (N+1) + PI * INR (i+1)) - sin ( (PI * INR (i+1))/INR (N+1)))/2).
{ assert (sin  (INR N *   (2 * PI * INR (i + 1) * / INR (N + 1)) / 2) *cos (PI * INR (i + 1))=
          (sin ((INR N *   (2 * PI * INR (i + 1) * / INR (N + 1)) / 2)+ (PI * INR (i + 1))) + sin ((INR N *   (2 * PI * INR (i + 1) * / INR (N + 1)) / 2)- (PI * INR (i + 1))))/2).
  { apply sin_a_cos_b. } rewrite H16.
  assert ((sin (PI * INR N * INR (i + 1) / INR (N + 1) +  PI * INR (i + 1)) - sin (PI * INR (i + 1) / INR (N + 1)))=
          sin (PI * INR N * INR (i + 1) / INR (N + 1) + PI * INR (i + 1)) + (- sin (PI * INR (i + 1) / INR (N + 1)))). { nra. } rewrite H17.
  assert (sin (-(PI * INR (i + 1) / INR (N + 1)))=  - sin (PI * INR (i + 1) / INR (N + 1))). { apply sin_neg. } rewrite <-H18. 
  assert ((INR N *    (2 * PI * INR (i + 1) * / INR (N + 1)) / 2 +    PI * INR (i + 1))= 
            (PI * INR N * INR (i + 1) / INR (N + 1) +    PI * INR (i + 1))). { nra. } rewrite H19.
  assert ( (INR N * (2 * PI * INR (i + 1) * / INR (N + 1)) / 2 -  PI * INR (i + 1))= -(PI * INR (i + 1) / INR (N + 1))). 
  { assert ( INR N * (2 * PI * INR (i + 1) * / INR (N + 1)) /2= INR N * PI * INR (i + 1) * / INR (N + 1)). { nra. } rewrite H20.
    assert (PI * INR (i + 1 ) = (PI * INR (i+1) * INR (N+1))/ INR (N+1)). 
    { assert (PI * INR (i + 1) * INR (N + 1) / INR (N + 1)= PI * INR (i+1) * (INR (N+1) * (/ INR (N+1)))). { nra. } rewrite H21.
      assert (1=(INR (N + 1) * / INR (N + 1))). { apply Rinv_r_sym. assert ( 0 < INR (N+1)-> INR (N + 1) <> 0). { nra. } apply H22. apply lt_0_INR. omega. } 
      rewrite <-H22. nra.
    } rewrite H21.
    assert (INR N * PI * INR (i + 1) * / INR (N + 1) -PI * INR (i + 1) * INR (N + 1) / INR (N + 1) =
              ( INR N * PI * INR (i + 1) + - PI * INR (i + 1) * INR (N + 1))/ INR (N+1)). { nra. } rewrite H22.
    rewrite <-H21. 
    assert ((INR N * PI * INR (i + 1) + - PI * INR (i + 1) * INR (N + 1))=  - (PI * INR (i + 1))). 
    { assert ( INR (N+1) = INR N+ INR 1). { apply plus_INR. } rewrite H23. assert (INR 1= 1). { reflexivity. }rewrite H24. nra. }
    rewrite H23. nra.
  } rewrite H20. reflexivity.
}  
rewrite H16.
assert (sin (2 * PI * INR (i + 1) * / INR (N + 1) / 2)= sin ( PI * INR (i + 1) * / INR (N + 1) )).
{ assert ((2 * PI * INR (i + 1) * / INR (N + 1) / 2)=PI * INR (i + 1) * / INR (N + 1)).  { nra. } rewrite H17. reflexivity. } rewrite H17.
assert ((sin  (PI * INR N * INR (i + 1) / INR (N + 1) +
            PI * INR (i + 1)) -
         sin (PI * INR (i + 1) / INR (N + 1))) / 2 *
        / sin (PI * INR (i + 1) * / INR (N + 1))= sin  (PI * INR N * INR (i + 1) / INR (N + 1) +
            PI * INR (i + 1))/ (2*  sin (PI * INR (i + 1) * / INR (N + 1))) - 1/2).
{ assert ((sin (PI * INR N * INR (i + 1) / INR (N + 1) +  PI * INR (i + 1)) - sin (PI * INR (i + 1) / INR (N + 1))) / 2=
            (sin (PI * INR N * INR (i + 1) / INR (N + 1) +  PI * INR (i + 1)))/2 - sin (PI * INR (i + 1) / INR (N + 1))/2). { nra. } rewrite H18.
  assert( (sin
             (PI * INR N * INR (i + 1) / INR (N + 1) +
              PI * INR (i + 1)) / 2 -
           sin (PI * INR (i + 1) / INR (N + 1)) / 2) *
          / sin (PI * INR (i + 1) * / INR (N + 1))= (sin
             (PI * INR N * INR (i + 1) / INR (N + 1) +
              PI * INR (i + 1)) / 2) * (/  sin (PI * INR (i + 1) * / INR (N + 1))) - (sin (PI * INR (i + 1) / INR (N + 1)) / 2) * (/  sin (PI * INR (i + 1) * / INR (N + 1)))).
  { nra. } rewrite H19.
  assert (sin (PI * INR (i + 1) / INR (N + 1)) / 2 */ sin (PI * INR (i + 1) * / INR (N + 1))= 1/2). 
  { assert (sin (PI * INR (i + 1) / INR (N + 1)) / 2 */ sin (PI * INR (i + 1) * / INR (N + 1))=
          (/2) * (sin (PI * INR (i + 1) / INR (N + 1)) * (/ sin (PI * INR (i + 1) * / INR (N + 1))))). { nra. } rewrite H20.
    assert ( 1= (sin (PI * INR (i + 1) / INR (N + 1)) * / sin (PI * INR (i + 1) * / INR (N + 1)))).
    { apply Rinv_r_sym.
       assert ( 0 < sin (PI * INR (i + 1) * / INR (N + 1)) -> sin (PI * INR (i + 1) * / INR (N + 1)) <> 0). { nra. } apply H21.
        apply sin_gt_0.
        assert (PI * INR (i + 1) * / INR (N + 1)= PI * (INR (i + 1) * / INR (N + 1))). { nra. } rewrite H22.
        apply Rmult_lt_0_compat. apply PI_RGT_0. 
        apply Rmult_lt_0_compat. apply lt_0_INR. omega. apply Rinv_0_lt_compat. apply lt_0_INR. omega. 
        assert (PI= PI * 1). { nra. } rewrite H22.
        assert (PI * 1 * INR (i + 1) * / INR (N + 1)= PI * (INR (i + 1) * / INR (N + 1))). { nra. } rewrite H23.
        apply Rmult_lt_compat_l. apply PI_RGT_0. 
        assert (1= INR (N+1) * (/ INR (N+1))). { apply Rinv_r_sym. assert ( 0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H24. apply lt_0_INR. omega. }
        rewrite H24. apply Rmult_lt_compat_r. apply Rinv_0_lt_compat. apply lt_0_INR. omega. apply lt_INR. omega.
    } rewrite <- H21. nra.
  } rewrite H20.
  apply Rplus_eq_compat_r. 
  assert (sin
              (PI * INR N * INR (i + 1) / INR (N + 1) +
               PI * INR (i + 1)) / 2 *
            / sin (PI * INR (i + 1) * / INR (N + 1)) = (sin
              (PI * INR N * INR (i + 1) / INR (N + 1) +
               PI * INR (i + 1))) * (/2) * (/ sin(PI * INR (i + 1) * / INR (N + 1)) )). { nra. } rewrite H21.
  assert (sin  (PI * INR N * INR (i + 1) / INR (N + 1) + PI * INR (i + 1)) *(/ 2) */ sin (PI * INR (i + 1) * / INR (N + 1))= sin
  (PI * INR N * INR (i + 1) / INR (N + 1) +
   PI * INR (i + 1)) */ (2 *  sin (PI * INR (i + 1) * / INR (N + 1)))). 
  { assert (sin
                (PI * INR N * INR (i + 1) / INR (N + 1) +
                 PI * INR (i + 1)) * / 2 *
              / sin (PI * INR (i + 1) * / INR (N + 1))= sin
                      (PI * INR N * INR (i + 1) / INR (N + 1) +
                       PI * INR (i + 1)) * (/ 2 *
                    / sin (PI * INR (i + 1) * / INR (N + 1)))). { nra. } rewrite H22.
  apply Rmult_eq_compat_l. symmetry. apply Rinv_mult_distr. nra.
  assert ( 0 < sin (PI * INR (i + 1) * / INR (N + 1)) -> sin (PI * INR (i + 1) * / INR (N + 1)) <> 0). { nra. } apply H23.
  apply sin_gt_0.
  assert (PI * INR (i + 1) * / INR (N + 1)= PI * (INR (i + 1) * / INR (N + 1))). { nra. } rewrite H24.
  apply Rmult_lt_0_compat. apply PI_RGT_0. 
  apply Rmult_lt_0_compat. apply lt_0_INR. omega. apply Rinv_0_lt_compat. apply lt_0_INR. omega. 
  assert (PI= PI * 1). { nra. } rewrite H24.
  assert (PI * 1 * INR (i + 1) * / INR (N + 1)= PI * (INR (i + 1) * / INR (N + 1))). { nra. } rewrite H25.
  apply Rmult_lt_compat_l. apply PI_RGT_0. 
  assert (1= INR (N+1) * (/ INR (N+1))). { apply Rinv_r_sym. assert ( 0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H26. apply lt_0_INR. omega. }
  rewrite H26. apply Rmult_lt_compat_r. apply Rinv_0_lt_compat. apply lt_0_INR. omega. apply lt_INR. omega.
} rewrite H22. nra.
} rewrite H18. 
assert ( -1 = -1/2 - 1/2). { nra. }rewrite H19.
apply Rplus_eq_compat_r.
assert (  sin (PI * INR N * INR (i + 1) / INR (N + 1) +  PI * INR (i + 1))= - sin (PI * INR (i + 1) * / INR (N + 1))).
{ assert (PI * INR N * INR (i + 1) / INR (N + 1) +   PI * INR (i + 1)=  2 * INR (i+1) * PI + - (PI * INR (i+1))/INR (N+1)).
  { assert (PI * INR (i + 1)= (PI * INR (i+1) * INR (N+1))/ INR (N+1)). 
    { assert (PI * INR (i + 1) * INR (N + 1) / INR (N + 1)=  PI * INR (i+1)* (INR (N+1) * (/ INR (N+1)))). { nra. } rewrite H20.
      assert ( 1=(INR (N + 1) * / INR (N + 1))). { apply Rinv_r_sym. assert ( 0 < INR (N + 1) -> INR (N + 1) <> 0). { nra. }apply H21. apply lt_0_INR. omega. } rewrite <-H21. nra.  
    } rewrite H20.  
    assert (PI * INR N * INR (i + 1) / INR (N + 1) + PI * INR (i + 1) * INR (N + 1) / INR (N + 1)=
              (PI * INR N * INR (i + 1) + PI * INR (i + 1) * INR (N + 1)) / INR (N+1)). { nra. } rewrite H21. rewrite <- H20.
    assert (2 * INR (i + 1) * PI= ( 2* INR (i+1) * PI * INR (N+1)) / INR (N+1)). 
    { assert (2 * INR (i + 1) * PI * INR (N + 1) / INR (N + 1)= 2 * INR(i+1) * PI * (INR (N+1) * (/ INR (N+1)))). { nra. } rewrite H22.
      assert (1= (INR (N+1) * (/ INR (N+1)))). { apply Rinv_r_sym. assert ( 0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H23. apply lt_0_INR. omega. }
      rewrite <- H23. nra.
    } rewrite H22. 
    assert (2 * INR (i + 1) * PI * INR (N + 1) / INR (N + 1) + - (PI * INR (i + 1)) / INR (N + 1)=
            (2 * INR (i + 1) * PI * INR (N + 1) + - (PI * INR (i + 1))) / INR (N+1)). { nra. }rewrite H23.
    assert ((PI * INR N * INR (i + 1) + PI * INR (i + 1) * INR (N + 1))= (2 * INR (i + 1) * PI * INR (N + 1) + - (PI * INR (i + 1)))).
    { assert ( INR (N+1) = INR N + INR 1). { apply plus_INR. } rewrite H24. assert (INR 1 =1). { reflexivity. }rewrite H25. nra. }
    rewrite H24. reflexivity.
  }
  rewrite H20.
  assert (sin  (2 * INR (i + 1) * PI + - (PI * INR (i + 1)) / INR (N + 1))= sin (- (PI * INR (i + 1)) / INR (N + 1))).
  { assert ( (2 * INR (i + 1) * PI + - (PI * INR (i + 1)) / INR (N + 1)) = - (PI * INR (i + 1)) / INR (N + 1) + 2 * INR (i + 1) * PI ). { nra. } rewrite H21.
    apply sin_period.
  } rewrite H21. assert ((- (PI * INR (i + 1)) / INR (N + 1))= - ((PI * INR (i + 1)) / INR (N + 1))). { nra. } rewrite H22. apply sin_neg. }
rewrite H20.
assert ( - sin (PI * INR (i + 1) * / INR (N + 1)) /(2 * sin (PI * INR (i + 1) * / INR (N + 1)))= 
        - sin (PI * INR (i + 1) * / INR (N + 1)) * (/(2 * sin (PI * INR (i + 1) * / INR (N + 1))))). { nra. } rewrite H21.
assert (/(2 * sin (PI * INR (i + 1) * / INR (N + 1)))= /2 * /sin (PI * INR (i + 1) * / INR (N + 1))).
{ apply Rinv_mult_distr. nra. 
  assert ( 0 < sin (PI * INR (i + 1) * / INR (N + 1)) -> sin (PI * INR (i + 1) * / INR (N + 1)) <> 0). { nra. } apply H22.
  apply sin_gt_0.
  assert (PI * INR (i + 1) * / INR (N + 1)= PI * (INR (i + 1) * / INR (N + 1))). { nra. } rewrite H23.
  apply Rmult_lt_0_compat. apply PI_RGT_0. 
  apply Rmult_lt_0_compat. apply lt_0_INR. omega. apply Rinv_0_lt_compat. apply lt_0_INR. omega. 
  assert (PI= PI * 1). { nra. } rewrite H23.
  assert (PI * 1 * INR (i + 1) * / INR (N + 1)= PI * (INR (i + 1) * / INR (N + 1))). { nra. } rewrite H24.
  apply Rmult_lt_compat_l. apply PI_RGT_0. 
  assert (1= INR (N+1) * (/ INR (N+1))). { apply Rinv_r_sym. assert ( 0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H25. apply lt_0_INR. omega. }
  rewrite H25. apply Rmult_lt_compat_r. apply Rinv_0_lt_compat. apply lt_0_INR. omega. apply lt_INR. omega.
}
rewrite H22. 
assert (- sin (PI * INR (i + 1) * / INR (N + 1)) *(/ 2 * / sin (PI * INR (i + 1) * / INR (N + 1)))=
        (-1) * (/2) * (/ sin (PI * INR (i + 1) * / INR (N + 1)) * sin (PI * INR (i + 1) * / INR (N + 1)))). { nra. }rewrite H23.
assert ((/ sin (PI * INR (i + 1) * / INR (N + 1)) * sin (PI * INR (i + 1) * / INR (N + 1)))=1).
{ symmetry. apply Rinv_l_sym. 
  assert ( 0 < sin (PI * INR (i + 1) * / INR (N + 1)) -> sin (PI * INR (i + 1) * / INR (N + 1)) <> 0). { nra. } apply H24.
  apply sin_gt_0.
  assert (PI * INR (i + 1) * / INR (N + 1)= PI * (INR (i + 1) * / INR (N + 1))). { nra. } rewrite H25.
  apply Rmult_lt_0_compat. apply PI_RGT_0. 
  apply Rmult_lt_0_compat. apply lt_0_INR. omega. apply Rinv_0_lt_compat. apply lt_0_INR. omega. 
  assert (PI= PI * 1). { nra. } rewrite H25.
  assert (PI * 1 * INR (i + 1) * / INR (N + 1)= PI * (INR (i + 1) * / INR (N + 1))). { nra. } rewrite H26.
  apply Rmult_lt_compat_l. apply PI_RGT_0. 
  assert (1= INR (N+1) * (/ INR (N+1))). { apply Rinv_r_sym. assert ( 0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H27. apply lt_0_INR. omega. }
  rewrite H27. apply Rmult_lt_compat_r. apply Rinv_0_lt_compat. apply lt_0_INR. omega. apply lt_INR. omega.
}
rewrite H24. nra.
Qed.

Lemma sinB2: forall(i j N:nat), (2<N)%nat /\ (0<=i<N)%nat /\ (0<=j<N)%nat /\ (i<>j) -> sin(INR(i+j+2)*PI*/ INR(N+1) /2) <> 0.
Proof.
     intros.
     remember (INR(i+j+2)*PI*/INR(N+1)) as b.
     assert(HBNeq : 0 < sin(b/2)). apply sin_gt_0. rewrite Heqb. apply Rmult_lt_0_compat. apply Rmult_lt_0_compat. apply Rmult_lt_0_compat. intuition. apply PI_RGT_0.
      - apply Rinv_0_lt_compat. apply lt_0_INR. omega.
      - nra.
      - rewrite Heqb. assert(INR (i + j + 2) * PI * / INR (N + 1) / 2 = PI * INR (i + j + 2) * / INR (N + 1) / 2). nra. rewrite H0.
        destruct H. destruct H1. destruct H2. apply (Rmult_gt_reg_l (INR(N+1)) (PI * INR (i + j + 2) * / INR (N + 1) / 2) (PI)).
        * apply lt_0_INR. omega. assert((INR (N + 1) * (PI * INR (i + j + 2) * / INR (N + 1) / 2)) = INR (N + 1) / INR(N+1) * (PI * INR (i + j + 2) * / 2)).
          { nra. } rewrite H4. assert(INR(N+1)/INR(N+1) = 1). { rewrite plus_INR. apply Rinv_r. assert(INR 1 = 1). { reflexivity. } assert(INR N + INR 1 > 0). { intuition. } nra. }
        * rewrite H5. assert(1 * (PI * INR (i + j + 2) * / 2) = (PI * INR (i + j + 2) * / 2)). { nra. } rewrite H6.
        * assert(INR (N + 1) * PI = PI * INR(N+1)). { nra. } rewrite H7. assert(PI > 0). { apply PI_RGT_0. } assert(PI * INR (i + j + 2) * / 2 = PI * (INR (i + j + 2) * / 2)). { nra. }
        * rewrite H9. apply (Rmult_lt_compat_l PI (INR(i+j+2)*/2) (INR(N+1))). apply H8.
        * destruct H1. destruct H2. apply lt_INR in H10. apply lt_INR in H11. assert((INR i + INR j) */ 2 < INR N). { nra. } rewrite plus_INR. rewrite plus_INR.
        * rewrite plus_INR. assert((INR i + INR j + INR 2) * / 2 = (INR i + INR j) */ 2 + INR 2 */ 2). { nra. } rewrite H13.
        * assert(INR 2 */ 2 = 1). { assert(INR 2 = 2). { reflexivity. } rewrite H14. nra. } rewrite H14.
        * assert(INR 1 = 1). { reflexivity. } rewrite H15. nra. nra.
Qed.

Lemma B2_gt_0: forall(i j N:nat), (2<N)%nat /\ (0<=i<N)%nat /\ (0<=j<N)%nat /\ (i<>j) -> (INR(i+j+2)*PI*/ INR(N+1) /2) > 0.
Proof.
     intros.
     remember (INR(i+j+2)*PI*/INR(N+1)) as b.
     rewrite Heqb. apply Rmult_lt_0_compat. apply Rmult_lt_0_compat. apply Rmult_lt_0_compat. intuition. apply PI_RGT_0.
      - apply Rinv_0_lt_compat. apply lt_0_INR. omega.
      - nra.
Qed.

Lemma sinA2: forall(i j N:nat), (2<N)%nat /\ (0<=i<N)%nat /\ (0<=j<N)%nat /\ (i<>j) -> sin((INR i - INR j)*PI/INR(N+1)/2) <> 0.
Proof.
  intros.
  remember ((INR i - INR j)*PI/INR(N+1)) as a.
  assert((i<j)%nat -> sin(a/2) < 0). intros. apply sin_lt_0_var. rewrite Heqa. assert(-PI = PI * -1). { nra. } rewrite H1.
      - assert((INR i - INR j) * PI / INR (N + 1) / 2 = PI * (INR i - INR j) / INR (N + 1) / 2). { nra. } rewrite H2.
      - assert(PI * (INR i - INR j) / INR (N + 1) / 2 = PI * ((INR i - INR j) / INR (N + 1) / 2)). { nra. } rewrite H3. apply (Rmult_lt_compat_l PI (-1) ((INR i - INR j) / INR (N + 1) / 2)).
      - apply PI_RGT_0. assert(INR i - INR j > -2 * INR(N+1)). apply lt_INR in H0. destruct H. destruct H4. destruct H5. destruct H4. destruct H5.
        * apply lt_INR in H7. apply lt_INR in H8. apply le_INR in H4. apply le_INR in H5. apply lt_INR in H. assert(INR 2 = 2). { reflexivity. } rewrite H9 in H.
      - rewrite plus_INR. assert(-2 * (INR N + INR 1) = -2 * INR N - 2 * INR 1). { nra. } rewrite H10. assert(INR 1 = 1). { reflexivity. } rewrite H11.
      - assert(-2 * INR N - 2 * 1 = -2 * INR N - 2). { nra. } rewrite H12. assert(INR i - INR j < 0). { nra. } assert(INR i - INR j < INR N). { nra. }
      - assert(-(INR i - INR j) < 2 * INR N). { assert(-(INR i - INR j) = - INR i + INR j). { nra. } rewrite H15. assert(INR 0 = 0). { reflexivity. } rewrite H16 in H4. rewrite H16 in H5. nra. }
      - assert(INR i - INR j > -2 * INR N). { nra. } nra.
  assert((INR i - INR j) / INR(N+1) / 2 = (INR i - INR j) / INR(N+1) * / 2). { nra. } rewrite H5.
      - assert((INR i - INR j) / INR (N + 1) */ 2 = (INR i - INR j) / (2*INR (N + 1))). { assert((INR i - INR j) / INR (N + 1) * / 2 = / INR (N + 1) * / 2 * (INR i - INR j)). { nra. } rewrite H6.
        rewrite <- Rinv_mult_distr. assert(/ (INR (N + 1) * 2) * (INR i - INR j) = (INR i - INR j) / (INR (N + 1) * 2)). { nra. } rewrite H7. assert(INR(N+1) * 2 = 2 * INR(N+1)). { nra. }
        rewrite H8. reflexivity. rewrite plus_INR. assert(INR 1 = 1). { reflexivity. } rewrite H7. assert(INR N + 1 > 0). { intuition. } nra. nra. }
      - rewrite H6. assert((INR i - INR j) / (2 * INR (N + 1)) = (INR i - INR j) */ (2 * INR (N + 1))). { nra. } rewrite H7.
      - apply (Rmult_gt_reg_l (2*INR(N+1)) (-1) ((INR i - INR j) */ (2 * INR(N + 1)))). rewrite plus_INR. assert(INR 1 = 1). { reflexivity. } rewrite H8.
        assert(2*(INR N + 1) = 2*INR N + 2). { nra. } rewrite H9. destruct H. apply lt_INR in H. assert(INR 2 = 2). { reflexivity. } rewrite H11 in H. nra.
      - assert(2 * INR (N + 1) * ((INR i - INR j) * / (2 * INR (N + 1))) = 2 * INR (N + 1) * (/ (2 * INR (N + 1)) * (INR i - INR j))). { nra. } rewrite H8.
        assert(2 * INR (N + 1) * (/ (2 * INR (N + 1)) * (INR i - INR j)) = (2*INR(N+1)) */ (2*INR(N+1)) * (INR i - INR j)). { nra. } rewrite H9.
        assert((2*INR(N+1)) */ (2*INR(N+1)) = 1). { intuition. } rewrite H10. assert(1*(INR i - INR j) = INR i - INR j). { nra. } rewrite H11.
        assert(2 * INR(N+1) * -1 = -2 * INR(N+1)). { nra. } rewrite H12. apply H4.
  rewrite Heqa. assert((INR i - INR j) * PI / INR (N + 1) / 2 = (INR i - INR j) * (PI / INR (N + 1) / 2)). { nra. } rewrite H1.
      - apply (Rmult_gt_reg_l (/(PI / INR(N+1) / 2)) ((INR i - INR j) * (PI / INR(N+1) /2)) 0).
        * assert(PI / INR(N+1) / 2 = PI */INR(N+1) */ 2). { nra. } rewrite H2. destruct H. apply lt_INR in H. rewrite plus_INR.
          assert((PI / (INR N + INR 1) * / 2) = PI / ((INR N + INR 1) * 2)). { assert(PI / (INR N + INR 1) * / 2 = / (INR N + INR 1) * / 2 * PI). { nra. } rewrite H4. rewrite <- Rinv_mult_distr. nra.
          assert(INR N + INR 1 > 0). { intuition. } nra. nra. }
      - assert(PI * / (INR N + INR 1) * / 2 = PI / (INR N + INR 1) * / 2). { nra. } rewrite H5. rewrite H4. assert(PI / ((INR N + INR 1) * 2) = PI */ ((INR N + INR 1) * 2)). { nra. } rewrite H6.
      - rewrite (Rinv_mult_distr (PI) (/((INR N + INR 1) * 2))). rewrite Rinv_involutive. assert(/PI * ((INR N + INR 1) * 2) = ((INR N + INR 1) * 2) / PI). { nra. } rewrite H7.
        assert(INR 1 = 1). { reflexivity. } rewrite H8. apply (Rmult_gt_reg_l (/(2/PI)) (0) ((INR N + 1) * 2 / PI)). { assert(/(2/PI) = /(2*/PI)). { nra. } rewrite H9.
        rewrite Rinv_mult_distr. rewrite Rinv_involutive. assert(/2 * PI = PI */ 2). { nra. } rewrite H10. apply (Rmult_gt_reg_l (2) (0) (PI */ 2)). nra.
        assert(2*(PI */ 2) = 2 */ 2 * PI). { nra. } rewrite H11. assert(2 */ 2 = 1). { nra. } rewrite H12. assert(2*0 = 0). { nra. } rewrite H13. assert(1*PI = PI). { nra. } rewrite H14.
        apply PI_RGT_0. assert(0 < PI). { apply PI_RGT_0. } nra. nra. assert(0 < /PI). { apply (Rmult_gt_reg_l (PI) (0) (/PI)). apply PI_RGT_0.  assert(PI */ PI = 1).
                                                                                         { assert(PI */ PI = PI / PI). { nra. } rewrite H10. apply Rinv_r. assert(PI > 0). { apply PI_RGT_0. } nra. }
                                                                                       rewrite H10. nra. } nra. }
        assert(/ (2 / PI) * ((INR N + 1) * 2 / PI) = (2/PI) / (2 / PI) * (INR N + 1)). { nra. } rewrite H9. assert(2 / PI / (2 / PI) = (2 / PI) */ (2 / PI)). { nra. } rewrite H10.
        assert(2 / PI * / (2 / PI) = 1). { apply Rinv_r. assert(/PI > 0). { apply Rinv_0_lt_compat. apply PI_RGT_0. } nra. } rewrite H11. assert(/(2/PI) * 0 = 0). { nra. } rewrite H12.
        assert(1 * (INR N + 1) = INR N + 1). { nra. } rewrite H13. intuition.
      - assert((INR N + INR 1) * 2 > 0). assert((INR N + INR 1) > 0). { intuition. } nra. nra.
      - assert(PI > 0). { apply PI_RGT_0. } nra.
      - assert(/ ((INR N + INR 1) * 2) > 0). { apply Rinv_0_lt_compat. assert(INR N + INR 1 > 0). { intuition. } nra. } nra.
      - assert(/ (PI / INR (N + 1) / 2) * 0 = 0). { nra. } rewrite H2. assert(/ (PI / INR (N + 1) / 2) * ((INR i - INR j) * (PI / INR (N + 1) / 2)) = (PI / INR (N + 1) / 2) / (PI / INR (N + 1) / 2) *
        ((INR i - INR j))). { nra. } rewrite H3. assert(PI / INR (N + 1) / 2 / (PI / INR (N + 1) / 2) = 1). { apply Rinv_r. assert(PI / INR (N + 1) / 2 = PI / INR (N + 1) */ 2). { nra. } rewrite H4.
        assert(PI / INR (N + 1) * / 2 = PI /(INR(N+1)*2)). assert(PI/(INR(N+1)*2) = /(INR(N+1)*2) * PI). { nra. } rewrite H5. rewrite (Rinv_mult_distr (INR(N+1)) (2)). nra.
        assert(INR(N+1) > 0). { intuition.  } nra. nra. rewrite H5. assert(/(INR(N+1)*2) > 0). { apply Rinv_0_lt_compat. assert(INR(N+1) > 0). { intuition. } nra. }
        assert(PI > 0). { apply PI_RGT_0. } assert(PI / (INR (N + 1) * 2) > 0). { nra. } nra. } rewrite H4.
      - assert(1 * (INR i - INR j) = INR i - INR j). { nra. } rewrite H5. apply lt_INR in H0. nra.
  assert((j<i)%nat -> sin(a/2) > 0). intros. apply sin_gt_0. rewrite Heqa. assert((INR i - INR j) * PI / INR (N + 1) / 2 = (INR i - INR j) * (PI / INR (N + 1) / 2)). { nra. } rewrite H2.
      - apply (Rmult_gt_reg_l (/(PI/INR(N+1)/2)) (0) ((INR i - INR j) * (PI / INR (N + 1) / 2))). assert(PI/INR(N+1)/2 = PI */INR(N+1)/2). { nra. } rewrite H3.
        assert(PI*/INR(N+1)/2 = PI*(/INR(N+1)/2)). { nra. } rewrite H4. rewrite (Rinv_mult_distr (PI) (/INR(N+1)/2)).
        assert(/(/INR(N+1)/2) = /(/INR(N+1) */ 2)). { nra. } rewrite H5. rewrite Rinv_mult_distr. rewrite Rinv_involutive. rewrite Rinv_involutive.
        assert(/PI > 0). { apply Rinv_0_lt_compat. apply PI_RGT_0. } assert(INR(N+1) > 0). { intuition. } nra. nra. assert(INR(N+1) > 0). { intuition. } nra.
        assert(/INR(N+1) > 0). { apply Rinv_0_lt_compat. intuition. } nra. nra. assert(PI > 0). { apply PI_RGT_0. } nra.
        assert(/INR(N+1) / 2 = /INR(N+1) * / 2). { nra. } rewrite H5. rewrite <- Rinv_mult_distr.
        assert((/(INR(N+1) * 2) > 0)). { apply Rinv_0_lt_compat. assert(INR(N+1) > 0). { intuition. } nra. } nra.
        assert(INR(N+1) > 0). { intuition. } nra. nra. assert(/ (PI / INR (N + 1) / 2) * 0 = 0). { nra. } rewrite H3.
        assert(/ (PI / INR (N + 1) / 2) *
  ((INR i - INR j) * (PI / INR (N + 1) / 2)) = ((PI / INR (N + 1) / 2)) / ((PI / INR (N + 1) / 2)) *
                                               ((INR i - INR j))). { nra. } rewrite H4. assert(PI / INR (N + 1) / 2 / (PI / INR (N + 1) / 2) = 1).
        { apply Rinv_r. assert(PI / INR (N + 1) / 2 > 0). assert(PI > 0). { apply PI_RGT_0. } assert(/INR(N+1) /2 > 0). { assert(/INR(N+1) /2 = /INR(N+1) */ 2). { nra. }
        rewrite H6. rewrite <- Rinv_mult_distr. apply Rinv_0_lt_compat. assert(INR(N+1) > 0). { intuition. } nra. assert(INR(N+1) > 0). { intuition. } nra. nra. } nra. nra. }
        rewrite H5. assert(1*(INR i - INR j) = INR i - INR j). { nra. } rewrite H6. apply lt_INR in H1. nra.
      - rewrite Heqa. assert(PI = PI * 1). { nra. } rewrite H2. assert((INR i - INR j) * (PI*1) / INR (N + 1) / 2 = PI * 1 * (INR i - INR j) / INR (N + 1) / 2). { nra. } rewrite H3.
        assert( PI * 1 * (INR i - INR j) / INR (N + 1) / 2 =  PI * (INR i - INR j) / INR (N + 1) / 2). { nra. } rewrite H4. apply (Rmult_gt_reg_l (/PI) (PI * (INR i - INR j) / INR (N + 1) / 2) (PI*1)).
        apply Rinv_0_lt_compat. apply PI_RGT_0. assert(/ PI * (PI * (INR i - INR j) / INR (N + 1) / 2) = PI / PI * ((INR i - INR j) / INR (N + 1) / 2)). { nra. } rewrite H5.
        assert(/PI * (PI * 1) = PI / PI * 1). { nra. } rewrite H6. assert(PI/PI = 1). { apply Rinv_r. assert(PI > 0). { apply PI_RGT_0. } nra. } rewrite H7.
        assert(1*1=1). {nra. } rewrite H8. assert( 1 * ((INR i - INR j) / INR (N + 1) / 2) =  ((INR i - INR j) / INR (N + 1) / 2)). {nra. } rewrite H9.
        assert((INR i - INR j) / INR (N + 1) / 2 = (INR i - INR j) / INR (N + 1) */ 2). {nra. } rewrite H10. assert((INR i - INR j) / INR (N + 1) * / 2 = / INR (N + 1) * / 2 * (INR i - INR j)).
        {nra. } rewrite H11. assert(/ INR (N + 1) * / 2 * (INR i - INR j) = /(INR (N + 1) * 2) * (INR i - INR j)). {rewrite <- Rinv_mult_distr. reflexivity. assert(INR(N+1) > 0). { intuition. } nra. nra. }
        rewrite H12. assert(/ (INR (N + 1) * 2) * (INR i - INR j) = (INR i - INR j) / (INR (N + 1) * 2)). {nra. } rewrite H13.
        assert(INR i - INR j < INR N). {destruct H. destruct H14. destruct H15. destruct H14. destruct H15. apply lt_INR in H17. apply lt_INR in H18. apply lt_INR in H1.
                                        apply le_INR in H14. apply le_INR in H15. apply (Rmult_gt_reg_l (/INR N) (INR i - INR j) (INR N)).
                                        - apply Rinv_0_lt_compat. apply lt_INR in H. assert(INR 2 = 2). {reflexivity. } rewrite H19 in H. nra.
                                        - assert(/INR N * INR N = INR N / INR N). {nra. } rewrite H19. assert(INR N / INR N = 1). {apply Rinv_r. assert(INR N > 0).
                                          {apply lt_INR in H. assert(INR 2 = 2). {reflexivity. } rewrite H20 in H. nra. }nra. } rewrite H20.
                                          rewrite Rmult_minus_distr_l.
                                        - assert(/ INR N * INR i < 1). {apply (Rmult_gt_reg_l (INR N) (/INR N * INR i) (1)). apply lt_INR in H. assert(INR 2 = 2). {reflexivity. }
                                          rewrite H21 in H. nra. assert(INR N * (/ INR N * INR i) = INR N */ INR N * INR i). {nra. } rewrite H21. assert(INR N */ INR N = 1). {nra. } rewrite H22. nra. }
                                        - assert(/INR N * INR j < 1). {apply (Rmult_gt_reg_l (INR N) (/INR N * INR j) (1)). apply lt_INR in H. assert(INR 2 = 2). {reflexivity. }
                                          rewrite H22 in H. nra. assert(INR N * (/ INR N * INR j) = INR N */ INR N * INR j). {nra. } rewrite H22. assert(INR N */ INR N = 1). {nra. } rewrite H23. nra. }
                                        - assert(0 < /INR N * INR i). {apply (Rmult_gt_reg_l (INR N) (0) (/INR N * INR i)). apply lt_INR in H. assert(INR 2 = 2). {reflexivity. }
                                          rewrite H23 in H. nra. assert(INR N * (/ INR N * INR i) = INR N */ INR N * INR i). {nra. } rewrite H23. assert(INR N */ INR N = 1). {nra. } rewrite H24.
                                          assert(INR N * 0 = 0). {nra. } rewrite H25. assert(1*INR i = INR i). {nra. } rewrite H26. assert(INR 0 = 0). {reflexivity. } nra. }
                                        - destruct H15. destruct H14. assert(INR 0 = 0). {reflexivity. } rewrite H24 in H14. rewrite H24 in H15. nra.
                                          * rewrite <- H14. assert(/INR N * INR 0 = INR 0). {nra. } rewrite H24. assert(INR 0 = 0). {reflexivity. } rewrite H25.
                                            assert(-/INR N * INR j < 0). {nra. } nra.
                                          * rewrite <- H15. assert(/INR N * INR 0 = INR 0). {intuition. } rewrite H24. assert(/INR N * INR i - INR 0 = /INR N * INR i). {intuition. } rewrite H25. apply H21. }
      - apply (Rmult_gt_reg_l (INR(N+1)*2) ((INR i - INR j) / (INR (N + 1) * 2)) (1)).
        * assert(INR(N+1) > 0). {intuition. } nra.
        * assert(INR (N + 1) * 2 * ((INR i - INR j) / (INR (N + 1) * 2)) = INR (N + 1) * 2 */ (INR (N + 1) * 2) * ((INR i - INR j))). {nra. } rewrite H15.
        * assert(INR (N + 1) * 2 * / (INR (N + 1) * 2) = 1). {apply Rinv_r. assert(INR(N+1) > 0). {intuition. } nra. } rewrite H16.
        * assert(1 * (INR i - INR j) = (INR i - INR j)). {nra. } rewrite H17. assert(INR(N+1) * 2 * 1 = INR(N+1) * 2). {nra. } rewrite H18. rewrite plus_INR.
        * assert((INR N + INR 1) * 2 = 2 * (INR N + INR 1)). {nra. } rewrite H19. assert(2*(INR N + INR 1) = 2*INR N + 2 * INR 1). {nra. } rewrite H20. assert(INR 1 = 1). {reflexivity. } rewrite H21.
        * assert(2*1 = 2). {nra. } rewrite H22. destruct H. destruct H23. destruct H24. destruct H23. destruct H24. apply lt_INR in H26. apply lt_INR in H27. apply le_INR in H23. apply le_INR in H24.
        * assert(2 * INR N = INR N * 2). {nra. } rewrite H28. assert(1*INR N < 2*INR N). {apply Rmult_lt_compat_r. apply lt_INR in H. assert(INR 2 = 2). {reflexivity. } rewrite H29 in H. nra. nra. } nra.
      - assert(i <> j -> (i<j)%nat \/ (j<i)%nat). {intros. omega. } assert(sin(a/2) < 0 \/ sin(a/2) > 0). {destruct H. destruct H3. destruct H4. apply H2 in H5. destruct H5. apply H0 in H5.
        left. apply H5. right. apply H1 in H5. apply H5. } nra.
Qed.

Lemma A2_lt_0: forall(i j N:nat), (2<N)%nat /\ (0<=i<N)%nat /\ (0<=j<N)%nat /\ (i<j)%nat -> ((INR i - INR j)*PI/INR(N+1)/2) < 0.
Proof.
  intros.
  remember ((INR i - INR j)*PI/INR(N+1)) as a.
  intros. rewrite Heqa. assert((INR i - INR j) * PI / INR (N + 1) / 2 = (INR i - INR j) * (PI / INR (N + 1) / 2)). { nra. } rewrite H0.
      - apply (Rmult_gt_reg_l (/(PI / INR(N+1) / 2)) ((INR i - INR j) * (PI / INR(N+1) /2)) 0).
        * assert(PI / INR(N+1) / 2 = PI */INR(N+1) */ 2). { nra. } rewrite H1. destruct H. apply lt_INR in H. rewrite plus_INR.
          assert((PI / (INR N + INR 1) * / 2) = PI / ((INR N + INR 1) * 2)). { assert(PI / (INR N + INR 1) * / 2 = / (INR N + INR 1) * / 2 * PI). { nra. } rewrite H3. rewrite <- Rinv_mult_distr. nra.
          assert(INR N + INR 1 > 0). { intuition. } nra. nra. }
      - assert(PI * / (INR N + INR 1) * / 2 = PI / (INR N + INR 1) * / 2). { nra. } rewrite H4. rewrite H3. assert(PI / ((INR N + INR 1) * 2) = PI */ ((INR N + INR 1) * 2)). { nra. } rewrite H5.
      - rewrite (Rinv_mult_distr (PI) (/((INR N + INR 1) * 2))). rewrite Rinv_involutive. assert(/PI * ((INR N + INR 1) * 2) = ((INR N + INR 1) * 2) / PI). { nra. } rewrite H6.
        assert(INR 1 = 1). { reflexivity. } rewrite H7. apply (Rmult_gt_reg_l (/(2/PI)) (0) ((INR N + 1) * 2 / PI)). { assert(/(2/PI) = /(2*/PI)). { nra. } rewrite H8.
        rewrite Rinv_mult_distr. rewrite Rinv_involutive. assert(/2 * PI = PI */ 2). { nra. } rewrite H9. apply (Rmult_gt_reg_l (2) (0) (PI */ 2)). nra.
        assert(2*(PI */ 2) = 2 */ 2 * PI). { nra. } rewrite H10. assert(2 */ 2 = 1). { nra. } rewrite H11. assert(2*0 = 0). { nra. } rewrite H12. assert(1*PI = PI). { nra. } rewrite H13.
        apply PI_RGT_0. assert(0 < PI). { apply PI_RGT_0. } nra. nra. assert(0 < /PI). { apply (Rmult_gt_reg_l (PI) (0) (/PI)). apply PI_RGT_0.  assert(PI */ PI = 1).
                                                                                         { assert(PI */ PI = PI / PI). { nra. } rewrite H9. apply Rinv_r. assert(PI > 0). { apply PI_RGT_0. } nra. }
                                                                                       rewrite H9. nra. } nra. }
        assert(/ (2 / PI) * ((INR N + 1) * 2 / PI) = (2/PI) / (2 / PI) * (INR N + 1)). { nra. } rewrite H8. assert(2 / PI / (2 / PI) = (2 / PI) */ (2 / PI)). { nra. } rewrite H9.
        assert(2 / PI * / (2 / PI) = 1). { apply Rinv_r. assert(/PI > 0). { apply Rinv_0_lt_compat. apply PI_RGT_0. } nra. } rewrite H10. assert(/(2/PI) * 0 = 0). { nra. } rewrite H11.
        assert(1 * (INR N + 1) = INR N + 1). { nra. } rewrite H12. intuition.
      - assert((INR N + INR 1) * 2 > 0). assert((INR N + INR 1) > 0). { intuition. } nra. nra.
      - assert(PI > 0). { apply PI_RGT_0. } nra.
      - assert(/ ((INR N + INR 1) * 2) > 0). { apply Rinv_0_lt_compat. assert(INR N + INR 1 > 0). { intuition. } nra. } nra.
      - assert(/ (PI / INR (N + 1) / 2) * 0 = 0). { nra. } rewrite H1. assert(/ (PI / INR (N + 1) / 2) * ((INR i - INR j) * (PI / INR (N + 1) / 2)) = (PI / INR (N + 1) / 2) / (PI / INR (N + 1) / 2) *
        ((INR i - INR j))). { nra. } rewrite H2. assert(PI / INR (N + 1) / 2 / (PI / INR (N + 1) / 2) = 1). { apply Rinv_r. assert(PI / INR (N + 1) / 2 = PI / INR (N + 1) */ 2). { nra. } rewrite H3.
        assert(PI / INR (N + 1) * / 2 = PI /(INR(N+1)*2)). assert(PI/(INR(N+1)*2) = /(INR(N+1)*2) * PI). { nra. } rewrite H4. rewrite (Rinv_mult_distr (INR(N+1)) (2)). nra.
        assert(INR(N+1) > 0). { intuition.  } nra. nra. rewrite H4. assert(/(INR(N+1)*2) > 0). { apply Rinv_0_lt_compat. assert(INR(N+1) > 0). { intuition. } nra. }
        assert(PI > 0). { apply PI_RGT_0. } assert(PI / (INR (N + 1) * 2) > 0). { nra. } nra. } rewrite H3.
      - assert(1 * (INR i - INR j) = INR i - INR j). { nra. } rewrite H4.
        destruct H. destruct H5. destruct H6. apply lt_INR in H7. nra.
Qed.

Lemma A2_gt_neg_PI: forall(i j N:nat), (2<N)%nat /\ (0<=i<N)%nat /\ (0<=j<N)%nat /\ (i<j)%nat -> ((INR i - INR j)*PI/INR(N+1)/2) > -PI.
Proof.
  intros.
  remember ((INR i - INR j)*PI/INR(N+1)) as a.
  assert((i<j)%nat -> a/2 > -PI). intros. rewrite Heqa. assert(-PI = PI * -1). { nra. } rewrite H1.
      - assert((INR i - INR j) * PI / INR (N + 1) / 2 = PI * (INR i - INR j) / INR (N + 1) / 2). { nra. } rewrite H2.
      - assert(PI * (INR i - INR j) / INR (N + 1) / 2 = PI * ((INR i - INR j) / INR (N + 1) / 2)). { nra. } rewrite H3. apply (Rmult_lt_compat_l PI (-1) ((INR i - INR j) / INR (N + 1) / 2)).
      - apply PI_RGT_0. assert(INR i - INR j > -2 * INR(N+1)). apply lt_INR in H0. destruct H. destruct H4. destruct H5. destruct H4. destruct H5.
        * apply lt_INR in H7. apply lt_INR in H8. apply le_INR in H4. apply le_INR in H5. apply lt_INR in H. assert(INR 2 = 2). { reflexivity. } rewrite H9 in H.
      - rewrite plus_INR. assert(-2 * (INR N + INR 1) = -2 * INR N - 2 * INR 1). { nra. } rewrite H10. assert(INR 1 = 1). { reflexivity. } rewrite H11.
      - assert(-2 * INR N - 2 * 1 = -2 * INR N - 2). { nra. } rewrite H12. assert(INR i - INR j < 0). { nra. } assert(INR i - INR j < INR N). { nra. }
      - assert(-(INR i - INR j) < 2 * INR N). { assert(-(INR i - INR j) = - INR i + INR j). { nra. } rewrite H15. assert(INR 0 = 0). { reflexivity. } rewrite H16 in H4. rewrite H16 in H5. nra. }
      - assert(INR i - INR j > -2 * INR N). { nra. } nra.
  assert((INR i - INR j) / INR(N+1) / 2 = (INR i - INR j) / INR(N+1) * / 2). { nra. } rewrite H5.
      - assert((INR i - INR j) / INR (N + 1) */ 2 = (INR i - INR j) / (2*INR (N + 1))). { assert((INR i - INR j) / INR (N + 1) * / 2 = / INR (N + 1) * / 2 * (INR i - INR j)). { nra. } rewrite H6.
        rewrite <- Rinv_mult_distr. assert(/ (INR (N + 1) * 2) * (INR i - INR j) = (INR i - INR j) / (INR (N + 1) * 2)). { nra. } rewrite H7. assert(INR(N+1) * 2 = 2 * INR(N+1)). { nra. }
        rewrite H8. reflexivity. rewrite plus_INR. assert(INR 1 = 1). { reflexivity. } rewrite H7. assert(INR N + 1 > 0). { intuition. } nra. nra. }
      - rewrite H6. assert((INR i - INR j) / (2 * INR (N + 1)) = (INR i - INR j) */ (2 * INR (N + 1))). { nra. } rewrite H7.
      - apply (Rmult_gt_reg_l (2*INR(N+1)) (-1) ((INR i - INR j) */ (2 * INR(N + 1)))). rewrite plus_INR. assert(INR 1 = 1). { reflexivity. } rewrite H8.
        assert(2*(INR N + 1) = 2*INR N + 2). { nra. } rewrite H9. destruct H. apply lt_INR in H. assert(INR 2 = 2). { reflexivity. } rewrite H11 in H. nra.
      - assert(2 * INR (N + 1) * ((INR i - INR j) * / (2 * INR (N + 1))) = 2 * INR (N + 1) * (/ (2 * INR (N + 1)) * (INR i - INR j))). { nra. } rewrite H8.
        assert(2 * INR (N + 1) * (/ (2 * INR (N + 1)) * (INR i - INR j)) = (2*INR(N+1)) */ (2*INR(N+1)) * (INR i - INR j)). { nra. } rewrite H9.
        assert((2*INR(N+1)) */ (2*INR(N+1)) = 1). { intuition. } rewrite H10. assert(1*(INR i - INR j) = INR i - INR j). { nra. } rewrite H11.
        assert(2 * INR(N+1) * -1 = -2 * INR(N+1)). { nra. } rewrite H12. apply H4.
        destruct H. destruct H1. destruct H2. apply H0 in H3. apply H3.
Qed.


Require Import Coq.Reals.Rdefinitions.
Lemma cos_sqr_sum: forall (i j N:nat), (2<N)%nat /\ (0<=i<N)%nat /\ (0<=j<N)%nat /\ (i<>j) -> sum_n_m (fun l:nat =>
                                                                                                       mult(/INR(N+1))(cos((INR(i) - INR(j)) * PI / INR (N + 1) + INR l * (INR(i) - INR(j)) * PI / INR (N + 1)) -
                                                                                                                    cos(INR(i+j+2)*PI */ INR(N+1) + INR l * INR(i+j+2)*PI */ INR(N+1)))) 0 (pred N)=0.
Proof.
  intros.
  assert(forall A B, A + B = plus A B). { reflexivity. }
  - rewrite sum_n_m_mult_l. assert(Hmult:forall A B, A * B = mult A B). {reflexivity. } rewrite <- Hmult.
  - apply Rmult_eq_0_compat_l.
  - assert((fun k : nat =>
     (cos ((INR i - INR j) * PI / INR (N + 1) + INR k * (INR i - INR j) * PI / INR (N + 1)) -
     cos (INR (i + j + 2) * PI * / INR (N + 1) + INR k * INR (i + j + 2) * PI * / INR (N + 1)))) =
          (fun k : nat =>
     (cos ((INR i - INR j) * PI / INR (N + 1) + INR k * (INR i - INR j) * PI / INR (N + 1)) +
     (-(cos (INR (i + j + 2) * PI * / INR (N + 1) + INR k * INR (i + j + 2) * PI * / INR (N + 1))))))).
    { intuition. } rewrite H1.
    assert(HZZ : sum_n_m
    (fun l : nat =>
     (cos ((INR i - INR j) * PI / INR (N + 1) + INR l * (INR i - INR j) * PI / INR (N + 1)) +
     - cos (INR (i + j + 2) * PI * / INR (N + 1) + INR l * INR (i + j + 2) * PI * / INR (N + 1)))) 0
    (pred N) =  sum_n_m
    (fun l : nat =>
     (cos ((INR i - INR j) * PI / INR (N + 1) + INR l * (INR i - INR j) * PI / INR (N + 1))) +
     (- cos (INR (i + j + 2) * PI * / INR (N + 1) + INR l * INR (i + j + 2) * PI * / INR (N + 1)))) 0
    (pred N)). {apply sum_n_m_ext_loc. intros. nra. }
    assert(sum_n_m
    (fun k : nat =>
     cos ((INR i - INR j) * PI / INR (N + 1) + INR k * (INR i - INR j) * PI / INR (N + 1)) +
     (- cos (INR (i + j + 2) * PI * / INR (N + 1) + INR k * INR (i + j + 2) * PI * / INR (N + 1)))) 0
    (pred N) = sum_n_m
    (fun k : nat =>
     plus (cos ((INR i - INR j) * PI / INR (N + 1) + INR k * (INR i - INR j) * PI / INR (N + 1)))
     (- cos (INR (i + j + 2) * PI * / INR (N + 1) + INR k * INR (i + j + 2) * PI * / INR (N + 1)))) 0
    (pred N)).
    { intros. apply sum_n_m_ext_loc. intros. reflexivity. }
    assert(Hizzy:@eq R
        (@sum_n_m (Ring.AbelianGroup R_Ring)
        (fun k : nat =>
            Rplus
            (cos
                (Rplus (Rdiv (Rmult (Rminus (INR i) (INR j)) PI) (INR (add N (S O))))
                    (Rdiv (Rmult (Rmult (INR k) (Rminus (INR i) (INR j))) PI) (INR (add N (S O))))))
            (Ropp
                (cos
                    (Rplus (Rmult (Rmult (INR (add (add i j) (S (S O)))) PI) (Rinv (INR (add N (S O)))))
                    (Rmult (Rmult (Rmult (INR k) (INR (add (add i j) (S (S O))))) PI) (Rinv (INR (add N (S O)))))))))
        O (pred N)) (@sum_n_m R_AbelianGroup
                (fun k : nat =>
                Rplus
                (cos
                    (Rplus (Rdiv (Rmult (Rminus (INR i) (INR j)) PI) (INR (add N (S O))))
                        (Rdiv (Rmult (Rmult (INR k) (Rminus (INR i) (INR j))) PI) (INR (add N (S O))))))
                (Ropp
                    (cos
                        (Rplus (Rmult (Rmult (INR (add (add i j) (S (S O)))) PI) (Rinv (INR (add N (S O)))))
                            (Rmult (Rmult (Rmult (INR k) (INR (add (add i j) (S (S O))))) PI)
                            (Rinv (INR (add N (S O))))))))) O (pred N))). {intuition. } rewrite Hizzy.
    rewrite H2.
    assert(sum_n_m
    (fun l : nat => plus
       (
        cos
          ((INR i - INR j) * PI / INR (N + 1) +
           INR l * (INR i - INR j) * PI / INR (N + 1)))
       (
        -
        cos
          (INR (i + j + 2) * PI * / INR (N + 1) +
           INR l * INR (i + j + 2) * PI * / INR (N + 1))))
    0 (pred N) =
     plus (sum_n_m (fun l : nat => cos ((INR i - INR j) * PI / INR (N + 1) + INR l * (INR i - INR j) * PI / INR (N + 1))) 0 (pred N))
       (sum_n_m (fun l : nat => - cos (INR (i + j + 2) * PI * / INR (N + 1) + INR l * INR (i + j + 2) * PI * / INR (N + 1))) 0 (pred N))).
    { apply sum_n_m_plus. } rewrite H3.
    assert(sum_n_m
       (fun l : nat =>
        cos
          ((INR i - INR j) * PI / INR (N + 1) +
           INR l * (INR i - INR j) * PI / INR (N + 1)))
       0 (pred N) = sum_n_m
       (fun l : nat =>
        cos
          ((INR i - INR j) * PI / INR (N + 1) +
           (INR i - INR j) * PI / INR (N + 1) * INR l))
       0 (pred N)). { apply sum_n_m_ext_loc. intros. rewrite (Rmult_comm ((INR i - INR j) * PI / INR (N + 1)) (INR k)). simpl.
                    assert(INR k * (INR i - INR j) * PI / INR (N + 1) = INR k * ((INR i - INR j) * PI / INR (N + 1))). { nra. } rewrite H5. reflexivity. } rewrite H4.
    remember ((INR i - INR j) * PI / INR (N + 1)) as a.
    assert(sum_n_m (fun l : nat => cos (a + INR l * a)) 0 (pred N) =
          sin(INR N*a/2)*cos(a+INR(N-1)*a/2)*/sin(a/2)).
    { apply cos_series_sum. rewrite Heqa. assert((INR i - INR j) <> 0). { destruct H. destruct H5. destruct H6.
                                                                          assert(INR i <> INR j). { apply not_INR. apply H7. } nra. }
                                                                        assert(PI/INR(N+1) <> 0). { assert(PI/INR(N+1) = PI*/INR(N+1)). { nra. } rewrite H6.
                                                                                                    assert(0 < PI*/INR(N+1)). assert(0=PI*0). { nra. } rewrite H7.
                                                                                                    assert(PI>0). { apply PI_RGT_0. } assert(0</INR(N+1)). { apply Rinv_0_lt_compat. apply lt_0_INR. omega. }
                                                                                                                                                           apply Rmult_lt_compat_l. apply H8. apply H9. nra. } nra. }
    assert(sum_n_m (fun l : nat => cos (a + a * INR l)) 0
       (pred N) = sum_n_m (fun l : nat => cos (a + INR l * a)) 0
       (pred N)). { apply sum_n_m_ext_loc. intros. intuition. } rewrite H6. rewrite H5.
    assert(sum_n_m
       (fun l : nat =>
        -
        cos
          (INR (i + j + 2) * PI * / INR (N + 1) +
           INR l * INR (i + j + 2) * PI *
           / INR (N + 1))) 0 (pred N) = sum_n_m
       (fun l : nat =>
        -
        cos
          (INR (i + j + 2) * PI * / INR (N + 1) +
           INR (i + j + 2) * PI *
           / INR (N + 1) * INR l)) 0 (pred N)).
    { apply sum_n_m_ext_loc. intros. rewrite (Rmult_comm (INR(i+j+2)*PI*/INR(N+1)) (INR(k))).
      assert(INR (i + j + 2) * PI * / INR (N + 1) +
             INR k * INR (i + j + 2) * PI * / INR (N + 1) =
    (INR (i + j + 2) * PI * / INR (N + 1) +
     INR k * (INR (i + j + 2) * PI * / INR (N + 1)))). { nra. } rewrite H8. reflexivity. } rewrite H7.
    remember(INR (i + j + 2) * PI * / INR (N + 1)) as b.
    assert(sum_n_m (fun l : nat => - cos (b + b * INR l)) 0
       (pred N) = - sin(INR N*b/2)*cos(b+INR(N-1)*b/2)*/sin(b/2)).
    { assert(sum_n_m (fun l : nat => - cos (b + b * INR l)) 0
       (pred N) = sum_n_m (fun l : nat => - cos (b + INR l * b)) 0
                          (pred N)). { apply sum_n_m_ext_loc. intros. intuition. } rewrite H8.
      apply cos_series_sum_neg. rewrite Heqb.
      assert(INR(i+j+2) <> 0). assert(INR(i+j+2) > 0). { intuition. } nra. assert(PI*/INR(N+1) <> 0). { assert(PI*/INR(N+1) > 0). assert(0=PI*0). { nra. } rewrite H10.
      assert(PI>0). { apply PI_RGT_0. } assert(/INR(N+1) > 0). { apply Rinv_0_lt_compat. apply lt_0_INR. omega. } apply Rmult_lt_compat_l. apply H11. apply H12. nra. } nra. } rewrite H8.
   assert(sin (INR N * a / 2) *
     cos (a + INR (N - 1) * a / 2) *
     / sin (a / 2) = (sin (INR N * a / 2) */ sin(a/2)) *
     cos (a + INR (N - 1) * a / 2)). { nra. } rewrite H9.
   assert(-sin (INR N * b / 2) *
     cos (b + INR (N - 1) * b / 2) *
     / sin (b / 2) = -(sin (INR N * b / 2) */ sin(b/2)) *
     cos (b + INR (N - 1) * b / 2)). { nra. } rewrite H10.
   rewrite <- H0.
   assert(sin (INR N * a / 2) * / sin (a / 2) *
  cos (a + INR (N - 1) * a / 2) +
  - (sin (INR N * b / 2) * / sin (b / 2)) *
  cos (b + INR (N - 1) * b / 2) = sin (INR N * a / 2) * / sin (a / 2) *
  cos (a + INR (N - 1) * a / 2) - (sin (INR N * b / 2) * / sin (b / 2)) *
  cos (b + INR (N - 1) * b / 2)). { nra. } rewrite H11.
  assert(sin (INR N * a / 2) * / sin (a / 2) * cos (a + INR (N - 1) * a / 2) -
  sin (INR N * b / 2) * / sin (b / 2) * cos (b + INR (N - 1) * b / 2) = sin (INR N * a / 2) * sin(b/2) * / (sin (a / 2) * sin(b/2)) * cos (a + INR (N - 1) * a / 2) -
  sin (INR N * b / 2) * sin(a/2) * / (sin(a/2) * sin (b / 2)) * cos (b + INR (N - 1) * b / 2)).
  { assert(sin (INR N * a / 2) * sin (b / 2) * / (sin (a / 2) * sin (b / 2)) = sin (INR N * a / 2) * / sin (a / 2)).
    { rewrite Rinv_mult_distr. assert(sin(INR N * a / 2) * sin (b / 2) * (/ sin (a / 2) * / sin (b / 2)) = sin(INR N * a / 2) * sin (b / 2) * / sin (b / 2) * / sin(a / 2)). { nra. } rewrite H12.
      assert(sin (INR N * a / 2) * sin (b / 2) * / sin (b / 2) * / sin (a / 2) = sin(b/2) */ sin(b/2) * sin (INR N * a / 2) * / sin (a / 2)). { nra. } rewrite H13. rewrite Rinv_r. nra.
      (* sin(b/2) <> 0 **)
      rewrite Heqb. apply sinB2. apply H.
      (* sin(a/2) <> 0 **)
      rewrite Heqa. apply sinA2. apply H.
      (* sin(b/2) <> 0 **)
      rewrite Heqb. apply sinB2. apply H. } rewrite <- H12.
    assert(sin (INR N * b / 2) * / sin (b / 2) = sin(a / 2) * sin (INR N * b / 2) * / (sin (a / 2) * sin (b / 2))). {
    rewrite Rinv_mult_distr. assert(sin (a / 2) * sin (INR N * b / 2) *
  (/ sin (a / 2) * / sin (b / 2)) = sin (a / 2) */ sin(a / 2) * sin (INR N * b / 2) *
  (/ sin (b / 2))). { nra. } rewrite H13. rewrite Rinv_r. nra.
    rewrite Heqa. apply sinA2. apply H.
    rewrite Heqa. apply sinA2. apply H.
    rewrite Heqb. apply sinB2. apply H.
  } rewrite H13. nra. } rewrite H12. assert(sin (INR N * a / 2) * sin (b / 2) *
  / (sin (a / 2) * sin (b / 2)) *
  cos (a + INR (N - 1) * a / 2) -
  sin (INR N * b / 2) * sin (a / 2) *
  / (sin (a / 2) * sin (b / 2)) *
  cos (b + INR (N - 1) * b / 2) = / (sin (a / 2) * sin (b / 2)) * (sin (INR N * a / 2) * sin (b / 2) *
  cos (a + INR (N - 1) * a / 2) -
  sin (INR N * b / 2) * sin (a / 2) *
  cos (b + INR (N - 1) * b / 2))). { nra. } rewrite H13.
  assert((sin (INR N * a / 2) * sin (b / 2) *
   cos (a + INR (N - 1) * a / 2) -
   sin (INR N * b / 2) * sin (a / 2) *
   cos (b + INR (N - 1) * b / 2)) = 0).

     remember (INR N * a / 2)  as X.
     remember (b / 2) as Y.
     remember (a + INR(N-1) * a / 2) as B.
     assert(1 * sin X * sin Y = 1/2 * (cos(X-Y) - cos(X+Y))). {apply sinA_sinB. } assert(1 * sin X * sin Y = sin X * sin Y). {nra. } rewrite <- H15. rewrite H14.
     assert(1 / 2 * (cos (X - Y) - cos (X + Y)) * cos B = 1 / 2 * cos (X - Y) * cos B - 1 / 2 * cos (X + Y) * cos B). {nra. } rewrite H16.
     remember (X-Y) as A1.
     remember (X+Y) as A2.
     assert(1/2 * cos A1 * cos B = 1 / 4 * (cos(A1-B) + cos(A1+B))). {assert(1/2 * cos A1 * cos B = cos A1 * cos B * 1/2). {nra. } rewrite H17. rewrite cosA_cosB. nra. } rewrite H17.
     assert(1/2 * cos A2 * cos B = 1 / 4 * (cos(A2-B) + cos(A2+B))). {assert(1/2 * cos A2 * cos B = cos A2 * cos B * 1/2). {nra. } rewrite H18. rewrite cosA_cosB. nra. } rewrite H18.

     remember (INR N * b / 2) as X1.
     remember (a/2) as Y1.
     assert(1 * sin X1 * sin Y1 = 1/2 * (cos(X1-Y1) - cos(X1+Y1))). {apply sinA_sinB. } assert(1 * sin X1 * sin Y1 = sin X1 * sin Y1). {nra. } rewrite <- H20. rewrite H20.
     remember (b + INR (N - 1) * b / 2) as Z1.
     assert(1 * sin X1 * sin Y1 = 1/2 * (cos(X1-Y1) - cos(X1+Y1))). {apply sinA_sinB. } assert(1 * sin X1 * sin Y1 = sin X1 * sin Y1). {nra. } rewrite <- H22. rewrite H19.
     assert(1 / 2 * (cos (X1 - Y1) - cos (X1 + Y1)) * cos Z1 = 1 / 2 * cos (X1 - Y1) * cos Z1 - 1 / 2 * cos (X1 + Y1) * cos Z1). {nra. } rewrite H23.
     assert(1 / 2 * cos (X1 - Y1) * cos Z1 = 1 / 4 * (cos((X1-Y1)-Z1) + cos((X1-Y1)+Z1))). {assert(1/2 * cos (X1-Y1) * cos (Z1) = cos (X1-Y1) * cos (Z1) * 1/2). {nra. } rewrite H24. rewrite cosA_cosB. nra. } rewrite H24.
     assert(1 / 2 * cos (X1 + Y1) * cos Z1 = 1 / 4 * (cos((X1+Y1)-Z1) + cos((X1+Y1)+Z1))). {assert(1/2 * cos (X1+Y1) * cos (Z1) = cos (X1+Y1) * cos (Z1) * 1/2). {nra. } rewrite H25. rewrite cosA_cosB. nra. } rewrite H25.
     assert(((cos (A1 - B) + cos (A1 + B)) -
  (cos (A2 - B) + cos (A2 + B)) -
  ((cos (X1 - Y1 - Z1) + cos (X1 - Y1 + Z1)) -
   (cos (X1 + Y1 - Z1) + cos (X1 + Y1 + Z1))) = 0) -> (1 / 4 * (cos (A1 - B) + cos (A1 + B)) -
  1 / 4 * (cos (A2 - B) + cos (A2 + B)) -
  (1 / 4 * (cos (X1 - Y1 - Z1) + cos (X1 - Y1 + Z1)) -
   1 / 4 * (cos (X1 + Y1 - Z1) + cos (X1 + Y1 + Z1))) = 0)). {nra. } rewrite H26. nra.
     rewrite HeqA1. rewrite HeqA2. rewrite HeqB. rewrite HeqX1. rewrite HeqY1. rewrite HeqZ1. rewrite HeqX. rewrite HeqY.
     assert(Hai : a + INR(N-1) * a/2 = a/2 + INR N * a/2). rewrite minus_INR. assert((INR N - INR 1) * a / 2 = INR N * a / 2 - INR 1 * a / 2). nra. rewrite H27.
     assert(INR 1 = 1). reflexivity. rewrite H28. assert(a + (INR N * a / 2 - 1 * a / 2) = a - 1 * a / 2 + INR N * a / 2). nra. rewrite H29.
     assert(a - 1 * a / 2 = a - a / 2). nra. rewrite H30. assert(a - a/2 = a/2). nra. rewrite H31. reflexivity. omega. rewrite Hai.
     assert(Hbi : b + INR(N-1) * b/2 = b/2 + INR N * b/2). rewrite minus_INR. assert((INR N - INR 1) * b / 2 = INR N * b / 2 - INR 1 * b / 2). nra. rewrite H27.
     assert(INR 1 = 1). reflexivity. rewrite H28. assert(b + (INR N * b / 2 - 1 * b / 2) = b - 1 * b / 2 + INR N * b / 2). nra. rewrite H29.
     assert(b - 1 * b / 2 = b - b / 2). nra. rewrite H30. assert(b - b/2 = b/2). nra. rewrite H31. reflexivity. omega. rewrite Hbi.
     assert(INR N * a / 2 - b / 2 - (a / 2 + INR N * a / 2) = -b / 2 - a / 2). {nra. } rewrite H27.
     assert(INR N * a / 2 - b / 2 + (a / 2 + INR N * a / 2) = INR N * a - b / 2 + a / 2). {nra. } rewrite H28.
     assert(INR N * a / 2 + b / 2 - (a / 2 + INR N * a / 2) = b / 2 - a / 2). {nra. } rewrite H29.
     assert(INR N * a / 2 + b / 2 + (a / 2 + INR N * a / 2) = INR N * a + b / 2 + a / 2). {nra. } rewrite H30.
     assert(INR N * b / 2 - a / 2 - (b / 2 + INR N * b / 2) = - a / 2 - b / 2). {nra. } rewrite H31.
     assert(INR N * b / 2 - a / 2 + (b / 2 + INR N * b / 2) = INR N * b - a / 2 + b / 2). {nra. } rewrite H32.
     assert(INR N * b / 2 + a / 2 - (b / 2 + INR N * b / 2) = a / 2 - b / 2). {nra. } rewrite H33.
     assert(INR N * b / 2 + a / 2 + (b / 2 + INR N * b / 2) = INR N * b + a / 2 + b / 2). {nra. } rewrite H34.
     assert(cos(a/2 - b/2) = cos(b/2 - a/2)). {assert(b/2 - a/2 = -(a/2 - b/2)). {nra. } rewrite H35. rewrite cos_neg. reflexivity. } rewrite H35.
     assert(-b/2 - a/2 = -a/2 - b/2). {nra. } rewrite H36.
     assert(cos (- a / 2 - b / 2) + cos (INR N * a - b / 2 + a / 2) -
  (cos (b / 2 - a / 2) + cos (INR N * a + b / 2 + a / 2)) -
  (cos (- a / 2 - b / 2) + cos (INR N * b - a / 2 + b / 2) -
   (cos (b / 2 - a / 2) + cos (INR N * b + a / 2 + b / 2))) = cos (- a / 2 - b / 2) + cos (INR N * a - b / 2 + a / 2) -
  cos (b / 2 - a / 2) - cos (INR N * a + b / 2 + a / 2) -
  (cos (- a / 2 - b / 2) + cos (INR N * b - a / 2 + b / 2) -
   (cos (b / 2 - a / 2) + cos (INR N * b + a / 2 + b / 2)))). {nra. } rewrite H37.
     assert(cos (- a / 2 - b / 2) + cos (INR N * a - b / 2 + a / 2) -
  cos (b / 2 - a / 2) - cos (INR N * a + b / 2 + a / 2) -
  (cos (- a / 2 - b / 2) + cos (INR N * b - a / 2 + b / 2) -
   (cos (b / 2 - a / 2) + cos (INR N * b + a / 2 + b / 2))) = cos (- a / 2 - b / 2) + cos (INR N * a - b / 2 + a / 2) -
  cos (b / 2 - a / 2) - cos (INR N * a + b / 2 + a / 2) -
  (cos (- a / 2 - b / 2) + cos (INR N * b - a / 2 + b / 2) -
   cos (b / 2 - a / 2) - cos (INR N * b + a / 2 + b / 2))). {nra. } rewrite H38.
     assert(cos (- a / 2 - b / 2) + cos (INR N * a - b / 2 + a / 2) -
  cos (b / 2 - a / 2) - cos (INR N * a + b / 2 + a / 2) -
  (cos (- a / 2 - b / 2) + cos (INR N * b - a / 2 + b / 2) -
   cos (b / 2 - a / 2) - cos (INR N * b + a / 2 + b / 2)) = cos (- a / 2 - b / 2) + cos (INR N * a - b / 2 + a / 2) -
  cos (b / 2 - a / 2) - cos (INR N * a + b / 2 + a / 2) -
  cos (- a / 2 - b / 2) - cos (INR N * b - a / 2 + b / 2) +
   cos (b / 2 - a / 2) + cos (INR N * b + a / 2 + b / 2)). {nra. } rewrite H39.
     assert(cos (- a / 2 - b / 2) + cos (INR N * a - b / 2 + a / 2) -
  cos (b / 2 - a / 2) - cos (INR N * a + b / 2 + a / 2) -
  cos (- a / 2 - b / 2) - cos (INR N * b - a / 2 + b / 2) +
  cos (b / 2 - a / 2) + cos (INR N * b + a / 2 + b / 2) = cos (INR N * a - b / 2 + a / 2) -
  cos (INR N * a + b / 2 + a / 2) - cos (INR N * b - a / 2 + b / 2) +
  cos (INR N * b + a / 2 + b / 2)). {nra. } rewrite H40.
     assert(2 */ 2 * (cos (INR N * a + a/2 - b / 2) - cos (INR N * a + a/2 + b / 2)) = 2 * sin(INR N * a + a/2) * sin(b/2)). {rewrite <- (sinA_sinB (2) (INR N * a + a/2) (b/2)). reflexivity. }
     assert(cos (INR N * a - b / 2 + a / 2) - cos (INR N * a + b / 2 + a / 2) = 2 */ 2 * (cos (INR N * a - b / 2 + a / 2) - cos (INR N * a + b / 2 + a / 2))). {nra. } rewrite H42.
     assert(INR N * a - b/2 + a/2 = INR N * a + a/2 - b/2). {nra. } rewrite H43.
     assert(INR N * a + b/2 + a/2 = INR N * a + a/2 + b/2). {nra. } rewrite H44.
     rewrite H41.

     assert(2 * sin (INR N * a + a / 2) * sin (b / 2) -
  cos (INR N * b - a / 2 + b / 2) + cos (INR N * b + a / 2 + b / 2) = 2 * sin (INR N * a + a / 2) * sin (b / 2) +
  ( cos (INR N * b + a / 2 + b / 2) - cos (INR N * b - a / 2 + b / 2))). {nra. } rewrite H45.
     assert(cos(INR N * b + a / 2 + b / 2) = cos(-(INR N * b + a / 2 + b / 2))). {rewrite cos_neg. reflexivity. } rewrite H46.
     assert(-(INR N * b + a / 2 + b / 2) = -INR N * b - a / 2 - b / 2). {nra. } rewrite H47.
     assert(cos (INR N * b - a / 2 + b / 2) = cos (-(INR N * b - a / 2 + b / 2))). {rewrite cos_neg. reflexivity. } rewrite H48.
     assert(- (INR N * b - a / 2 + b / 2) = - INR N * b + a / 2 - b / 2). {nra. } rewrite H49.
     assert(2 */ 2  * (cos (- INR N * b - a / 2 - b / 2) - cos (- INR N * b + a / 2 - b / 2)) = 2 * sin(-INR N * b - b/2) * sin(a/2)). {assert(-INR N * b - a/2 - b/2 = -INR N * b - b/2 - a/2). {nra. } rewrite H50.
                                                                                                                         assert(-INR N * b + a/2 - b/2 = -INR N * b - b/2 + a/2). {nra. } rewrite H51.
                                                                                                                         rewrite <- (sinA_sinB (2) (-INR N * b - b/2) (a/2)). reflexivity. }
    assert(cos (- INR N * b - a / 2 - b / 2) - cos (- INR N * b + a / 2 - b / 2) = 2 */ 2 * (cos (- INR N * b - a / 2 - b / 2) - cos (- INR N * b + a / 2 - b / 2))). {nra. } rewrite H51. rewrite H50.
    assert(sin(-INR N * b - b /2) = - sin(INR N * b + b/2)). {assert(-INR N * b - b/2 = -(INR N * b + b/2)). {nra. } rewrite H52. rewrite sin_neg. reflexivity. } rewrite H52.
    assert((sin (INR N * a + a / 2) * sin (b / 2) +
  - sin (INR N * b + b / 2) * sin (a / 2) = 0) -> (2 * sin (INR N * a + a / 2) * sin (b / 2) +
  2 * - sin (INR N * b + b / 2) * sin (a / 2) = 0)). {nra. } apply H53.
    assert(sin (INR N * a + a / 2) * sin (b / 2) +
  - sin (INR N * b + b / 2) * sin (a / 2) = sin (INR N * a + a / 2) * sin (b / 2) -
    sin (INR N * b + b / 2) * sin (a / 2)). {nra. } rewrite H54.
    rewrite Heqa. rewrite Heqb.
    assert ( (i>j)%nat \/ (i<j)%nat). { omega. } destruct H55. 
    * (* i > j case *)
      assert ( INR (i-j) = INR i - INR j). { apply minus_INR. omega. } rewrite <-H56.
      assert (sin  (INR N * (INR (i - j) * PI / INR (N + 1)) + INR (i - j) * PI / INR (N + 1) / 2) =
                sin ( INR (i-j) * PI - (INR (i-j)*PI)/ (2 * INR (N+1)))).
      { assert (INR N * (INR (i - j) * PI / INR (N + 1))= (INR N * (INR (i - j) * PI) * (/ INR (N+1)))). { nra. } rewrite H57.
        assert (INR (i - j) * PI / INR (N + 1) / 2= (INR (i-j) * PI) * (/2 */INR (N+1))). { nra. } rewrite H58.
        assert (/ (2* INR (N+1)) = (/2) * (/ INR (N+1))). { apply Rinv_mult_distr. nra. assert ( 0 < INR (N+1) ->INR (N + 1) <> 0). { nra. } apply H59. apply lt_0_INR. omega. } rewrite <-H59.
        assert (INR N * (INR (i - j) * PI) * / INR (N + 1)= 1 * INR N * (INR (i - j) * PI) * / INR (N + 1)). { nra. } rewrite H60.
        assert (1=  2* (/2)). { apply Rinv_r_sym. nra. } rewrite H61.
        assert (2 * / 2 * INR N * (INR (i - j) * PI) *   / INR (N + 1)=
                  (2* INR N * INR (i-j) * PI) *(/2 * / INR (N+1))). { nra. } rewrite H62. rewrite <-H59.
        assert ( 2 * INR N * INR (i - j) * PI *   / (2 * INR (N + 1)) + INR (i - j) * PI * / (2 * INR (N + 1))=
                (  2 * INR N * INR (i - j) * PI + INR (i - j) * PI ) * (/ (2* INR (N+1)))). { nra. } rewrite H63.
        assert (2 * INR N * INR (i - j) * PI + INR (i - j) * PI= (2 * (INR N +1) * PI * INR (i-j) - PI * INR (i-j))). { nra. } rewrite H64.
        assert ( INR 1 = 1). { reflexivity. } rewrite <-H65. assert ( INR (N+1) = INR N + INR 1). { apply plus_INR. } rewrite <-H66.
        assert ( ((2 * INR (N + 1) * PI * INR (i - j) -  PI * INR (i - j)) * / (2 * INR (N + 1)))=
                  ( ( 2 * INR (N+1)) * (/ (2* INR (N+1)))) * PI * INR (i-j) - (PI * INR (i-j)) * (/ (2 * INR (N+1)))). { nra. } rewrite H67.
        assert (( 2 * INR (N+1)) * (/ (2* INR (N+1))) = 1). { apply Rinv_r. apply Rmult_integral_contrapositive_currified. nra. 
        assert ( 0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H68. apply lt_0_INR. omega. } rewrite H68.
        assert (1 * PI * INR (i - j)=INR (i - j) * PI). { nra. } rewrite H69.
        assert (PI * INR (i - j) * / (2 * INR (N + 1))=INR (i - j) * PI / (2 * INR (N + 1))). { nra. } rewrite H70. reflexivity. } 
        rewrite H57.

       assert (INR (i + j + 2) * PI * / INR (N + 1) / 2 = ( INR (i+j+2) * PI) * (/2 * /INR (N+1))). { nra. } rewrite H58.
       assert ( (/ (2 * INR (N+1)))= (/ 2 * / INR (N + 1))). { apply Rinv_mult_distr. nra. assert ( 0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H59. apply lt_0_INR. omega. } rewrite <-H59.
       assert (INR (i - j) * PI / INR (N + 1) / 2= (INR (i-j) * PI) * (/2 * / INR (N+1))). { nra. } rewrite H60. 
       assert ( (/ (2* INR (N+1))) = /2 * / INR (N+1)). { apply Rinv_mult_distr. nra. assert ( 0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H61. apply lt_0_INR. omega. } rewrite H61.
       assert (sin  (INR N * (INR (i + j + 2) * PI * / INR (N + 1)) + INR (i + j + 2) * PI * (/ 2 * / INR (N + 1)))=
                sin ( INR (i+j+2) * PI - (INR (i+j+2) * PI  * (/ (2* INR (N+1)))))). 
       { rewrite <-H59. 
         assert (INR N * (INR (i + j + 2) * PI * / INR (N + 1)) = 1* INR N * (INR (i + j + 2) * PI * / INR (N + 1))). { nra. } rewrite H62.
         assert (1 = 2 * /2). { apply Rinv_r_sym. nra. } rewrite H63.
         assert ((2 * / 2) * INR N *   (INR (i + j + 2) * PI * / INR (N + 1))=
                  ( 2 * INR N *INR (i+j+2) * PI) * (/2 * / INR (N+1))). { nra. } rewrite H64. rewrite <-H59.
         assert (2 * INR N * INR (i + j + 2) * PI * (/ (2 * INR (N + 1))) +  INR (i + j + 2) * PI * / (2 * INR (N + 1))=
                   ( 2* (INR N +1) * INR (i+j+2) * PI - INR (i+j+2) * PI) * (/ (2* INR (N+1)))). { nra. } rewrite H65.
         assert (INR 1 =1). { reflexivity. } rewrite <-H66. assert  (INR (N+1) = INR N + INR 1). { apply plus_INR. } rewrite <-H67.
         assert ( ((2 * INR (N + 1) * INR (i + j + 2) * PI - INR (i + j + 2) * PI) * / (2 * INR (N + 1)))=
                ( (2* INR (N+1)) * (/ (2* INR (N+1)))) * INR (i+j+2) * PI - (INR (i+j+2) * PI * (/ (2 *INR (N+1))))). { nra. } rewrite H68.
         assert ( 1=  (2* INR (N+1)) * (/ (2* INR (N+1)))). { apply Rinv_r_sym. apply Rmult_integral_contrapositive_currified. nra.
         assert ( 0< INR (N+1) ->  INR (N + 1) <> 0). { nra. } apply H69. apply lt_0_INR. omega. } rewrite <-H69.
         assert ( 1 * INR (i + j + 2) * PI=INR (i + j + 2) * PI). { nra. } rewrite H70. reflexivity. } rewrite H62.
       
         assert ( even (i-j)%nat \/ odd (i-j)%nat). { apply even_or_odd. } destruct H63.
         + assert ( even (i+j+2)%nat \/ odd (i+j+2)%nat). { apply even_or_odd. } destruct H64.
           - assert ( even (i-j)%nat <-> Nat.Even (i-j)%nat). { apply even_equiv. } destruct H65. specialize (H65 H63). rewrite <-H59. 
             (* you need to prove here *)
            remember ((i-j)%nat) as k.
            assert(sin(INR k *PI - INR k *PI *(/ (2*INR (N+1)))) = -sin(INR k * PI * (/ (2*INR (N+1))))).
            { intros. induction k.
            - assert(INR 0 = 0). {reflexivity. } rewrite H67. assert(0*PI - 0*PI* (/ (2*INR (N + 1))) = 0). { nra. } assert( 0*PI * (/ (2*(INR (N + 1)))) = 0). {nra. } rewrite H68. rewrite H69. rewrite sin_0. nra.
            - assert (INR(S k) = INR (k + 1)). {intuition. } rewrite H67. assert(INR(k+1) *PI = INR k *PI+ INR 1 * PI). {rewrite plus_INR. nra. } rewrite H68.
              assert(INR 1 = 1). {reflexivity. } rewrite H69. assert(1*PI = PI). {nra. } rewrite H70. assert( (INR k * PI + PI -  (INR k * PI + PI) * / (2 * INR (N + 1))) = PI - ((PI * INR k + PI) *(/ (2* INR (N + 1))) - INR k * PI)).
              {nra. } rewrite H71. rewrite sin_PI_x. assert(Nat.Odd k). {assert(S k = (k + 1)%nat). {omega. } rewrite even_equiv in H66. rewrite Nat.Even_succ in H65. apply H65. } unfold Nat.Odd in H72.
              assert(INR k = 2 * INR k/2). {nra. } rewrite H73. assert((PI * (2 * INR k / 2) + PI) * (/ (2* INR (N + 1))) - 2 * INR k / 2 * PI = -(2 * INR k / 2 * PI - ((PI * (2 * INR k / 2) + PI)* (/ (2 * INR (N + 1)))))). {nra. } rewrite H74. rewrite sin_neg.
              assert(2 * INR k / 2 * PI - (PI * (2 * INR k / 2) + PI) * (/ (2 *INR (N + 1))) = - (PI * (2 * INR k / 2) + PI)* ( / (2* INR (N + 1))) + 2 * INR k / 2 * PI ). {nra. } rewrite H75.
              destruct H72. rewrite H72. assert(INR(2*x + 1) = INR(2*x) + INR 1). {rewrite plus_INR. reflexivity. } rewrite H76. assert(2 * (INR (2 * x) + INR 1) / 2 * PI = (2 * INR (2 * x) + 2 * INR 1)/ 2 * PI). {nra. } rewrite H77.
              assert((2 * INR (2 * x) + 2 * INR 1) / 2 * PI = 2/2 * INR (2 * x) * PI + 2/2 * INR 1 * PI). {nra. } rewrite H78. assert(2/2 = 1). {nra. } rewrite H79.
              assert(1 * INR (2*x) * PI + 1 * INR 1 * PI = INR(2*x) * PI + INR 1 * PI). {nra. } rewrite H80. assert(INR 1 = 1). {reflexivity. } rewrite H81. assert(1*PI = PI). {nra. } rewrite H82.
              assert(-sin(- (PI * (2 * (INR (2 * x) + 1) / 2) + PI) * (/ (2 * INR (N + 1))) + (INR (2 * x) * PI + PI)) = -sin(-(PI * (2 * (INR (2 * x) + 1) / 2) + PI)* ( / (2* INR (N + 1))) + INR (2 * x) * PI + PI)). {intuition. } rewrite H83.
              rewrite neg_sin. rewrite mult_INR. assert(INR 2 = 2). {reflexivity. } rewrite H84. rewrite sin_period.
              assert(- (PI * (2 * (2 * INR x + 1) / 2) + PI) * (/ (2 * INR (N + 1)))  = - ((PI * (2 * (2 * INR x + 1) / 2) + PI) * (/ (2* INR (N + 1))))). {nra. } rewrite H85. rewrite sin_neg.
              assert ( (2 * (2 * INR x + 1) / 2) = (2 * INR x + 1) ). { nra. } rewrite H86.
              assert ((PI * (2 * INR x + 1))= 2 * INR x * PI + PI). { nra. } rewrite H87. nra.
            }
            assert (sin (INR k * PI - INR k * PI / (2 * INR (N + 1)))= sin  (INR k * PI - INR k * PI * / (2 * INR (N + 1)))). { nra. } rewrite H68. rewrite H67.
            assert (sin  (INR (i + j + 2) * PI - INR (i + j + 2) * PI * / (2 * INR (N + 1)))=-sin (INR (i + j + 2) * PI * / (2 * INR (N + 1)))).
            {  remember ((i+j+2)%nat) as q. assert(sin(INR q *PI - INR q *PI * (/(2* INR (N + 1)))) = -sin(PI*INR q * (/(2* INR (N + 1))))).
              { intros. induction q.
              - assert(INR 0 = 0). {reflexivity. } rewrite H69. assert( 0*PI - 0* PI * (/ (2* INR (N + 1))) = 0). {nra. } rewrite H70. assert(PI * 0 * (/ (2* INR (N + 1))) = 0). {nra. } rewrite H71.  assert ( sin 0 = 0).  { apply sin_0. } rewrite H72.  nra. 
              - assert (INR(S q) = INR (q + 1)). {intuition. } rewrite H69. assert(INR(q+1) *PI = INR q * PI+ INR 1*PI). {rewrite plus_INR. nra. } rewrite H70.
                assert(INR 1 = 1). {reflexivity. } rewrite H71. assert(1* PI = PI). {nra. } rewrite H72. assert(INR q *PI+ PI - (INR q *PI+ PI)* ( / (2*INR (N + 1))) = PI - ((INR q *PI+ PI) * (/ (2* INR (N + 1))) - INR q * PI)).
                {nra. } rewrite H73. rewrite sin_PI_x. assert(Nat.Odd q). {assert(S q = (q + 1)%nat). {omega. } rewrite even_equiv in H64. rewrite Nat.Even_succ in H64. apply H64. } unfold Nat.Odd in H74.
                assert(INR q = 2 * INR q/2). {nra. } rewrite H75. assert(((2 * INR q / 2)*PI + PI) * (/ (2* INR (N + 1))) - 2 * INR q / 2 * PI = -(2 * INR q / 2 * PI - ((PI * (2 * INR q / 2) + PI)* (/ (2* INR (N + 1)))))). {nra. } rewrite H76. rewrite sin_neg.
                assert(2 * INR q / 2 * PI - (PI * (2 * INR q / 2) + PI) * (/ (2* INR (N + 1))) = - (PI * (2 * INR q / 2) + PI) * ( / (2* INR (N + 1))) + 2 * INR q / 2 * PI ). {nra. } rewrite H77.
                destruct H74. rewrite H74. assert(INR(2*x + 1) = INR(2*x) + INR 1). {rewrite plus_INR. reflexivity. } rewrite H78. assert(2 * (INR (2 * x) + INR 1) / 2 * PI = (2 * INR (2 * x) + 2 * INR 1)/ 2 * PI). {nra. } rewrite H79.
                assert((2 * INR (2 * x) + 2 * INR 1) / 2 * PI = 2/2 * INR (2 * x) * PI + 2/2 * INR 1 * PI). {nra. } rewrite H80. assert(2/2 = 1). {nra. } rewrite H81. 
                assert(1 * INR (2*x) * PI + 1 * INR 1 * PI = INR(2*x) * PI + INR 1 * PI). {nra. } rewrite H82. assert(INR 1 = 1). {reflexivity. } rewrite H83. assert(1*PI = PI). {nra. } rewrite H84.
                assert(-sin(- (PI * (2 * (INR (2 * x) + 1) / 2) + PI) *(/ (2* INR (N + 1))) + (INR (2 * x) * PI + PI)) = -sin(-(PI * (2 * (INR (2 * x) + 1) / 2) + PI) * (/ (2* INR (N + 1))) + INR (2 * x) * PI + PI)). {intuition. } rewrite H85.
                rewrite neg_sin. rewrite mult_INR. assert(INR 2 = 2). {reflexivity. } rewrite H86. rewrite sin_period.
                assert(- (PI * (2 * (2 * INR x + 1) / 2) + PI) * (/ (2* INR (N + 1))) = - ((PI * (2 * (2 * INR x + 1) / 2) + PI) * (/ (2* INR (N + 1))))). {nra. } rewrite H87. rewrite sin_neg.
                assert ((2 * (2 * INR x + 1) / 2)= (2 * INR x + 1)). { nra. } rewrite H88.
                assert ((PI * (2 * INR x + 1) + PI)= PI * 2 * INR x + PI + PI). { nra. } rewrite H89.
                assert ((2 * x + 1 + 1)%nat = (2 * x +2)%nat). { omega. } rewrite H90. assert ( INR (2 * x + 2)= INR (2*x) + INR 2). { apply plus_INR. } rewrite H91.
                assert (INR (2 * x)= INR 2 * INR x). { apply mult_INR. } rewrite H92. assert ( INR 2=2). { reflexivity. } rewrite H93.
                assert ((PI * 2 * INR x + PI + PI)=PI * (2 * INR x + 2)). { nra. } rewrite H94. nra.
              } rewrite H69.
              assert (PI * INR q=INR q * PI). { apply Rmult_comm. } rewrite H70. nra.
            } rewrite H69. nra.
          - contradict H64. apply even_3. omega. assert (even (i+j+2) <-> Nat.Even (i+j+2)). { apply even_equiv. } destruct H64. apply H64. apply even_1. omega. apply H63.
        + assert ( even (i+j+2)%nat \/ odd (i+j+2)%nat). { apply even_or_odd. } destruct H64.
          - contradict H64. apply odd_4. omega. assert ( odd (i+j+2) <-> Nat.Odd (i+j+2)). { apply odd_equiv. } destruct H64. apply H64. apply odd_1. omega. apply H63.
          -  remember ((i-j)%nat) as k. assert( sin(INR k *PI - INR k * PI * (/ (2* INR (N + 1)))) = sin(INR k * PI * (/(2 * INR (N + 1))))).
            {intros. induction k.
            - assert(INR 0 = 0). {reflexivity. } rewrite H65. assert(0*PI -  0*PI* ( / (2* INR (N + 1))) = 0). {nra. } rewrite H66. assert(0*PI * (/ (2* INR (N + 1))) = 0). {nra. } rewrite H67. nra.
            - assert (INR(S k) = INR (k + 1)). {intuition. } rewrite H65. assert(INR(k+1) *PI  = INR k * PI+ INR 1 * PI). {rewrite plus_INR. nra. } rewrite H66.
              assert(INR 1 = 1). {reflexivity. } rewrite H67. assert(1*PI = PI). {nra. } rewrite H68. assert(INR k *PI+ PI - (INR k *PI+ PI) * (/ (2* INR (N + 1))) = PI - ((INR k *PI + PI)* ( / (2* INR (N + 1))) - INR k * PI)).
              {nra. } rewrite H69. rewrite sin_PI_x. assert(Nat.Even k). {assert(S k = (k + 1)%nat). {omega. } rewrite odd_equiv in H63. rewrite Nat.Odd_succ in H63. apply H63. } unfold Nat.Even in H70.
              assert(INR k = 2 * INR k/2). {nra. } rewrite H71. assert(((2 * INR k / 2)*PI + PI) * (/ (2* INR (N + 1))) - 2 * INR k / 2 * PI = -(2 * INR k / 2 * PI - ((PI * (2 * INR k / 2) + PI) * (/ (2* INR (N + 1)))))). {nra. } rewrite H72. rewrite sin_neg.
              assert(2 * INR k / 2 * PI - (PI * (2 * INR k / 2) + PI) * (/ (2* INR (N + 1))) = - (PI * (2 * INR k / 2) + PI) * (/ (2* INR (N + 1))) + 2 * INR k / 2 * PI ). {nra. } rewrite H73.
              assert(exists m, INR k / 2 = INR (m)). {destruct H70. exists x. rewrite H70. rewrite mult_INR. assert(INR 2 * INR x / 2 = INR 2 / 2 * INR x). {nra. } assert(INR 2 = 2). {reflexivity. } rewrite H75. nra. }
              destruct H74. assert(2 * INR k / 2 * PI = 2 * INR x * PI). {assert(2 * INR k / 2 * PI = INR k / 2 * 2 * PI). {nra. } rewrite H75. rewrite H74. nra.  } rewrite H75.
              rewrite (sin_period (- (PI * (2 * INR k / 2) + PI) *(/ (2* INR (N + 1)))) (x)). assert(-(PI * (2 * INR k / 2) + PI)* ( / (2* INR (N + 1))) = -((PI * (2 * INR k / 2) + PI)* ( / (2* INR (N + 1))))). {nra. }
              rewrite H76. rewrite (sin_neg ((PI * (2 * INR k / 2) + PI) *(/ (2* INR (N + 1))))). rewrite <-H75.
              assert ((PI * (2 * INR k / 2) + PI)=(2 * INR k / 2 * PI + PI)). { nra. } rewrite H77. nra. }
            assert (sin  (INR (i + j + 2) * PI -  INR (i + j + 2) * PI * / (2 * INR (N + 1))) = sin (INR (i + j + 2) * PI * (/ 2 * / INR (N + 1)))). 
            {   remember ((i+j+2)%nat) as q. rewrite <-H59.
                assert(sin (INR q * PI - INR q * PI *(/ (2* INR (N + 1)))) =  sin (INR q * PI * (/ ( 2 * INR (N + 1))))).
                { intros. induction q.
                - assert(INR 0 = 0). {reflexivity. } rewrite H66. assert(0 * PI - 0 * PI * (/ (2* INR (N + 1))) = 0). {nra. } rewrite H67.  assert(0 * PI *  (/ (2 * INR (N + 1))) = 0). {nra. } rewrite H68.  nra.
                - assert (INR(S q) = INR (q + 1)). {intuition. } rewrite H66. assert(INR(q+1) * PI = PI * INR q + PI * INR 1). {rewrite plus_INR. nra. } rewrite H67.
                assert(INR 1 = 1). {reflexivity. } rewrite H68. assert(PI * 1 = PI). {nra. } rewrite H69. assert(PI * INR q + PI - (PI * INR q + PI) *(/ (2* INR (N + 1))) = PI - ((PI * INR q + PI) * (/ (2* INR (N + 1))) - INR q * PI)).
                {nra. } rewrite H70. rewrite sin_PI_x. assert(Nat.Even q). {assert(S q = (q + 1)%nat). {omega. }  rewrite odd_equiv in H64. rewrite Nat.Odd_succ in H64. apply H64. } unfold Nat.Even in H71.
                assert(INR q = 2 * INR q/2). {nra. } rewrite H72. assert((PI * (2 * INR q / 2) + PI) * (/ (2* INR (N + 1))) - 2 * INR q / 2 * PI = -(2 * INR q / 2 * PI - ((PI * (2 * INR q / 2) + PI) * (/ (2* INR (N + 1)))))). {nra. } rewrite H73. rewrite sin_neg.
                assert(2 * INR q / 2 * PI - (PI * (2 * INR q / 2) + PI) * (/ (2* INR (N + 1))) = - (PI * (2 * INR q / 2) + PI) * (/ (2* INR (N + 1))) + 2 * INR q / 2 * PI ). {nra. } rewrite H74.
                destruct H71. assert(2 * INR q / 2 * PI = 2 * INR x * PI). {assert(2 * INR q / 2 * PI = INR q / 2 * 2 * PI). {nra. } rewrite H75. rewrite H71. rewrite mult_INR. assert(INR 2 = 2). {reflexivity. } rewrite H76. nra.  }
                assert(PI * (2 * INR q /2) = 2 * INR q / 2 * PI). {nra. } rewrite H76. rewrite H75.
                rewrite (sin_period (- (2 * INR x * PI + PI) * (/ (2 *INR (N + 1)))) (x)). assert(- (2 * INR x * PI + PI) * (/ (2* INR (N + 1))) = - ((2 * INR x * PI + PI) * (/ (2* INR (N + 1))))). {nra. } rewrite H77.
                rewrite (sin_neg ((2 * INR x * PI + PI) * (/ (2* INR (N + 1))))). nra. }
                rewrite H66. nra.
          } rewrite H66. rewrite <-H59.
            assert ( (INR k * PI -  INR k * PI * / (2 * INR (N + 1)))= (INR k * PI - INR k * PI / (2 * INR (N + 1)))). { nra. } rewrite <-H67. rewrite H65. nra.
     * assert ( (INR i - INR j)= - (INR j - INR i)). { nra. } rewrite H56. 
       assert ( INR (j-i) = INR j - INR i). { apply minus_INR. omega. } rewrite <-H57.
       assert ( (INR N * (- INR (j - i) * PI / INR (N + 1)) + - INR (j - i) * PI / INR (N + 1) / 2) = 
                - ( INR N * (INR (j - i) * PI / INR (N + 1)) +  INR (j - i) * PI / INR (N + 1) / 2)). { nra. } rewrite H58.
       assert (sin  (-   (INR N * (INR (j - i) * PI / INR (N + 1)) +  INR (j - i) * PI / INR (N + 1) / 2))=
                - sin ((INR N * (INR (j - i) * PI / INR (N + 1)) +  INR (j - i) * PI / INR (N + 1) / 2))). { apply sin_neg. } rewrite  H59.
       assert ( (- INR (j - i) * PI / INR (N + 1) / 2)= - (INR (j - i) * PI / INR (N + 1) / 2)). { nra. } rewrite H60.
       assert (sin (- (INR (j - i) * PI / INR (N + 1) / 2))= - sin ( (INR (j - i) * PI / INR (N + 1) / 2))). { apply sin_neg. } rewrite H61.
       assert (sin
                  (INR N * (INR (i + j + 2) * PI * / INR (N + 1)) +
                   INR (i + j + 2) * PI * / INR (N + 1) / 2) *
                - sin (INR (j - i) * PI / INR (N + 1) / 2)= - sin
                  (INR N * (INR (i + j + 2) * PI * / INR (N + 1)) +
                   INR (i + j + 2) * PI * / INR (N + 1) / 2) * sin (INR (j - i) * PI / INR (N + 1) / 2)). { nra. } rewrite H62.
      assert (-
                sin
                  (INR N * (INR (j - i) * PI / INR (N + 1)) +
                   INR (j - i) * PI / INR (N + 1) / 2) *
                sin (INR (i + j + 2) * PI * / INR (N + 1) / 2) -
                -
                sin
                  (INR N * (INR (i + j + 2) * PI * / INR (N + 1)) +
                   INR (i + j + 2) * PI * / INR (N + 1) / 2) *
                sin (INR (j - i) * PI / INR (N + 1) / 2)=- sin
                  (INR N * (INR (j - i) * PI / INR (N + 1)) +
                   INR (j - i) * PI / INR (N + 1) / 2) *
                sin (INR (i + j + 2) * PI * / INR (N + 1) / 2) + sin
                  (INR N * (INR (i + j + 2) * PI * / INR (N + 1)) +
                   INR (i + j + 2) * PI * / INR (N + 1) / 2) *
                sin (INR (j - i) * PI / INR (N + 1) / 2)). { nra. } rewrite H63.
    assert (-
              sin
                (INR N * (INR (j - i) * PI / INR (N + 1)) +
                 INR (j - i) * PI / INR (N + 1) / 2) *
              sin (INR (i + j + 2) * PI * / INR (N + 1) / 2)= - (sin
                (INR N * (INR (j - i) * PI / INR (N + 1)) +
                 INR (j - i) * PI / INR (N + 1) / 2) * sin (INR (i + j + 2) * PI * / INR (N + 1) / 2))). { nra. } rewrite H64.
    
     assert (sin  (INR N * (INR (j - i) * PI / INR (N + 1)) + INR (j - i) * PI / INR (N + 1) / 2) =
                sin ( INR (j-i) * PI - (INR (j-i)*PI)/ (2 * INR (N+1)))).
      { assert (INR N * (INR (j - i) * PI / INR (N + 1))= (INR N * (INR (j - i) * PI) * (/ INR (N+1)))). { nra. } rewrite H65.
        assert (INR (j - i) * PI / INR (N + 1) / 2= (INR (j-i) * PI) * (/2 */INR (N+1))). { nra. } rewrite H66.
        assert (/ (2* INR (N+1)) = (/2) * (/ INR (N+1))). { apply Rinv_mult_distr. nra. assert ( 0 < INR (N+1) ->INR (N + 1) <> 0). { nra. } apply H67. apply lt_0_INR. omega. } rewrite <-H67.
        assert (INR N * (INR (j - i) * PI) * / INR (N + 1)= 1 * INR N * (INR (j - i) * PI) * / INR (N + 1)). { nra. } rewrite H68.
        assert (1=  2* (/2)). { apply Rinv_r_sym. nra. } rewrite H69.
        assert (2 * / 2 * INR N * (INR (j - i) * PI) *   / INR (N + 1)=
                  (2* INR N * INR (j-i) * PI) *(/2 * / INR (N+1))). { nra. } rewrite H70.  rewrite <-H67.
        assert ( 2 * INR N * INR (j - i) * PI *   / (2 * INR (N + 1)) + INR (j - i) * PI * / (2 * INR (N + 1))=
                (  2 * INR N * INR (j - i) * PI + INR (j - i) * PI ) * (/ (2* INR (N+1)))). { nra. } rewrite H71.
        assert (2 * INR N * INR (j - i) * PI + INR (j - i) * PI= (2 * (INR N +1) * PI * INR (j-i) - PI * INR (j-i))). { nra. } rewrite H72.
        assert ( INR 1 = 1). { reflexivity. } rewrite <-H73. assert ( INR (N+1) = INR N + INR 1). { apply plus_INR. } rewrite <-H74.
        assert ( ((2 * INR (N + 1) * PI * INR (j - i) -  PI * INR (j - i)) * / (2 * INR (N + 1)))=
                  ( ( 2 * INR (N+1)) * (/ (2* INR (N+1)))) * PI * INR (j-i) - (PI * INR (j-i)) * (/ (2 * INR (N+1)))). { nra. } rewrite H75.
        assert (( 2 * INR (N+1)) * (/ (2* INR (N+1))) = 1). { apply Rinv_r. apply Rmult_integral_contrapositive_currified. nra. 
        assert ( 0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H76. apply lt_0_INR. omega. } rewrite H76.
        assert (1 * PI * INR (j - i)=INR (j - i) * PI). { nra. } rewrite H77.
        assert (PI * INR (j - i) * / (2 * INR (N + 1))=INR (j - i) * PI / (2 * INR (N + 1))). { nra. } rewrite H78. reflexivity. } 
        rewrite H65.
      
       assert (INR (i + j + 2) * PI * / INR (N + 1) / 2 = ( INR (i+j+2) * PI) * (/2 * /INR (N+1))). { nra. } rewrite H66.
       assert ( (/ (2 * INR (N+1)))= (/ 2 * / INR (N + 1))). { apply Rinv_mult_distr. nra. assert ( 0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H67. apply lt_0_INR. omega. } rewrite <-H67.
       assert (INR (j - i) * PI / INR (N + 1) / 2= (INR (j-i) * PI) * (/2 * / INR (N+1))). { nra. } rewrite H68. 
       assert ( (/ (2* INR (N+1))) = /2 * / INR (N+1)). { apply Rinv_mult_distr. nra. assert ( 0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H69. apply lt_0_INR. omega. } rewrite H69.
       assert (sin  (INR N * (INR (i + j + 2) * PI * / INR (N + 1)) + INR (i + j + 2) * PI * (/ 2 * / INR (N + 1)))=
                sin ( INR (i+j+2) * PI - (INR (i+j+2) * PI  * (/ (2* INR (N+1)))))). 
       { rewrite <-H69. 
         assert (INR N * (INR (i + j + 2) * PI * / INR (N + 1)) = 1* INR N * (INR (i + j + 2) * PI * / INR (N + 1))). { nra. } rewrite H70.
         assert (1 = 2 * /2). { apply Rinv_r_sym. nra. } rewrite H71.
         assert ((2 * / 2) * INR N *   (INR (i + j + 2) * PI * / INR (N + 1))=
                  ( 2 * INR N *INR (i+j+2) * PI) * (/2 * / INR (N+1))). { nra. } rewrite H72. rewrite <-H69.
         assert (2 * INR N * INR (i + j + 2) * PI * (/ (2 * INR (N + 1))) +  INR (i + j + 2) * PI * / (2 * INR (N + 1))=
                   ( 2* (INR N +1) * INR (i+j+2) * PI - INR (i+j+2) * PI) * (/ (2* INR (N+1)))). { nra. } rewrite H73.
         assert (INR 1 =1). { reflexivity. } rewrite <-H74. assert  (INR (N+1) = INR N + INR 1). { apply plus_INR. } rewrite <-H75.
         assert ( ((2 * INR (N + 1) * INR (i + j + 2) * PI - INR (i + j + 2) * PI) * / (2 * INR (N + 1)))=
                ( (2* INR (N+1)) * (/ (2* INR (N+1)))) * INR (i+j+2) * PI - (INR (i+j+2) * PI * (/ (2 *INR (N+1))))). { nra. } rewrite H76.
         assert ( 1=  (2* INR (N+1)) * (/ (2* INR (N+1)))). { apply Rinv_r_sym. apply Rmult_integral_contrapositive_currified. nra.
         assert ( 0< INR (N+1) ->  INR (N + 1) <> 0). { nra. } apply H77. apply lt_0_INR. omega. } rewrite <-H77.
         assert ( 1 * INR (i + j + 2) * PI=INR (i + j + 2) * PI). { nra. } rewrite H78. reflexivity. } rewrite H70.
         assert ( even (j-i)%nat \/ odd (j-i)%nat). { apply even_or_odd. } destruct H71.
         + assert ( even (i+j+2)%nat \/ odd (i+j+2)%nat). { apply even_or_odd. } destruct H72.
           - assert ( even (j-i)%nat <-> Nat.Even (j-i)%nat). { apply even_equiv. } destruct H73. specialize (H73 H71). rewrite <-H69.
              remember ((j-i)%nat) as k.
              assert(sin(INR k *PI - INR k *PI *(/ (2*INR (N+1)))) = -sin(INR k * PI * (/ (2*INR (N+1))))).
             { intros. induction k.
            - assert(INR 0 = 0). {reflexivity. } rewrite H75. assert(0*PI - 0*PI* (/ (2*INR (N + 1))) = 0). { nra. } rewrite H76. assert( 0*PI * (/ (2*(INR (N + 1)))) = 0). {nra. }  rewrite H77. rewrite sin_0. nra.
            - assert (INR(S k) = INR (k + 1)). {intuition. } rewrite H75. assert(INR(k+1) *PI = INR k *PI+ INR 1 * PI). {rewrite plus_INR. nra. } rewrite H76.
              assert(INR 1 = 1). {reflexivity. } rewrite H77. assert(1*PI = PI). {nra. } rewrite H78. assert( (INR k * PI + PI -  (INR k * PI + PI) * / (2 * INR (N + 1))) = PI - ((PI * INR k + PI) *(/ (2* INR (N + 1))) - INR k * PI)).
              {nra. } rewrite H79. rewrite sin_PI_x. assert(Nat.Odd k). {assert(S k = (k + 1)%nat). {omega. } rewrite even_equiv in H74. rewrite Nat.Even_succ in H73. apply H73. } unfold Nat.Odd in H80.
              assert(INR k = 2 * INR k/2). {nra. } rewrite H81. assert((PI * (2 * INR k / 2) + PI) * (/ (2* INR (N + 1))) - 2 * INR k / 2 * PI = -(2 * INR k / 2 * PI - ((PI * (2 * INR k / 2) + PI)* (/ (2 * INR (N + 1)))))). {nra. } rewrite H82. rewrite sin_neg.
              assert(2 * INR k / 2 * PI - (PI * (2 * INR k / 2) + PI) * (/ (2 *INR (N + 1))) = - (PI * (2 * INR k / 2) + PI)* ( / (2* INR (N + 1))) + 2 * INR k / 2 * PI ). {nra. } rewrite H83.
              destruct H80. rewrite H80. assert(INR(2*x + 1) = INR(2*x) + INR 1). {rewrite plus_INR. reflexivity. } rewrite H84. assert(2 * (INR (2 * x) + INR 1) / 2 * PI = (2 * INR (2 * x) + 2 * INR 1)/ 2 * PI). {nra. } rewrite H85.
              assert((2 * INR (2 * x) + 2 * INR 1) / 2 * PI = 2/2 * INR (2 * x) * PI + 2/2 * INR 1 * PI). {nra. } rewrite H86. assert(2/2 = 1). {nra. } rewrite H87.
              assert(1 * INR (2*x) * PI + 1 * INR 1 * PI = INR(2*x) * PI + INR 1 * PI). {nra. } rewrite H88. assert(INR 1 = 1). {reflexivity. } rewrite H89. assert(1*PI = PI). {nra. } rewrite H90.
              assert(-sin(- (PI * (2 * (INR (2 * x) + 1) / 2) + PI) * (/ (2 * INR (N + 1))) + (INR (2 * x) * PI + PI)) = -sin(-(PI * (2 * (INR (2 * x) + 1) / 2) + PI)* ( / (2* INR (N + 1))) + INR (2 * x) * PI + PI)). {intuition. } rewrite H91.
              rewrite neg_sin. rewrite mult_INR. assert(INR 2 = 2). {reflexivity. } rewrite H92. rewrite sin_period.
              assert(- (PI * (2 * (2 * INR x + 1) / 2) + PI) * (/ (2 * INR (N + 1)))  = - ((PI * (2 * (2 * INR x + 1) / 2) + PI) * (/ (2* INR (N + 1))))). {nra. } rewrite H93. rewrite sin_neg.
              assert ( (2 * (2 * INR x + 1) / 2) = (2 * INR x + 1) ). { nra. } rewrite H94.
              assert ((PI * (2 * INR x + 1))= 2 * INR x * PI + PI). { nra. } rewrite H95. nra.
            }
            assert (sin (INR k * PI - INR k * PI / (2 * INR (N + 1)))= sin  (INR k * PI - INR k * PI * / (2 * INR (N + 1)))). { nra. } rewrite H76. rewrite H75.
             assert (sin  (INR (i + j + 2) * PI - INR (i + j + 2) * PI * / (2 * INR (N + 1)))=-sin (INR (i + j + 2) * PI * / (2 * INR (N + 1)))). {
             remember ((i+j+2)%nat) as q. assert(sin(INR q *PI - INR q *PI * (/(2* INR (N + 1)))) = -sin(PI*INR q * (/(2* INR (N + 1))))).
              { intros. induction q.
              - assert(INR 0 = 0). {reflexivity. } rewrite H77. assert( 0*PI - 0* PI * (/ (2* INR (N + 1))) = 0). {nra. } rewrite H78. assert(PI * 0 * (/ (2* INR (N + 1))) = 0). {nra. } rewrite H79.  assert ( sin 0 = 0).  { apply sin_0. } rewrite H80.  nra. 
              - assert (INR(S q) = INR (q + 1)). {intuition. } rewrite H77. assert(INR(q+1) *PI = INR q * PI+ INR 1*PI). {rewrite plus_INR. nra. } rewrite H78.
                assert(INR 1 = 1). {reflexivity. } rewrite H79. assert(1* PI = PI). {nra. } rewrite H80. assert(INR q *PI+ PI - (INR q *PI+ PI)* ( / (2*INR (N + 1))) = PI - ((INR q *PI+ PI) * (/ (2* INR (N + 1))) - INR q * PI)).
                {nra. } rewrite H81. rewrite sin_PI_x. assert(Nat.Odd q). {assert(S q = (q + 1)%nat). {omega. } rewrite even_equiv in H72. rewrite Nat.Even_succ in H72. apply H72. } unfold Nat.Odd in H82.
                assert(INR q = 2 * INR q/2). {nra. } rewrite H83. assert(((2 * INR q / 2)*PI + PI) * (/ (2* INR (N + 1))) - 2 * INR q / 2 * PI = -(2 * INR q / 2 * PI - ((PI * (2 * INR q / 2) + PI)* (/ (2* INR (N + 1)))))). {nra. } rewrite H84. rewrite sin_neg.
                assert(2 * INR q / 2 * PI - (PI * (2 * INR q / 2) + PI) * (/ (2* INR (N + 1))) = - (PI * (2 * INR q / 2) + PI) * ( / (2* INR (N + 1))) + 2 * INR q / 2 * PI ). {nra. } rewrite H85.
                destruct H82. rewrite H82. assert(INR(2*x + 1) = INR(2*x) + INR 1). {rewrite plus_INR. reflexivity. } rewrite H86. assert(2 * (INR (2 * x) + INR 1) / 2 * PI = (2 * INR (2 * x) + 2 * INR 1)/ 2 * PI). {nra. } rewrite H87.
                assert((2 * INR (2 * x) + 2 * INR 1) / 2 * PI = 2/2 * INR (2 * x) * PI + 2/2 * INR 1 * PI). {nra. } rewrite H88. assert(2/2 = 1). {nra. } rewrite H89. 
                assert(1 * INR (2*x) * PI + 1 * INR 1 * PI = INR(2*x) * PI + INR 1 * PI). {nra. } rewrite H90. assert(INR 1 = 1). {reflexivity. } rewrite H91. assert(1*PI = PI). {nra. } rewrite H92.
                assert(-sin(- (PI * (2 * (INR (2 * x) + 1) / 2) + PI) *(/ (2* INR (N + 1))) + (INR (2 * x) * PI + PI)) = -sin(-(PI * (2 * (INR (2 * x) + 1) / 2) + PI) * (/ (2* INR (N + 1))) + INR (2 * x) * PI + PI)). {intuition. } rewrite H93.
                rewrite neg_sin. rewrite mult_INR. assert(INR 2 = 2). {reflexivity. } rewrite H94. rewrite sin_period.
                assert(- (PI * (2 * (2 * INR x + 1) / 2) + PI) * (/ (2* INR (N + 1))) = - ((PI * (2 * (2 * INR x + 1) / 2) + PI) * (/ (2* INR (N + 1))))). {nra. } rewrite H95. rewrite sin_neg.
                assert ((2 * (2 * INR x + 1) / 2)= (2 * INR x + 1)). { nra. } rewrite H96.
                assert ((PI * (2 * INR x + 1) + PI)= PI * 2 * INR x + PI + PI). { nra. } rewrite H97.
                assert ((2 * x + 1 + 1)%nat = (2 * x +2)%nat). { omega. } rewrite H98. assert ( INR (2 * x + 2)= INR (2*x) + INR 2). { apply plus_INR. } rewrite H99.
                assert (INR (2 * x)= INR 2 * INR x). { apply mult_INR. } rewrite H100. assert ( INR 2=2). { reflexivity. } rewrite H101.
                assert ((PI * 2 * INR x + PI + PI)=PI * (2 * INR x + 2)). { nra. } rewrite H102. nra.
              } rewrite H77.
              assert (PI * INR q=INR q * PI). { apply Rmult_comm. } rewrite H78. nra.
             } 
             rewrite H77. nra. 
           - contradict H72. apply even_4. omega. assert (even (i+j+2) <-> Nat.Even (i+j+2)). { apply even_equiv. } destruct H72. apply H72. apply even_2. omega. apply H71.
         + assert ( even (i+j+2)%nat \/ odd (i+j+2)%nat). { apply even_or_odd. } destruct H72.
          - contradict H72. apply odd_5. omega. assert ( odd (i+j+2) <-> Nat.Odd (i+j+2)). { apply odd_equiv. } destruct H72. apply H72. apply odd_2. omega. apply H71.
          -  remember ((j-i)%nat) as k. assert( sin(INR k *PI - INR k * PI * (/ (2* INR (N + 1)))) = sin(INR k * PI * (/(2 * INR (N + 1))))).
            {intros. induction k.
            - assert(INR 0 = 0). {reflexivity. } rewrite H73. assert(0*PI -  0*PI* ( / (2* INR (N + 1))) = 0). {nra. } rewrite H74. assert(0*PI * (/ (2* INR (N + 1))) = 0). {nra. } rewrite H75. nra.
            - assert (INR(S k) = INR (k + 1)). {intuition. } rewrite H73. assert(INR(k+1) *PI  = INR k * PI+ INR 1 * PI). {rewrite plus_INR. nra. } rewrite H74.
              assert(INR 1 = 1). {reflexivity. } rewrite H75. assert(1*PI = PI). {nra. } rewrite H76. assert(INR k *PI+ PI - (INR k *PI+ PI) * (/ (2* INR (N + 1))) = PI - ((INR k *PI + PI)* ( / (2* INR (N + 1))) - INR k * PI)).
              {nra. } rewrite H77. rewrite sin_PI_x. assert(Nat.Even k). {assert(S k = (k + 1)%nat). {omega. } rewrite odd_equiv in H71. rewrite Nat.Odd_succ in H71. apply H71. } unfold Nat.Even in H78.
              assert(INR k = 2 * INR k/2). {nra. } rewrite H79. assert(((2 * INR k / 2)*PI + PI) * (/ (2* INR (N + 1))) - 2 * INR k / 2 * PI = -(2 * INR k / 2 * PI - ((PI * (2 * INR k / 2) + PI) * (/ (2* INR (N + 1)))))). {nra. } rewrite H80. rewrite sin_neg.
              assert(2 * INR k / 2 * PI - (PI * (2 * INR k / 2) + PI) * (/ (2* INR (N + 1))) = - (PI * (2 * INR k / 2) + PI) * (/ (2* INR (N + 1))) + 2 * INR k / 2 * PI ). {nra. } rewrite H81.
              assert(exists m, INR k / 2 = INR (m)). {destruct H78. exists x. rewrite H78. rewrite mult_INR. assert(INR 2 * INR x / 2 = INR 2 / 2 * INR x). {nra. } assert(INR 2 = 2). {reflexivity. } rewrite H83. nra. }
              destruct H82. assert(2 * INR k / 2 * PI = 2 * INR x * PI). {assert(2 * INR k / 2 * PI = INR k / 2 * 2 * PI). {nra. } rewrite H83. rewrite H82. nra.  } rewrite H83.
              rewrite (sin_period (- (PI * (2 * INR k / 2) + PI) *(/ (2* INR (N + 1)))) (x)). assert(-(PI * (2 * INR k / 2) + PI)* ( / (2* INR (N + 1))) = -((PI * (2 * INR k / 2) + PI)* ( / (2* INR (N + 1))))). {nra. }
              rewrite H84. rewrite (sin_neg ((PI * (2 * INR k / 2) + PI) *(/ (2* INR (N + 1))))). rewrite <-H83.
              assert ((PI * (2 * INR k / 2) + PI)=(2 * INR k / 2 * PI + PI)). { nra. } rewrite H85. nra. }
            assert (sin  (INR (i + j + 2) * PI -  INR (i + j + 2) * PI * / (2 * INR (N + 1))) = sin (INR (i + j + 2) * PI * (/ 2 * / INR (N + 1)))). {
                 remember ((i+j+2)%nat) as q. rewrite <-H67.
                assert(sin (INR q * PI - INR q * PI *(/ (2* INR (N + 1)))) =  sin (INR q * PI * (/ ( 2 * INR (N + 1))))).
                { intros. induction q.
                - assert(INR 0 = 0). {reflexivity. } rewrite H74. assert(0 * PI - 0 * PI * (/ (2* INR (N + 1))) = 0). {nra. } rewrite H75.  assert(0 * PI *  (/ (2 * INR (N + 1))) = 0). {nra. } rewrite H76.  nra.
                - assert (INR(S q) = INR (q + 1)). {intuition. } rewrite H74. assert(INR(q+1) * PI = PI * INR q + PI * INR 1). {rewrite plus_INR. nra. } rewrite H75.
                assert(INR 1 = 1). {reflexivity. } rewrite H76. assert(PI * 1 = PI). {nra. } rewrite H77. assert(PI * INR q + PI - (PI * INR q + PI) *(/ (2* INR (N + 1))) = PI - ((PI * INR q + PI) * (/ (2* INR (N + 1))) - INR q * PI)).
                {nra. } rewrite H78. rewrite sin_PI_x. assert(Nat.Even q). {assert(S q = (q + 1)%nat). {omega. }  rewrite odd_equiv in H72. rewrite Nat.Odd_succ in H72. apply H72. } unfold Nat.Even in H79.
                assert(INR q = 2 * INR q/2). {nra. } rewrite H80. assert((PI * (2 * INR q / 2) + PI) * (/ (2* INR (N + 1))) - 2 * INR q / 2 * PI = -(2 * INR q / 2 * PI - ((PI * (2 * INR q / 2) + PI) * (/ (2* INR (N + 1)))))). {nra. } rewrite H81. rewrite sin_neg.
                assert(2 * INR q / 2 * PI - (PI * (2 * INR q / 2) + PI) * (/ (2* INR (N + 1))) = - (PI * (2 * INR q / 2) + PI) * (/ (2* INR (N + 1))) + 2 * INR q / 2 * PI ). {nra. } rewrite H82.
                destruct H79. assert(2 * INR q / 2 * PI = 2 * INR x * PI). {assert(2 * INR q / 2 * PI = INR q / 2 * 2 * PI). {nra. } rewrite H83. rewrite H79. rewrite mult_INR. assert(INR 2 = 2). {reflexivity. } rewrite H84. nra.  }
                assert(PI * (2 * INR q /2) = 2 * INR q / 2 * PI). {nra. } rewrite H84. rewrite H83.
                rewrite (sin_period (- (2 * INR x * PI + PI) * (/ (2 *INR (N + 1)))) (x)). assert(- (2 * INR x * PI + PI) * (/ (2* INR (N + 1))) = - ((2 * INR x * PI + PI) * (/ (2* INR (N + 1))))). {nra. } rewrite H85.
                rewrite (sin_neg ((2 * INR x * PI + PI) * (/ (2* INR (N + 1))))). nra. }
                rewrite H74. nra.
          } rewrite H74. rewrite <-H67.
            assert ( (INR k * PI -  INR k * PI * / (2 * INR (N + 1)))= (INR k * PI - INR k * PI / (2 * INR (N + 1)))). { nra. } rewrite <-H75. rewrite H73. nra.
            apply Rmult_eq_0_compat_l. apply H14.
Qed.


Lemma Scond:forall (N:nat) (a b:R), (2<N)%nat -> 0<a ->   Mmult (Sm N a b) (Stranspose N a b) = identity N /\  Mmult (Stranspose N a b) (Sm N a b) = identity N.
Proof.
intros.
split.
+ unfold Mmult. unfold identity. 
  apply (mk_matrix_ext N N
             (fun i j : nat => sum_n (fun l : nat =>
                    mult (coeff_mat Hierarchy.zero (Sm N a b) i l)
                      (coeff_mat Hierarchy.zero (Stranspose N a b) l j)) (pred N))
              (fun i j : nat => if i =? j then 1 else 0)).
  intros.
  assert ( i=j \/ i <> j). { omega. } destruct H3.
  - rewrite H3.
    assert ( j =? j =true). { symmetry. apply (beq_nat_refl j). } rewrite H4.
    unfold sum_n.
    assert ( sum_n_m (fun l:nat => (2/INR (N+1)) *sin(((INR l+1)* INR (i+1)*PI) */ INR (N+1)) ^2) 0 (pred N)=1).
    { apply sin_sqr_sum. omega. } rewrite <-H5.
    apply sum_n_m_ext_loc. intros. 
    unfold Stranspose. unfold mat_transpose. 
    assert (coeff_mat Hierarchy.zero
     (mk_matrix N N
        (fun i0 j0 : nat =>
         coeff_mat 0 (Sm N a b) j0 i0)) k j= (fun i0 j0 : nat =>
         coeff_mat 0 (Sm N a b) j0 i0) k j ).
    { apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
                    coeff_mat 0 (Sm N a b) j0 i0) k j). omega. omega. } rewrite H7.
    unfold Sm.
    assert (coeff_mat Hierarchy.zero
                 (mk_matrix N N
                    (fun i0 j0 : nat =>
                     coeff_mat 0 (Eigen_vec j0 N a b a) i0 0))
                 j k= (fun i0 j0 : nat =>
                     coeff_mat 0 (Eigen_vec j0 N a b a) i0 0) j k).
    { apply (coeff_mat_bij Hierarchy.zero  (fun i0 j0 : nat =>
                     coeff_mat 0 (Eigen_vec j0 N a b a) i0 0) j k). omega. omega. } rewrite H8.
    assert (coeff_mat 0
               (mk_matrix N N
                  (fun i0 j0 : nat =>
                   coeff_mat 0 (Eigen_vec j0 N a b a) i0 0))
               j k=   (fun i0 j0 : nat =>
                   coeff_mat 0 (Eigen_vec j0 N a b a) i0 0) j k). 
    { apply (coeff_mat_bij 0 (fun i0 j0 : nat =>
                   coeff_mat 0 (Eigen_vec j0 N a b a) i0 0) j k). omega. omega. } rewrite H9.
    unfold Eigen_vec.
    assert (coeff_mat 0
               (mk_matrix N 1
                  (fun i0 _ : nat =>  sqrt (2 / INR (N + 1))*
                   Rpower (a  * / a )
                     (INR i0 + 1 - 1 * / 2) *
                   sin
                     ((INR i0 + 1) * INR (k + 1) * PI *
                      / INR (N + 1)))) j 0= (fun i0 _ : nat =>  sqrt (2 / INR (N + 1))*
                   Rpower (a  * / a )
                     (INR i0 + 1 - 1 * / 2) *
                   sin
                     ((INR i0 + 1) * INR (k + 1) * PI *
                      / INR (N + 1))) j 0%nat).
   { apply (coeff_mat_bij 0 (fun i0 _ : nat =>  sqrt (2 / INR (N + 1))*
                   Rpower (a  * / a )
                     (INR i0 + 1 - 1 * / 2) *
                   sin
                     ((INR i0 + 1) * INR (k + 1) * PI *
                      / INR (N + 1))) j 0%nat). omega. omega. } rewrite H10.
   assert (Rpower (a  * / a )  (INR j + 1 - 1 * / 2)=1). 
   { assert ( a  * / a =1). { apply Rinv_r.  nra. } rewrite H11. apply rpower_1.  }
   rewrite H11. 
   rewrite H3. 
   assert (sqrt (2 / INR (N + 1)) * 1 * sin  ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1))= sqrt (2 / INR (N + 1)) *sin  ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1))). { nra. } rewrite H12.
   assert (mult
              (sqrt (2 / INR (N + 1)) *
               sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1)))
              (sqrt (2 / INR (N + 1)) *
               sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1)))=  (sqrt (2 / INR (N + 1)) *sqrt (2 / INR (N + 1)))*
               sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1)) *  sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1))). 
   { assert (mult  (sqrt (2 / INR (N + 1)) *  sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1))) 
              (sqrt (2 / INR (N + 1)) *  sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1)))=
              (sqrt (2 / INR (N + 1))* sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1))) * 
              (sqrt (2 / INR (N + 1)) *  sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1)))). { reflexivity. } nra.
   } rewrite H13.
   assert ( sqrt (2 / INR (N + 1)) * sqrt (2 / INR (N + 1))=2 / INR (N + 1)). 
    { apply sqrt_def.  apply Rlt_le. assert ( 2 / INR (N + 1)= 2 * (/ INR (N+1))). { nra. }rewrite H14.
      apply Rmult_lt_0_compat. nra. apply Rinv_0_lt_compat. apply lt_0_INR. omega. } rewrite H14.
  assert (2 / INR (N + 1) *
              sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1)) *
              sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1))= (2 / INR (N + 1)) * 
          (sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1)) *
              sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1)))). { nra. } rewrite H15.
  apply Rmult_eq_compat_l.
   assert (((INR j + 1) * INR (k + 1) * PI *  / INR (N + 1))=
            ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1))). 
   { assert ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1)= ((INR j + 1) * INR (k + 1)) * (PI * / INR (N + 1))). { nra. } rewrite H16.
     assert ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)= ((INR k + 1) * INR (j + 1)) * (PI * / INR (N + 1))). { nra. } rewrite H17.
     apply Rmult_eq_compat_r. assert (INR(k+1) = INR k + INR 1). { apply plus_INR. } rewrite H18. assert ( INR 1 = 1). { reflexivity. } rewrite H19. 
     assert (INR (j+1)= INR j + INR 1). { apply plus_INR. } rewrite H20. assert ( INR 1 =1). { reflexivity. } rewrite H21. apply Rmult_comm.
   } rewrite H16. 
   assert (sin  ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)) ^ 2=
            (sin  ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1))) * (sin  ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)))). { nra. } rewrite H17. reflexivity.
   (* Proof that i <> j **)
  - assert ( i =? j = false ).
    { apply beq_nat_false_iff. apply H3. }
    unfold sum_n.
    assert (sum_n_m (fun l : nat => 0) 0 (pred N) = 0).
    { apply sum_const_zero. intuition. }
    rewrite H4. (* rewrite <- H4. **)
    assert(sum_n_m (fun l:nat => mult(/INR(N+1))(cos((INR (i) - INR(j)) * PI / INR (N + 1) + INR l * (INR(i) - INR(j)) * PI / INR (N + 1)) -
    cos(INR(i+j+2)*PI */ INR(N+1) + INR l * INR(i+j+2)*PI */ INR(N+1)))) 0 (pred N)=0).
    { apply cos_sqr_sum. split.
      - apply H. split.
      - intuition. split.
      - intuition.
      - apply H3. }
    rewrite <- H6.
    apply sum_n_m_ext_loc. intros.
    unfold Stranspose. unfold mat_transpose.
    assert (coeff_mat Hierarchy.zero
       (mk_matrix N N
          (fun i0 j0 : nat =>
           coeff_mat 0 (Sm N a b) j0 i0)) k j = (fun i0 j0 : nat => coeff_mat 0 (Sm N a b) j0 i0) k j).
    { intros. apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat => coeff_mat 0 (Sm N a b) j0 i0) k j). omega. omega. }
    rewrite H8.
    unfold Sm.
    assert (coeff_mat Hierarchy.zero
           (mk_matrix N N (fun i0 j0 : nat => coeff_mat 0 (Eigen_vec j0 N a b a) i0 0)) i k =
            (fun i0 j0 : nat => coeff_mat 0 (Eigen_vec j0 N a b a) i0 0) i k).
    { apply (coeff_mat_bij Hierarchy.zero
    ((fun i0 j0 : nat => coeff_mat 0 (Eigen_vec j0 N a b a) i0 0)) i k). omega. omega. }
    rewrite H9.
    assert (coeff_mat 0 (mk_matrix N N (fun i0 j0 : nat => coeff_mat 0 (Eigen_vec j0 N a b a) i0 0)) j k =
            (fun i0 j0 : nat => coeff_mat 0 (Eigen_vec j0 N a b a) i0 0) j k).
    { apply (coeff_mat_bij 0 ((fun i0 j0 : nat => coeff_mat 0 (Eigen_vec j0 N a b a) i0 0)) j k). omega. omega. }
    rewrite H10.
    unfold Eigen_vec.
    assert (coeff_mat 0
       (mk_matrix N 1
          (fun i0 _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a  * / a ) (INR i0 + 1 - 1 * / 2) *
           sin ((INR i0 + 1) * INR (k + 1) * PI * / INR (N + 1)))) i 0 = (fun i0 _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a  * / a ) (INR i0 + 1 - 1 * / 2) *
           sin ((INR i0 + 1) * INR (k + 1) * PI * / INR (N + 1))) i 0%nat).
    { apply (coeff_mat_bij 0  (fun i0 _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a  * / a ) (INR i0 + 1 - 1 * / 2) *
           sin ((INR i0 + 1) * INR (k + 1) * PI * / INR (N + 1))) i 0%nat). omega. omega. }
    rewrite H11.
    assert (coeff_mat 0
       (mk_matrix N 1
          (fun i0 _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a  * / a ) (INR i0 + 1 - 1 * / 2) *
           sin ((INR i0 + 1) * INR (k + 1) * PI * / INR (N + 1)))) j 0 = (fun i0 _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a  * / a ) (INR i0 + 1 - 1 * / 2) *
           sin ((INR i0 + 1) * INR (k + 1) * PI * / INR (N + 1))) j 0%nat).
    { apply (coeff_mat_bij 0 (fun i0 _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a  * / a ) (INR i0 + 1 - 1 * / 2) *
           sin ((INR i0 + 1) * INR (k + 1) * PI * / INR (N + 1))) j 0%nat). omega. omega. }
    rewrite H12.
    assert (Rpower (a  */ a ) (INR i + 1 -1 */2) = 1). { assert ( a  * / a =1). { apply Rinv_r. nra. } rewrite H13. apply rpower_1.  } rewrite H13.
    assert (Rpower (a  */ a ) (INR j + 1 -1 */2) = 1). { assert ( a  * / a =1). { apply Rinv_r. nra. } rewrite H14. apply rpower_1. } rewrite H14.
    simpl.
    assert(forall A B, mult A B = A * B). { reflexivity. } rewrite H15.
    assert(sqrt (2 / INR (N + 1)) * 1 *
  sin ((INR i + 1) * INR (k + 1) * PI * / INR (N + 1)) *
  (sqrt (2 / INR (N + 1)) * 1 *
   sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1))) = sqrt (2 / INR (N + 1)) *
  sin ((INR i + 1) * INR (k + 1) * PI * / INR (N + 1)) *
  (sqrt (2 / INR (N + 1)) *
   sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1))) ).
    { nra. }
    rewrite H16.
    assert(sqrt (2 / INR (N + 1)) *
  sin ((INR i + 1) * INR (k + 1) * PI * / INR (N + 1)) *
  (sqrt (2 / INR (N + 1)) *
   sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1))) =
          sqrt (2 / INR (N + 1)) * sqrt (2 / INR (N + 1)) *
  sin ((INR i + 1) * INR (k + 1) * PI * / INR (N + 1)) *
   sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1))).
    { nra. } rewrite H17.
    rewrite sqrt_sqrt.
    assert (1 = 1 * 1).
    { nra. } (** rewrite H17. *)
    assert (2 / INR(N+1) * sin ((INR i + 1) * INR (k + 1) * PI * / INR (N + 1)) *
            sin ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1)) =
            /INR(N+1) * (cos((INR i + 1) * INR (k + 1) * PI * / INR (N + 1) - (INR j + 1) * INR (k + 1) * PI * / INR (N + 1)) -
           cos((INR i + 1) * INR (k + 1) * PI * / INR (N + 1) + (INR j + 1) * INR (k + 1) * PI * / INR (N + 1)))).
    remember ((INR i + 1) * INR (k + 1) * PI * / INR (N + 1)) as U.
    remember ((INR j + 1) * INR (k + 1) * PI * / INR (N + 1)) as V.
    { assert(Hc:2/INR(N+1)*sin U * sin V = 2 * sin U * sin V */INR(N+1)). {nra. } rewrite Hc. rewrite (sinA_sinB 2 U V). nra. } rewrite H19.
    assert (cos ((INR (i + 1)) * INR (k + 1) * PI * / INR (N + 1) -
     (INR (j + 1)) * INR (k + 1) * PI * / INR (N + 1)) = cos(INR(k)*(INR(i)-INR(j))*PI / INR(N+1) + (INR(i)-INR(j))*PI / INR(N+1))).
    { intros. assert(INR (i + 1) * INR (k + 1) * PI * / INR (N + 1) -
                                         INR (j + 1) * INR (k + 1) * PI * / INR (N + 1) = (INR (k + 1) * PI * / INR (N + 1))*(INR(i+1)-INR(j+1))). { nra. } rewrite H20.
      assert((INR(i+1)-INR(j+1) = INR(i)-INR(j))). rewrite plus_INR. rewrite plus_INR. assert(INR 1 = 1). { reflexivity. } rewrite H21.
      assert(INR i + 1 - (INR j + 1) = INR i - INR j). { nra. } rewrite H22. reflexivity. rewrite H21. rewrite plus_INR. assert(INR 1 = 1). { reflexivity. } rewrite H22. 
      assert((INR k + 1) * PI * / INR (N + 1) * (INR(i) - INR(j)) =
              INR k * (INR(i) - INR(j)) * PI / INR (N + 1) +
              (INR(i) - INR(j)) * PI / INR (N + 1)). { nra. } rewrite H23. reflexivity. } assert(INR 1 = 1). { reflexivity. } rewrite <- H21. 
    rewrite <- plus_INR.
    rewrite <- plus_INR. rewrite H20.
    assert(INR k * (INR(i) - INR(j)) * PI / INR (N + 1) +
     (INR(i) - INR(j)) * PI / INR (N + 1) = (INR(i) - INR(j)) * PI / INR (N + 1) +
     INR k * (INR(i) - INR(j)) * PI / INR (N + 1)).
    { nra. } rewrite H22.
    assert(cos
    (INR (i + 1) * INR (k + 1) * PI * / INR (N + 1) +
     INR (j + 1) * INR (k + 1) * PI * / INR (N + 1)) = cos
    (INR (i + j + 2) * PI * / INR (N + 1) +
     INR k * INR (i + j + 2) * PI * / INR (N + 1))).
    { intros. assert((INR i + INR 1) * INR (k + 1) * PI * / INR (N + 1) +
                                                               (INR j + INR 1) * INR (k + 1) * PI * / INR (N + 1) = INR (k + 1) * PI * / INR (N + 1) * (INR(i+1)+INR(j+1))).
      { rewrite <- plus_INR. rewrite <- plus_INR. nra. } rewrite plus_INR. rewrite (plus_INR j 1). rewrite H23.
      assert(INR(i+1)+INR(j+1) = INR(i+j+2)). rewrite (plus_INR i 1). rewrite (plus_INR j 1). rewrite H21.
      assert(INR i + 1 + (INR j + 1) = INR i + INR j + 2). { nra. } rewrite H24. assert(2 = INR 2). { intuition. } rewrite H25.
      rewrite <- plus_INR. rewrite <- plus_INR. reflexivity. rewrite H24.
      assert(INR (k + 1) * PI * / INR (N + 1) * INR (i + j + 2) = INR (i + j + 2) * PI * / INR (N + 1) +
                                                                  INR k * INR (i + j + 2) * PI * / INR (N + 1)). rewrite plus_INR. rewrite H21.
      assert(INR (k + 1) * PI * / INR (N + 1) * INR (i + j + 2) = INR k * INR (i + j + 2) * PI * / INR (N + 1) + INR (i + j + 2) * PI * / INR (N + 1)).
      {rewrite plus_INR. rewrite H21. nra. } rewrite <- H21. rewrite <- plus_INR. rewrite H25.
      assert(INR k * INR (i + j + 2) * PI * / INR (N + 1) +
  INR (i + j + 2) * PI * / INR (N + 1) = INR (i + j + 2) * PI * / INR (N + 1) +
  INR k * INR (i + j + 2) * PI * / INR (N + 1)). { nra. } rewrite H26. reflexivity. rewrite H25. reflexivity. }
    rewrite H23. assert(Hmult:forall A B, mult A B = A * B). {reflexivity. } rewrite <- Hmult. reflexivity.
    apply Rlt_le. assert(2 / INR(N+1) = 2 */ INR(N+1)). { nra. } rewrite H18. assert(0=2*0). { nra. } rewrite H19.
    assert(0<2). { nra. } assert(0</INR(N+1)). { apply Rinv_0_lt_compat. apply lt_0_INR. omega. }
    apply Rmult_lt_compat_l. apply H20. apply H21.
    (***)

+ unfold Mmult. unfold identity.
  apply (mk_matrix_ext N N  (fun i j : nat =>
             sum_n
               (fun l : nat =>
                mult
                  (coeff_mat Hierarchy.zero 
                     (Stranspose N a b) i l)
                  (coeff_mat Hierarchy.zero (Sm N a b) l j))
               (pred N))(fun i j : nat => if i =? j then 1 else 0)).
  intros. 
  assert ( i=j \/ (i<>j)). { omega. }
  destruct H3.
  - rewrite H3.
    assert (j =? j=true). { symmetry. apply (beq_nat_refl j). } rewrite H4.
     assert (sum_n_m (fun l:nat => (2/ INR (N+1))*sin(((INR l+1)* INR (i+1)*PI) */ INR (N+1)) ^2) 0 (pred N)=1). 
      { apply sin_sqr_sum. omega. } rewrite <- H5. 
     apply sum_n_m_ext_loc. intros.
     unfold Stranspose. unfold mat_transpose.
     assert (coeff_mat Hierarchy.zero
                 (mk_matrix N N
                    (fun i0 j0 : nat =>
                     coeff_mat 0 (Sm N a b) j0 i0))
                 j k= (fun i0 j0 : nat =>
                     coeff_mat 0 (Sm N a b) j0 i0) j k).
     { apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
                     coeff_mat 0 (Sm N a b) j0 i0) j k). omega. omega. } rewrite H7.
     unfold Sm.
     assert (coeff_mat 0
                 (mk_matrix N N
                    (fun i0 j0 : nat =>
                     coeff_mat 0
                       (Eigen_vec j0 N a b a) i0 0))
                 k j=  (fun i0 j0 : nat =>
                     coeff_mat 0
                       (Eigen_vec j0 N a b a) i0 0) k j).
     { apply (coeff_mat_bij 0 (fun i0 j0 : nat =>
                     coeff_mat 0
                       (Eigen_vec j0 N a b a) i0 0) k j). omega. omega. } rewrite H8.
      assert (coeff_mat Hierarchy.zero
                 (mk_matrix N N
                    (fun i0 j0 : nat =>
                     coeff_mat 0
                       (Eigen_vec j0 N a b a) i0 0))
                 k j= (fun i0 j0 : nat =>
                     coeff_mat 0
                       (Eigen_vec j0 N a b a) i0 0) k j).
      { apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat =>
                     coeff_mat 0
                       (Eigen_vec j0 N a b a) i0 0) k j). omega. omega. } rewrite H9.
      unfold Eigen_vec.
      assert (coeff_mat 0
                 (mk_matrix N 1
                    (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                     Rpower (a  * / a )
                       (INR i0 + 1 - 1 * / 2) *
                     sin
                       ((INR i0 + 1) *
                        INR (j + 1) * PI *
                        / INR (N + 1)))) k 0=(fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                     Rpower (a  * / a )
                       (INR i0 + 1 - 1 * / 2) *
                     sin
                       ((INR i0 + 1) *
                        INR (j + 1) * PI *
                        / INR (N + 1))) k 0%nat).
      { apply (coeff_mat_bij 0 (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                     Rpower (a  * / a )
                       (INR i0 + 1 - 1 * / 2) *
                     sin
                       ((INR i0 + 1) *
                        INR (j + 1) * PI *
                        / INR (N + 1))) k 0%nat). omega. omega. } rewrite H10.
      assert (Rpower (a  * / a ) (INR k + 1 - 1 * / 2)=1). { assert ( a  * / a =1). { apply Rinv_r. nra. } rewrite H11. apply rpower_1.  } rewrite H11.
      assert (sqrt (2 / INR (N + 1)) * 1 * sin  ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1))= sqrt (2 / INR (N + 1)) *sin  ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1))). { nra. } rewrite H12.
     assert (mult
                (sqrt (2 / INR (N + 1)) *
                 sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)))
                (sqrt (2 / INR (N + 1)) *
                 sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)))=  (sqrt (2 / INR (N + 1)) *sqrt (2 / INR (N + 1)))*
                 sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)) *  sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1))). 
     { assert (mult  (sqrt (2 / INR (N + 1)) *  sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1))) 
                (sqrt (2 / INR (N + 1)) *  sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)))=
                (sqrt (2 / INR (N + 1))* sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1))) * 
                (sqrt (2 / INR (N + 1)) *  sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)))). { reflexivity. } nra.
     } rewrite H13.
     assert ( sqrt (2 / INR (N + 1)) * sqrt (2 / INR (N + 1))=2 / INR (N + 1)). 
    { apply sqrt_def.  apply Rlt_le. assert ( 2 / INR (N + 1)= 2 * (/ INR (N+1))). { nra. }rewrite H14.
        apply Rmult_lt_0_compat. nra. apply Rinv_0_lt_compat. apply lt_0_INR. omega. } rewrite H14.
    assert (2 / INR (N + 1) *
                sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)) *
                sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1))= (2 / INR (N + 1)) * 
            (sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)) *
                sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)))). { nra. } rewrite H15.
    apply Rmult_eq_compat_l.
     assert (((INR k + 1) * INR (j + 1) * PI *  / INR (N + 1))=
              ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1))). 
     { assert ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)= ((INR k + 1) * INR (j + 1)) * (PI * / INR (N + 1))). { nra. } rewrite H16.
       assert ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)= ((INR k + 1) * INR (j + 1)) * (PI * / INR (N + 1))). { nra. } reflexivity. } simpl. rewrite H3. nra.

   -  assert(i=?j = false). { apply beq_nat_false_iff. apply H3. } unfold sum_n.
      rewrite H4.
      assert(sum_n_m (fun l:nat => mult(/INR(N+1)) (cos((INR (i) - INR(j)) * PI / INR (N + 1) + INR l * (INR(i) - INR(j)) * PI / INR (N + 1)) -
      cos(INR(i+j+2)*PI */ INR(N+1) + INR l * INR(i+j+2)*PI */ INR(N+1)))) 0 (pred N)=0).
      { apply cos_sqr_sum. split.
        - apply H.
        - intuition. }
      rewrite <- H5.
      apply sum_n_m_ext_loc. intros.
      unfold Stranspose. unfold mat_transpose.
      assert(coeff_mat Hierarchy.zero (mk_matrix N N (fun i0 j0 : nat => coeff_mat 0 (Sm N a b) j0 i0)) i k =
            (fun i0 j0 : nat => coeff_mat 0 (Sm N a b) j0 i0) i k).
      { intros. apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat => coeff_mat 0 (Sm N a b) j0 i0) i k). omega. omega. } rewrite H7.
      unfold Sm.
      assert(coeff_mat 0 (mk_matrix N N (fun i0 j0 : nat => coeff_mat 0 (Eigen_vec j0 N a b a) i0 0)) k i =
            (fun i0 j0 : nat => coeff_mat 0 (Eigen_vec j0 N a b a) i0 0) k i).
      { intros. apply (coeff_mat_bij 0 (fun i0 j0 : nat => coeff_mat 0 (Eigen_vec j0 N a b a) i0 0) k i). omega. omega. } rewrite H8.
      assert(coeff_mat Hierarchy.zero (mk_matrix N N (fun i0 j0 : nat => coeff_mat 0 (Eigen_vec j0 N a b a) i0 0)) k j =
             (fun i0 j0 : nat => coeff_mat 0 (Eigen_vec j0 N a b a) i0 0) k j).
      { intros. apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat => coeff_mat 0 (Eigen_vec j0 N a b a) i0 0) k j). omega. omega. } rewrite H9.
      unfold Eigen_vec.
      assert(coeff_mat 0
       (mk_matrix N 1
          (fun i0 _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a  * / a ) (INR i0 + 1 - 1 * / 2) *
           sin ((INR i0 + 1) * INR (i + 1) * PI * / INR (N + 1)))) k 0 =
          (fun i0 _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a  * / a ) (INR i0 + 1 - 1 * / 2) *
           sin ((INR i0 + 1) * INR (i + 1) * PI * / INR (N + 1))) k 0%nat).
      { intros. apply (coeff_mat_bij 0 (fun i0 _ : nat =>
        sqrt (2 / INR (N + 1)) * Rpower (a  * / a ) (INR i0 + 1 - 1 * / 2) *
        sin ((INR i0 + 1) * INR (i + 1) * PI * / INR (N + 1))) k 0%nat). omega. omega. } rewrite H10.
      assert(coeff_mat 0
       (mk_matrix N 1
          (fun i0 _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a  * / a ) (INR i0 + 1 - 1 * / 2) *
           sin ((INR i0 + 1) * INR (j + 1) * PI * / INR (N + 1)))) k 0 =
          (fun i0 _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a  * / a ) (INR i0 + 1 - 1 * / 2) *
           sin ((INR i0 + 1) * INR (j + 1) * PI * / INR (N + 1))) k 0%nat).
      { intros. apply (coeff_mat_bij 0 (fun i0 _ : nat =>
        sqrt (2 / INR (N + 1)) * Rpower (a  * / a ) (INR i0 + 1 - 1 * / 2) *
        sin ((INR i0 + 1) * INR (j + 1) * PI * / INR (N + 1))) k 0%nat). omega. omega. } rewrite H11.
      assert(Rpower (a  * / a ) (INR k + 1 - 1 * / 2) = 1). { assert ( a  * / a =1). { apply Rinv_r. nra. } rewrite H12. apply rpower_1.  } rewrite H12.
      simpl. assert(forall A B, mult A B = A * B). { reflexivity. } rewrite H13.
      assert(sqrt (2 / INR (N + 1)) * 1 * sin ((INR k + 1) * INR (i + 1) * PI * / INR (N + 1)) *
             (sqrt (2 / INR (N + 1)) * 1 * sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1))) =
            sqrt (2 / INR (N + 1)) * sqrt ( 2 / INR(N+1) ) * sin ((INR k + 1) * INR (i + 1) * PI * / INR (N + 1)) *
            (sin ((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)))).
      { nra. } rewrite H14.
      rewrite sqrt_sqrt.
      assert(1 = 1 * 1).
      { nra. } (*rewrite H14.**)
      remember((INR k + 1) * INR (i + 1) * PI * / INR (N + 1)) as U.
      remember((INR k + 1) * INR (j + 1) * PI * / INR (N + 1)) as V.
      assert(2/INR(N+1) * sin U * sin V = /INR(N+1) * (cos(U-V) - cos(U+V))).
      { assert(Hc:2 / INR (N + 1) * sin U * sin V = 2 * sin U * sin V * /INR(N+1)). {nra. } rewrite Hc. rewrite (sinA_sinB 2 U V). assert(2 */ 2 = 1). { nra. } rewrite H16. nra. } rewrite H16. rewrite HeqU. rewrite HeqV.
      assert (cos ((INR (i + 1)) * INR (k + 1) * PI * / INR (N + 1) -
     (INR (j + 1)) * INR (k + 1) * PI * / INR (N + 1)) = cos(INR(k)*(INR(i)-INR(j))*PI / INR(N+1) + (INR(i)-INR(j))*PI / INR(N+1))).
    { intros. assert(INR (i + 1) * INR (k + 1) * PI * / INR (N + 1) -
                                         INR (j + 1) * INR (k + 1) * PI * / INR (N + 1) = (INR (k + 1) * PI * / INR (N + 1))*(INR(i+1)-INR(j+1))). { nra. } rewrite H17.
      assert((INR(i+1)-INR(j+1) = INR(i)-INR(j))). rewrite plus_INR. rewrite plus_INR. assert(INR 1 = 1). { reflexivity. } rewrite H18.
      assert(INR i + 1 - (INR j + 1) = INR i - INR j). { nra. } rewrite H19. reflexivity. rewrite H18. rewrite plus_INR. assert(INR 1 = 1). { reflexivity. } rewrite H19.
   assert((INR k + 1) * PI * / INR (N + 1) * (INR(i) - INR(j)) =
    INR k * (INR(i) - INR(j)) * PI / INR (N + 1) +
    (INR(i) - INR(j)) * PI / INR (N + 1)). { nra. } rewrite H20. reflexivity. } assert(INR 1 = 1). { reflexivity. } rewrite <- H18. rewrite <- plus_INR.
    rewrite plus_INR. assert((INR k + INR 1) * INR (i + 1) * PI * / INR (N + 1) -
     (INR k + INR 1) * INR (j + 1) * PI * / INR (N + 1) = INR (i + 1) * INR(k + 1) * PI * / INR (N + 1) -
     INR (j + 1) * INR(k + 1) * PI * / INR (N + 1)).
    { rewrite H18. assert(INR k + 1 = INR(k+1)). { rewrite <- H18. intuition. } rewrite H19. nra. }
    assert(Hf1:INR(k+1) = INR k + INR 1). {apply plus_INR. } rewrite Hf1.
    assert(Hf2:INR N + INR 1 = INR(N+1)). {rewrite plus_INR. reflexivity. } rewrite Hf2.
    rewrite H19. rewrite H17.
    assert(INR k * (INR(i) - INR(j)) * PI / INR (N + 1) +
     (INR(i) - INR(j)) * PI / INR (N + 1) = (INR(i) - INR(j)) * PI / INR (N + 1) +
     INR k * (INR(i) - INR(j)) * PI / INR (N + 1)).
    { nra. } rewrite H20.
    assert(cos
    (INR (i + 1) * INR (k + 1) * PI * / INR (N + 1) +
     INR (j + 1) * INR (k + 1) * PI * / INR (N + 1)) = cos
    (INR (i + j + 2) * PI * / INR (N + 1) +
     INR k * INR (i + j + 2) * PI * / INR (N + 1))).
    { intros. assert((INR i + INR 1) * INR (k + 1) * PI * / INR (N + 1) +
                                                               (INR j + INR 1) * INR (k + 1) * PI * / INR (N + 1) = INR (k + 1) * PI * / INR (N + 1) * (INR(i+1)+INR(j+1))).
      { rewrite <- plus_INR. rewrite <- plus_INR. nra. } rewrite plus_INR. rewrite (plus_INR j 1). rewrite H21.
      assert(INR(i+1)+INR(j+1) = INR(i+j+2)). rewrite (plus_INR i 1). rewrite (plus_INR j 1). rewrite H18.
      assert(INR i + 1 + (INR j + 1) = INR i + INR j + 2). { nra. } rewrite H22. assert(2 = INR 2). { intuition. } rewrite H23.
      rewrite <- plus_INR. rewrite <- plus_INR. reflexivity. rewrite H22.
      assert(INR (k + 1) * PI * / INR (N + 1) * INR (i + j + 2) = INR (i + j + 2) * PI * / INR (N + 1) +
                                                                  INR k * INR (i + j + 2) * PI * / INR (N + 1)). rewrite plus_INR. rewrite H18.
      assert(INR (k + 1) * PI * / INR (N + 1) * INR (i + j + 2) = INR k * INR (i + j + 2) * PI * / INR (N + 1) + INR (i + j + 2) * PI * / INR (N + 1)).
      {rewrite plus_INR. rewrite H18. nra. } rewrite <- H18. rewrite <- plus_INR. rewrite H23.
      assert(INR k * INR (i + j + 2) * PI * / INR (N + 1) +
  INR (i + j + 2) * PI * / INR (N + 1) = INR (i + j + 2) * PI * / INR (N + 1) +
  INR k * INR (i + j + 2) * PI * / INR (N + 1)). { nra. } rewrite H24. reflexivity. rewrite H23. reflexivity. }
    assert(INR k + 1 = INR(k+1)). { rewrite <- H18. intuition. } rewrite H18. rewrite H22.
    assert(INR (k + 1) * INR (i + 1) * PI * / INR (N + 1) + INR (k + 1) * INR (j + 1) * PI * / INR (N + 1) =
           INR (i + 1) * INR(k+1) * PI * / INR (N + 1) + INR (j + 1) * INR(k+1) * PI * / INR (N + 1)).
    { nra. } rewrite H23. rewrite H21. reflexivity.
      apply Rlt_le. assert(2 / INR(N+1) = 2 */ INR(N+1)). { nra. } rewrite H15. assert(0=2*0). { nra. } rewrite H16.
      assert(0<2). { nra. } assert(0</INR(N+1)). { apply Rinv_0_lt_compat. apply lt_0_INR. omega. }
      apply Rmult_lt_compat_l. apply H17. apply H18.
Qed.


Lemma eigen_vec_col (a b:R) : forall (j N:nat) , (2<N)%nat -> (j<N)%nat -> (Mmult (Ah N a b a) (A_col j N (Sm N a b)))= LHS j N a b a.
Proof.
intros. unfold LHS.
assert ((A_col j N (Sm N a b))= (Eigen_vec j N a b a)).
{ unfold A_col. unfold Eigen_vec.
  apply (mk_matrix_ext N 1%nat  (fun i _ : nat => coeff_mat 0 (Sm N a b) i j) (fun i _ : nat =>sqrt (2 / INR (N + 1)) *
             Rpower (a  * / a ) (INR i + 1 - 1 * / 2) *
             sin ((INR i + 1) * INR (j+1) * PI * / INR (N + 1)))).
  intros.
  unfold Sm.
  assert (coeff_mat 0
              (mk_matrix N N
                 (fun i0 j1 : nat =>
                  coeff_mat 0 (Eigen_vec j1 N a b a) i0 0%nat))
              i j = (fun i0 j1 : nat =>
                  coeff_mat 0 (Eigen_vec j1 N a b a) i0 0%nat) i j).
  { apply (coeff_mat_bij 0 (fun i0 j1 : nat =>
                  coeff_mat 0 (Eigen_vec j1 N a b a) i0 0%nat) i j). omega. omega. } rewrite H3.
  unfold Eigen_vec.
  assert (coeff_mat 0
            (mk_matrix N 1
               (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                Rpower (a  * / a )
                  (INR i0 + 1 - 1 * / 2) *
                sin
                  ((INR i0 + 1) * INR (j+1) * PI *
                   / INR (N + 1)))) i 0 =  (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                Rpower (a  * / a )
                  (INR i0 + 1 - 1 * / 2) *
                sin
                  ((INR i0 + 1) * INR (j+1) * PI *
                   / INR (N + 1))) i 0%nat).
  { apply (coeff_mat_bij 0 (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                Rpower (a  * / a )
                  (INR i0 + 1 - 1 * / 2) *
                sin
                  ((INR i0 + 1) * INR (j+1) * PI *
                   / INR (N + 1))) i 0%nat). omega. omega. }
  rewrite H4. reflexivity.
} rewrite H1. reflexivity.
Qed.

Lemma eigen_prop_1 (a b:R): forall (j N:nat),  (j<N)%nat -> A_col j N (Lam N a b) = Mmult (single_elem_vec j N) (Lambda j N a b a).
Proof.
intros.
unfold A_col. unfold Mmult.
apply (mk_matrix_ext N 1%nat (fun i _ : nat => coeff_mat 0 (Lam N a b) i j) (fun i j0 : nat =>
   sum_n
     (fun l : nat =>
      mult
        (coeff_mat Hierarchy.zero
           (single_elem_vec j N) i l)
        (coeff_mat Hierarchy.zero 
           (Lambda j N a b a) l j0)) 
     (pred 1))).
intros.
unfold Lam.
assert (coeff_mat 0
            (mk_matrix N N
               (fun i0 j1 : nat =>
                if i0 =? j1
                then coeff_mat 0 (Lambda i0 N a b a) 0 0
                else 0)) i j = (fun i0 j1 : nat =>
                if i0 =? j1
                then coeff_mat 0 (Lambda i0 N a b a) 0 0
                else 0) i j).
{ apply (coeff_mat_bij 0 (fun i0 j1 : nat =>
                if i0 =? j1
                then coeff_mat 0 (Lambda i0 N a b a) 0 0
                else 0) i j). omega. omega. } rewrite H2. 
assert ( i= j \/ (i<>j)). { omega. } destruct H3.
+ rewrite H3.
  assert (j =? j= true). { symmetry. apply (beq_nat_refl j). } rewrite H4.
  assert (pred 1 = 0%nat). { omega. } rewrite H5. unfold sum_n.
  assert (sum_n_m
            (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (single_elem_vec j N) j l)
               (coeff_mat Hierarchy.zero (Lambda j N  a b a) l j0)) 0 0=  (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (single_elem_vec j N) j l)
               (coeff_mat Hierarchy.zero (Lambda j N a b a) l j0)) 0%nat).
  { apply (sum_n_n (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (single_elem_vec j N) j l)
               (coeff_mat Hierarchy.zero (Lambda j N a b a) l j0)) 0%nat). } rewrite H6.
  assert (j0=0%nat). { omega. } rewrite H7.
  assert ((coeff_mat Hierarchy.zero (single_elem_vec j N) j 0)=1).
  { unfold single_elem_vec.
    assert (coeff_mat Hierarchy.zero
              (mk_matrix N 1
                 (fun i0 _ : nat => if i0 =? j then 1 else 0)) j 0 =  
                (fun i0 _ : nat => if i0 =? j then 1 else 0) j 0%nat).
    { apply (coeff_mat_bij  Hierarchy.zero (fun i0 _ : nat => if i0 =? j then 1 else 0) j 0%nat). omega. omega. }
    rewrite H8. rewrite H4. nra.
  } rewrite H8. 
  assert (mult 1 (coeff_mat Hierarchy.zero (Lambda j N a b a) 0 0)= (coeff_mat Hierarchy.zero (Lambda j N a b a) 0 0)).
  { apply (mult_one_l (coeff_mat Hierarchy.zero (Lambda j N a b a) 0 0)). } rewrite H9. reflexivity.
+ assert (i =? j =false). { assert ((i =? j) = false <-> i <> j). { apply (beq_nat_false_iff i j). } destruct H4. apply H5. omega. }
  rewrite H4. 
  assert (pred 1= 0%nat). { omega. } rewrite H5. unfold sum_n.
  assert (sum_n_m
            (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (single_elem_vec j N) i l)
               (coeff_mat Hierarchy.zero (Lambda j N a b a) l j0)) 0 0=  (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (single_elem_vec j N) i l)
               (coeff_mat Hierarchy.zero (Lambda j N a b a) l j0)) 0%nat).
  { apply (sum_n_n (fun l : nat =>
             mult
               (coeff_mat Hierarchy.zero (single_elem_vec j N) i l)
               (coeff_mat Hierarchy.zero (Lambda j N a b a) l j0)) 0%nat). } rewrite H6.
  assert ((coeff_mat Hierarchy.zero (single_elem_vec j N) i 0)=0).
  { unfold single_elem_vec.
    assert (coeff_mat Hierarchy.zero
                (mk_matrix N 1
                   (fun i0 _ : nat => if i0 =? j then 1 else 0)) i 0 = (fun i0 _ : nat => if i0 =? j then 1 else 0) i 0%nat).
    { apply (coeff_mat_bij  Hierarchy.zero (fun i0 _ : nat => if i0 =? j then 1 else 0) i 0%nat). omega. omega. } rewrite H7.
    rewrite H4. nra.
  } rewrite H7. symmetry. apply (mult_zero_l (coeff_mat Hierarchy.zero (Lambda j N a b a) 0 j0)).
Qed.

Lemma lambda_vec_col (a b:R): forall (j N:nat), (2<N)%nat -> (j<N)%nat -> Mmult (Sm N a b) (A_col j N (Lam N a b)) =RHS j N a b a.
Proof.
intros.
unfold RHS. 
assert ( (A_col j N (Lam N a b))= Mmult (single_elem_vec j N) (Lambda j N a b a)).
{ apply eigen_prop_1. omega. } rewrite H1.
assert ( Mmult (Sm N a b) (Mmult (single_elem_vec j N) (Lambda j N a b a))= 
          Mmult (Mmult (Sm N a b) (single_elem_vec j N)) (Lambda j N a b a)).
{ apply Mmult_assoc. } rewrite H2.
assert ( Mmult (Sm N a b) (single_elem_vec j N)= A_col j N (Sm N a b)). { apply linear_prop_2. omega. } 
rewrite H3.
assert (A_col j N (Sm N a b)= Eigen_vec j N a b a).
{ unfold A_col. unfold Eigen_vec.
  apply (mk_matrix_ext N 1%nat  (fun i _ : nat => coeff_mat 0 (Sm N a b) i j)  (fun i _ : nat =>sqrt (2 / INR (N + 1)) *
               Rpower (a  * / a )
                 (INR i + 1 - 1 * / 2) *
               sin
                 ((INR i + 1) * INR (j+1) * PI * / INR (N + 1)))).
  intros. unfold Sm.
  assert (coeff_mat 0
              (mk_matrix N N
                 (fun i0 j1 : nat =>
                  coeff_mat 0 (Eigen_vec j1 N a b a) i0 0)) i j= (fun i0 j1 : nat =>
                  coeff_mat 0 (Eigen_vec j1 N a b a) i0 0) i j).
  { apply (coeff_mat_bij 0 (fun i0 j1 : nat =>
                  coeff_mat 0 (Eigen_vec j1 N a b a) i0 0) i j). omega. omega. } rewrite H6. 
    unfold Eigen_vec.
    assert (coeff_mat 0
                (mk_matrix N 1
                   (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                    Rpower (a  * / a )
                      (INR i0 + 1 - 1 * / 2) *
                    sin
                      ((INR i0 + 1) * INR (j+1) * PI *
                       / INR (N + 1)))) i 0 = (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                    Rpower (a  * / a )
                      (INR i0 + 1 - 1 * / 2) *
                    sin
                      ((INR i0 + 1) * INR (j+1) * PI *
                       / INR (N + 1))) i 0%nat).
    { apply (coeff_mat_bij 0 (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                    Rpower (a  * / a )
                      (INR i0 + 1 - 1 * / 2) *
                    sin
                      ((INR i0 + 1) * INR (j+1) * PI *
                       / INR (N + 1))) i 0%nat). omega. omega. } rewrite H7.
    reflexivity.
  } rewrite H4. reflexivity.
Qed.

(*Proof that AS= S \Lambda *)


Lemma eigen_mat (a b:R): forall (N:nat), (2<N)%nat -> 0<a -> Mmult (Ah N a b a) (Sm N a b) = Mmult (Sm N a b) (Lam N a b).
Proof.
intros.
assert (Mmult (Ah N a b a) (Sm N a b) =  mk_matrix N N (fun i j => coeff_mat 0 (Mmult (Ah N a b a) (A_col j N (Sm N a b))) i 0%nat)).
{ apply linear_prop_1. } 
assert (Mmult (Sm N a b) (Lam N a b) =  mk_matrix N N (fun i j => coeff_mat 0 (Mmult (Sm N a b) (A_col j N (Lam N a b))) i 0%nat)).
{ apply linear_prop_1. }
rewrite H1. rewrite H2.
apply (mk_matrix_ext N N (fun i j : nat =>
   coeff_mat 0
     (Mmult (Ah N a b a) (A_col j N (Sm N a b))) i 0)(fun i j : nat =>
   coeff_mat 0
     (Mmult (Sm N a b) (A_col j N (Lam N a b))) i 0)).
intros.
apply coeff_mat_ext.
assert (Mmult (Ah N a b a) (A_col j N (Sm N a b)) = LHS j N a b a). { apply eigen_vec_col. omega. omega. } rewrite H5. 
assert (Mmult (Sm N a b) (A_col j N (Lam N a b)) = RHS j N a b a). { apply lambda_vec_col. omega. omega. } rewrite H6.
apply eigen_belongs. omega. omega. split. nra. nra.
Qed.

(* Proof that A = S \Lambda S^{T} *)
Lemma A_decompose(a b:R): forall (N:nat), (2< N)%nat -> 0<a -> Ah N a b a = Mmult (Sm N a b) (Mmult (Lam N a b) (Stranspose N a b)).
Proof.
intros.
assert ( Mmult (identity N) (Ah N a b a) = (Ah N a b a) /\ Mmult (Ah N a b a) (identity N)= Ah N a b a). { apply iden_mat_prop. } destruct H1.
rewrite <-H2. 
assert ( Mmult (Sm N a b) (Stranspose N a b) = identity N /\  Mmult (Stranspose N a b) (Sm N a b) = identity N). { apply Scond. omega. nra. }
destruct H3. rewrite <- H3. 
assert (Mmult (Ah N a b a) (Mmult (Sm N a b) (Stranspose N a b))= Mmult (Mmult (Ah N a b a) (Sm N a b)) (Stranspose N a b)). { apply Mmult_assoc. } rewrite H5.
assert (Mmult (Sm N a b) (Mmult (Lam N a b) (Stranspose N a b))= Mmult (Mmult (Sm N a b)(Lam N a b))  (Stranspose N a b)). { apply Mmult_assoc. } rewrite H6.
assert ((Mmult (Ah N a b a) (Sm N a b))= (Mmult (Sm N a b) (Lam N a b))). 
{ apply eigen_mat. omega. nra. }
rewrite H7. reflexivity.
Qed.
