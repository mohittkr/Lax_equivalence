
(**** Defining the eigen system of the matrix Ah (a, b, c) and verifying that the eigenvalue - eigen vector pair 
    belong to the spectrum of Ah. From here on we choose to work with symmetric tridiagonal matrix Ah (a, b, a).
*****************************************************************************************************************)


Require Import Reals Psatz.
Require Import Coquelicot.Hierarchy.
Require Import Omega Init.Nat Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import R_sqrt Rpower.
Require Import Ah_properties.
Require Import obvio_lemmas.


(*** Analytical expression for the eigen vector of Ah (a,b, c) *******)
Definition Eigen_vec (m N:nat) (a b c:R):= mk_matrix N 1%nat
                        (fun i j => sqrt ( 2 / INR (N+1))*(Rpower (a */c) (INR i +1 -1*/2))* sin(((INR i +1)*INR(m+1)*PI)*/INR (N+1))).

(*** Analytica; expression for the eigen value of Ah(a,b,c *****************)
Definition Lambda (m N:nat) (a b c:R):= mk_matrix 1%nat 1%nat
                         (fun i j => b + 2* sqrt(a*c)* cos ( (INR (m+1) * PI)*/INR(N+1))).

Definition LHS (m N:nat) (a b c:R) := Mmult (Ah N a b c ) (Eigen_vec m N a b c ).
Definition RHS (m N:nat) (a b c:R):= Mmult (Eigen_vec m N a b c ) (Lambda m N a b c ).


(******* We next verify that that LHS = RHS for the symmetric tridiagonal system Ah (a, b, a )****)

Lemma rpower_1 : forall x:R, Rpower 1 x =1.
Proof.
intros.
unfold Rpower.
assert (ln 1=0). { apply ln_1. } rewrite H.
assert (x * 0 = 0). { nra. } rewrite H0. 
assert (ln 1=0). { apply ln_1. } rewrite <- H1. apply exp_ln. nra.
Qed.

(* Trigonometric lemmas *)

Lemma trigo_1: forall x y:R, sin (x-y)+sin(x+y)=2*sin x*cos y.
Proof.
intros.
assert (sin (x-y)= sin x * cos y - cos x * sin y). { apply sin_minus. }
assert (sin (x+y) = sin x * cos y + cos x * sin y). { apply sin_plus. }
rewrite H. rewrite H0. nra.
Qed.

Lemma trigo_2 (c:R): forall m N:nat, (2<N)%nat -> (0<=m<N)%nat ->
mult c (sin (1 * INR (m+1) * PI * / INR (N + 1))) +
mult c (sin (3 * INR (m+1) * PI * / INR (N + 1))) =
2 * c  * sin (2 * INR (m+1) * PI * / INR (N + 1)) *
cos (1 * INR (m+1) * PI * / INR (N + 1)).
Proof.
intros.
assert (3= 2+1). { nra. } rewrite H1. 
assert ((sin (1 * INR (m+1) * PI * / INR (N + 1)))=(sin ((2-1) * INR (m+1) * PI * / INR (N + 1)))).
{ assert ((1 * INR (m+1) * PI * / INR (N + 1)) = (2-1)*INR (m+1) * PI * / INR (N + 1)).
  { apply Rmult_eq_compat_r. apply Rmult_eq_compat_r. apply Rmult_eq_compat_r. nra. }
rewrite H2. reflexivity. } rewrite H2.
assert (mult c (sin ((2 - 1) * INR (m+1) * PI * / INR (N + 1))) +
            mult c (sin ((2 + 1) * INR (m+1) * PI * / INR (N + 1)))= c*
          (sin ((2 - 1) * INR (m+1) * PI * / INR (N + 1))+sin ((2 + 1) * INR (m+1) * PI * / INR (N + 1)))).
{ symmetry. 
  apply (mult_distr_l c (sin ((2 - 1) * INR (m+1) * PI * / INR (N + 1))) (sin ((2 + 1) * INR (m+1) * PI * / INR (N + 1)))). }
rewrite H3.
cut((sin ((2 - 1) * INR (m+1) * PI * / INR (N + 1)) + sin ((2 + 1) * INR (m+1) * PI * / INR (N + 1)))=
      2*sin (2 * INR (m+1) * PI * / INR (N + 1))* cos (1 * INR (m+1) * PI * / INR (N + 1))).
+ intros. rewrite H4. nra.
+ assert ((2 - 1) * INR (m+1) * PI * / INR (N + 1)= (2*INR (m+1) * PI * / INR (N + 1)) - (1*INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H4.
  assert ((2 + 1) * INR (m+1) * PI * / INR (N + 1)= (2*INR (m+1) * PI * / INR (N + 1)) + (1*INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H5.
  apply trigo_1.
Qed.

Lemma trigo_3: forall m:nat , sin ((INR m) * PI)=0.
Proof.
intros.
induction m.
+ assert (INR 0=0). { reflexivity. } rewrite H.
  assert (0 * PI =0). { nra. } rewrite H0. apply sin_0.
+ assert (S m = (m+1)%nat). { omega. } rewrite H. 
  assert (INR (m+1)= INR m + INR 1). { apply plus_INR. } rewrite H0.
  assert ((INR m + INR 1) * PI= (INR m)*PI + (INR 1)* PI). { nra. } rewrite H1.
  assert (INR 1* PI=PI). { assert (INR 1=1). { reflexivity. } rewrite H2. nra. }
  rewrite H2.
  assert ( sin (INR m * PI + PI)= - sin (INR m * PI)). { apply neg_sin. } rewrite H3.
  rewrite IHm. nra.
Qed.


Lemma i_0_j (a b c:R): forall (m N:nat), (2<N)%nat -> (0<=m<N)%nat -> a=c /\ 0<c->
  mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero 0)
  (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) 0 0) +
mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero 1)
  (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) 1 0) =
mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) zero 0)
  (coeff_mat Hierarchy.zero (Lambda m N a b c ) 0 0).
Proof.
intros.
unfold Lambda.  
assert(coeff_mat Hierarchy.zero
        (mk_matrix 1 1
          (fun _ _ : nat =>
           b + 2 * sqrt (a * c) * cos (INR (m + 1) * PI * / INR (N + 1)))) 0 0= (fun _ _ : nat =>
           b + 2 * sqrt (a * c) * cos (INR (m + 1) * PI * / INR (N + 1))) 0%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun _ _ : nat =>
           b + 2 * sqrt (a * c) * cos (INR (m + 1) * PI * / INR (N + 1))) 0%nat 0%nat). omega. omega. }
rewrite H2. unfold Eigen_vec.
assert(coeff_mat Hierarchy.zero
        (mk_matrix N 1
          (fun i _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a * / c) (INR i + 1 - 1 * / 2) *
           sin ((INR i + 1) * INR (m + 1) * PI * / INR (N + 1)))) 0 0= (fun i _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a * / c) (INR i + 1 - 1 * / 2) *
           sin ((INR i + 1) * INR (m + 1) * PI * / INR (N + 1))) 0%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a * / c) (INR i + 1 - 1 * / 2) *
           sin ((INR i + 1) * INR (m + 1) * PI * / INR (N + 1))) 0%nat 0%nat). omega. omega. }
rewrite H3. 
assert (coeff_mat Hierarchy.zero
         (mk_matrix N 1
          (fun i _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a * / c) (INR i + 1 - 1 * / 2) *
           sin ((INR i + 1) * INR (m + 1) * PI * / INR (N + 1)))) 1 0= (fun i _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a * / c) (INR i + 1 - 1 * / 2) *
           sin ((INR i + 1) * INR (m + 1) * PI * / INR (N + 1))) 1%nat 0%nat). 
{ apply (coeff_mat_bij Hierarchy.zero (fun i _ : nat =>
           sqrt (2 / INR (N + 1)) * Rpower (a * / c) (INR i + 1 - 1 * / 2) *
           sin ((INR i + 1) * INR (m + 1) * PI * / INR (N + 1))) 1%nat 0%nat). omega. omega. }
rewrite H4.
assert(coeff_mat Hierarchy.zero
      (mk_matrix N 1
        (fun i _ : nat =>
         sqrt (2 / INR (N + 1)) * Rpower (a * / c) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m + 1) * PI * / INR (N + 1)))) zero 0=(fun i _ : nat =>
         sqrt (2 / INR (N + 1)) * Rpower (a * / c) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m + 1) * PI * / INR (N + 1))) zero 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i _ : nat =>
         sqrt (2 / INR (N + 1)) * Rpower (a * / c) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m + 1) * PI * / INR (N + 1))) zero 0%nat). apply obvio_1. omega. omega. }
rewrite H5. 
assert ((a  * / c ) =1). 
{ destruct H1 as [H1 H6]. rewrite H1. apply Rinv_r. nra.  }
  rewrite H6. 
  assert (Rpower 1 (INR 0 + 1 - 1 * / 2)=1). { apply (rpower_1 (INR 0 + 1 - 1 * / 2)). } rewrite H7.
  assert ((Rpower 1 (INR 1 + 1 - 1 * / 2))=1). { apply (rpower_1 (INR 1 + 1 - 1 * / 2) ). } rewrite H8.
  assert (Rpower 1 (INR zero + 1 - 1 * / 2) = 1). { apply (rpower_1 (INR zero + 1 - 1 * / 2)). } rewrite H9.
  assert ((sqrt (2 / INR (N + 1))*1 * sin ((INR 0 + 1) * INR (m+1) * PI * / INR (N + 1)))= sqrt (2 / INR (N + 1))*sin ((INR 0 + 1) * INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H10.
  assert ((sqrt (2 / INR (N + 1))*1 * sin ((INR 1 + 1) * INR (m+1) * PI * / INR (N + 1)))= sqrt (2 / INR (N + 1))*sin ((INR 1 + 1) * INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H11.
  assert (sqrt (2 / INR (N + 1))*1 * sin ((INR zero + 1) * INR (m+1) * PI * / INR (N + 1))= sqrt (2 / INR (N + 1))*sin ((INR zero + 1) * INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H12.
  assert (sqrt (a*c )= c ). {  destruct H1 as [H1 H13]. rewrite H1. apply sqrt_square. nra. } rewrite H13.
  assert (coeff_mat Hierarchy.zero (Ah N a b c ) zero 0= b  ). { apply coeff_prop_2. omega. omega. } rewrite H14. 
  assert (coeff_mat Hierarchy.zero (Ah N a b c ) zero 1= c ). { apply coeff_prop_3. omega. assert (zero=0%nat). auto. rewrite H15. omega. } rewrite H15.
  assert (INR 0=0). { reflexivity. } rewrite H16.
  assert (INR 1= 1). { reflexivity. } rewrite H17.
  assert (INR zero = 0). { reflexivity. } rewrite H18.
  assert ((0 + 1)=1). { nra. } rewrite H19.
  assert ((1 + 1)=2). { nra. } rewrite H20.
  assert(mult (sqrt (2 / INR (N + 1))* sin (1 * INR (m+1) * PI * / INR (N + 1)))
        (b  + 2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))= 
        (sqrt (2 / INR (N + 1))*sin (1 * INR (m+1) * PI * / INR (N + 1)))* (b ) + 
        (sqrt (2 / INR (N + 1))*sin (1 * INR (m+1) * PI * / INR (N + 1)))* (2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))).
  { apply (mult_distr_l  (sqrt (2 / INR (N + 1))*sin (1 * INR (m+1) * PI * / INR (N + 1))) (b ) (2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))). }
  rewrite H21.
  assert (sqrt (2 / INR (N + 1))*sin (1 * INR (m+1) * PI * / INR (N + 1))= sqrt (2 / INR (N + 1))*sin (INR (m+1) * PI * / INR (N + 1))). 
  { apply Rmult_eq_compat_l.
    assert(1 * INR (m+1) * PI * / INR (N + 1)= (INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H22. reflexivity. } rewrite H22.
    assert (sqrt (2 / INR (N + 1))*sin (INR (m+1) * PI * / INR (N + 1)) *
              (2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))= sqrt (2 / INR (N + 1))*(c ) * (2 * sin (INR (m+1) * PI * / INR (N + 1))* cos (INR (m+1) * PI * / INR (N + 1)))).
  { nra. } rewrite H23.
  assert ((sin (2 * INR (m+1) * PI * / INR (N + 1)))= (2 * sin (INR (m+1) * PI * / INR (N + 1)) *
              cos (INR (m+1) * PI * / INR (N + 1)))).
  { assert (2 * INR (m+1) * PI * / INR (N + 1)= 2*(INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H24. apply sin_2a. }
  rewrite <- H24. 
  assert (mult (b ) (sqrt (2 / INR (N + 1))* sin (INR (m+1) * PI * / INR (N + 1)))= (sqrt (2 / INR (N + 1))* sin (INR (m+1) * PI * / INR (N + 1))) * b ). { apply Rmult_comm. } rewrite H25.
  assert (mult (c )  (sqrt (2 / INR (N + 1)) *  sin (2 * INR (m + 1) * PI * / INR (N + 1)))=
            sqrt (2 / INR (N + 1)) * c  *sin (2 * INR (m + 1) * PI * / INR (N + 1))). 
  { assert (sqrt (2 / INR (N + 1)) * c  *sin (2 * INR (m + 1) * PI * / INR (N + 1))=
             (c ) *  (sqrt (2 / INR (N + 1)) *   sin (2 * INR (m + 1) * PI * / INR (N + 1)))). { nra. } rewrite H26. reflexivity.
  } rewrite H26.
  reflexivity.
Qed.

Lemma i_j (a b c:R): forall (m N i:nat) , (2<N)%nat -> (0<=m<N)%nat -> (1 < i < pred N)%nat -> a=c /\ 0<c ->
    mult (coeff_mat Hierarchy.zero (Ah N a b c ) i (pred i))
      (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) (pred i) 0) +
    mult (coeff_mat Hierarchy.zero (Ah N a b c ) i i)
      (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) i 0) +
    mult (coeff_mat Hierarchy.zero (Ah N a b c ) i (i + 1))
      (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) (i + 1) 0) =
    mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c) i 0)
      (coeff_mat Hierarchy.zero (Lambda m N a b c ) 0 0).
Proof.
intros. unfold Lambda.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 1 1
        (fun _ _ : nat =>
         b  + 2 * sqrt (a * c ) * cos (INR (m+1) * PI * / INR (N + 1)))) 0 0=
      (fun _ _ : nat =>
         b  + 2 * sqrt (a * c ) * cos (INR (m+1) * PI * / INR (N + 1))) 0%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun _ _ : nat =>
         b  + 2 * sqrt (a * c ) * cos (INR (m+1) * PI * / INR (N + 1))) 0%nat 0%nat). omega. omega. }
rewrite H3.
unfold Eigen_vec.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N 1
        (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i0 + 1 - 1 * / 2) *
         sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) 
     (pred i) 0=  (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i0 + 1 - 1 * / 2) *
         sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))) (pred i) 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i0 + 1 - 1 * / 2) *
         sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))) (pred i) 0%nat). omega. omega. }
rewrite H4.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N 1
        (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i0 + 1 - 1 * / 2) *
         sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) i 0=(fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i0 + 1 - 1 * / 2) *
         sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))) i 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i0 + 1 - 1 * / 2) *
         sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))) i 0%nat). omega. omega. } rewrite H5.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N 1
        (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i0 + 1 - 1 * / 2) *
         sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) 
     (i + 1) 0= (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i0 + 1 - 1 * / 2) *
         sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))) (i+1)%nat 0%nat). 
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i0 + 1 - 1 * / 2) *
         sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))) (i+1)%nat 0%nat). omega. omega. }
rewrite H6.
assert ((a  * / c )=1). 
{ destruct H2 as [ H2 H7]. rewrite H2. apply Rinv_r. nra. } rewrite H7.
assert ( Rpower 1 (INR (pred i) + 1 - 1 * / 2)=1). { apply (rpower_1 (INR (pred i) + 1 - 1 * / 2)). } rewrite H8.
assert (Rpower 1 (INR i + 1 - 1 * / 2)= 1). { apply (rpower_1 (INR i + 1 - 1 * / 2)). } rewrite H9.
assert (Rpower 1 (INR (i + 1) + 1 - 1 * / 2)=1). { apply (rpower_1 (INR (i + 1) + 1 - 1 * / 2)). } rewrite H10.
assert ((sqrt (2 / INR (N + 1)) *1 * sin ((INR (pred i) + 1) * INR (m+1) * PI * / INR (N + 1))) = sqrt (2 / INR (N + 1)) *sin ((INR (pred i) + 1) * INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H11.
assert ((sqrt (2 / INR (N + 1)) *1 * sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1)))= sqrt (2 / INR (N + 1)) *sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H12.
assert ((sqrt (2 / INR (N + 1)) *1 * sin ((INR (i + 1) + 1) * INR (m+1) * PI * / INR (N + 1)))= sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) + 1) * INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H13.
assert ((coeff_mat Hierarchy.zero (Ah N a b c  ) i (pred i))= a ). { apply (coeff_prop_1 ). omega. omega. } rewrite H14.
assert ((coeff_mat Hierarchy.zero (Ah N a b c ) i i)= b ). { apply (coeff_prop_2 ). omega. omega. } rewrite H15. 
assert ((coeff_mat Hierarchy.zero (Ah N a b c  ) i (i + 1))= c ). { apply (coeff_prop_3 ). omega. omega. } rewrite H16.
assert (a  = c ). { nra.  } 
assert (sqrt (a * c )= c ). { rewrite H17. apply sqrt_square. nra.  } rewrite H18.
assert (pred i = (i-1)%nat). { omega. } rewrite H19. 
assert (INR (i-1)=INR i - INR 1). { apply minus_INR. omega. } rewrite H20. 
assert (INR 1= 1). { reflexivity. } rewrite H21.
assert (INR i - 1 + 1= (INR i + 1)-1). { nra. } rewrite H22. rewrite <- H21.
assert (INR (i+1)= INR i + INR 1). { apply plus_INR. } rewrite <- H23. 
assert (mult (a )
          (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) - INR 1) * INR (m+1) * PI * / INR (N + 1))) +
        mult (b )
          (sqrt (2 / INR (N + 1)) *sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1))) +
        mult (c )
          (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) + INR 1) * INR (m+1) * PI * / INR (N + 1)))=
         mult (b )
          (sqrt (2 / INR (N + 1)) *sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1))) +mult (a )
          (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) - INR 1) * INR (m+1) * PI * / INR (N + 1))) +
         mult (c )
          (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) + INR 1) * INR (m+1) * PI * / INR (N + 1)))). { nra. } rewrite H24.
assert(mult (b )
        (sqrt (2 / INR (N + 1)) *sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1))) +
      mult (a )
        (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) - INR 1) * INR (m+1) * PI * / INR (N + 1))) +
      mult (c )
        (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) + INR 1) * INR (m+1) * PI * / INR (N + 1)))=
      mult (b )
        (sqrt (2 / INR (N + 1)) *sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1))) +
      (mult (a )
        (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) - INR 1) * INR (m+1) * PI * / INR (N + 1))) +
      mult (c )
        (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) + INR 1) * INR (m+1) * PI * / INR (N + 1))))). { nra. } rewrite H25. rewrite H17.
assert ((c ) * ( sqrt (2 / INR (N + 1)) *(sin ((INR (i + 1) - INR 1) * INR (m+1) * PI * / INR (N + 1)))+ sqrt (2 / INR (N + 1)) *(sin ((INR (i + 1) + INR 1) * INR (m+1) * PI * / INR (N + 1))))=
        (mult (c )
           (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) - INR 1) * INR (m+1) * PI * / INR (N + 1))) +
         mult (c )
           (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) + INR 1) * INR (m+1) * PI * / INR (N + 1))))). 
{ apply (mult_distr_l (c ) (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) - INR 1) * INR (m+1) * PI * / INR (N + 1))) 
          (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) + INR 1) * INR (m+1) * PI * / INR (N + 1)))). } rewrite <-H26.
assert (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) - INR 1) * INR (m+1) * PI * / INR (N + 1)) +
          (sqrt (2 / INR (N + 1)) *sin ((INR (i + 1) + INR 1) * INR (m+1) * PI * / INR (N + 1)))=
        sqrt (2 / INR (N + 1)) *2* (sin ((INR (i + 1) * INR (m+1) * PI * / INR (N + 1))) * cos (INR (m+1) * PI * / INR (N + 1)))).
{ assert (sqrt (2 / INR (N + 1)) *
              sin
                ((INR (i + 1) - INR 1) * INR (m + 1) * PI *
                 / INR (N + 1)) +
              sqrt (2 / INR (N + 1)) *
              sin
                ((INR (i + 1) + INR 1) * INR (m + 1) * PI *
                 / INR (N + 1))= sqrt (2 / INR (N + 1)) *
                  (sin
                    ((INR (i + 1) - INR 1) * INR (m + 1) * PI *
                     / INR (N + 1)) +
                  sin
                    ((INR (i + 1) + INR 1) * INR (m + 1) * PI *
                     / INR (N + 1)))). { nra. } rewrite H27.
 assert ( sqrt (2 / INR (N + 1)) * 2 *
              (sin (INR (i + 1) * INR (m + 1) * PI * / INR (N + 1)) *
               cos (INR (m + 1) * PI * / INR (N + 1)))= sqrt (2 / INR (N + 1)) *( 2 *
                  (sin (INR (i + 1) * INR (m + 1) * PI * / INR (N + 1)) *
                   cos (INR (m + 1) * PI * / INR (N + 1))))). { nra. } rewrite H28. apply Rmult_eq_compat_l.
  assert ((INR (i + 1) - INR 1) * INR (m+1) * PI * / INR (N + 1)= (INR (i+1) * INR (m+1) * PI * / INR (N + 1))- (INR 1 * INR (m+1) * PI * / INR (N + 1))).
  { nra. } rewrite H29.
  assert ((INR (i + 1) + INR 1) * INR (m+1) * PI * / INR (N + 1)= (INR (i+1) * INR (m+1) * PI * / INR (N + 1))+ (INR 1 * INR (m+1) * PI * / INR (N + 1))).
  { nra. } rewrite H30. 
    assert (INR 1 * INR (m+1) * PI * / INR (N + 1)=(INR (m+1) * PI * / INR (N + 1))). { assert (INR 1 = 1). { reflexivity. } rewrite H31. nra. } rewrite H31. 
    assert (2 *(sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1)) *
             cos (INR (m+1) * PI * / INR (N + 1)))=2 *sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1)) *
            cos (INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H32.
    apply (trigo_1 ((INR (i + 1) * INR (m+1) * PI * / INR (N + 1))) (INR (m+1) * PI * / INR (N + 1))).
} rewrite H27.
assert (c  *(sqrt (2 / INR (N + 1))* 2 *
           (sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1)) *
            cos (INR (m+1) * PI * / INR (N + 1))))=sqrt (2 / INR (N + 1))* 2* (c ) * (sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1)))* cos (INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H28.
assert (mult (sqrt (2 / INR (N + 1))* sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1)))
          (b  + 2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))= (sqrt (2 / INR (N + 1))*sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1)))* (b ) +
          (sqrt (2 / INR (N + 1))*sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1)))* (2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))). 
{ apply (mult_distr_l (sqrt (2 / INR (N + 1))*sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1))) (b ) (2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))). }
rewrite H29. 
assert (sqrt (2 / INR (N + 1))*sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1)) *
            (2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))=  sqrt (2 / INR (N + 1))*2* c  * sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1)) *
              cos (INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H30. 
assert (mult (b )
            (sqrt (2 / INR (N + 1))*sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1)))= (sqrt (2 / INR (N + 1))*sin (INR (i + 1) * INR (m+1) * PI * / INR (N + 1))) * b ). { apply Rmult_comm. } rewrite H31.
reflexivity.
Qed.

Lemma i_predN_j (a b c:R): forall (m N:nat) , (2<N)%nat -> (0<=m<N)%nat -> a=c /\ 0<c ->
  mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) (N - 2))
    (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) (N - 2) 0) +
  mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) (pred N))
    (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) (pred N) 0) =
  mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) (pred N) 0)
    (coeff_mat Hierarchy.zero (Lambda m N a b c ) 0 0).
Proof.
intros.
unfold Lambda.
assert (coeff_mat Hierarchy.zero
     (mk_matrix 1 1
        (fun _ _ : nat =>
         b  + 2 * sqrt (a * c ) * cos (INR (m+1) * PI * / INR (N + 1)))) 0 0=
        (fun _ _ : nat =>
         b  + 2 * sqrt (a * c ) * cos (INR (m+1) * PI * / INR (N + 1))) 0%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun _ _ : nat =>
         b  + 2 * sqrt (a * c ) * cos (INR (m+1) * PI * / INR (N + 1))) 0%nat 0%nat). omega. omega. }
rewrite H2. unfold Eigen_vec.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N 1
        (fun i _ : nat => sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1)))) 
     (N - 2) 0= (fun i _ : nat => sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1))) (N-2)%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i _ : nat => sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1))) (N-2)%nat 0%nat). omega. omega. }
rewrite H3.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N 1
        (fun i _ : nat => sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1)))) 
     (pred N) 0= (fun i _ : nat => sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1))) (pred N) 0%nat). 
{ apply (coeff_mat_bij Hierarchy.zero (fun i _ : nat => sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1))) (pred N) 0%nat).  omega. omega. }
rewrite H4.
assert ((a  * / c ) =1). { destruct H1. rewrite H1. apply Rinv_r. nra. } rewrite H5.
assert (Rpower 1 (INR (N - 2) + 1 - 1 * / 2)=1). { apply (rpower_1 (INR (N - 2) + 1 - 1 * / 2)). } rewrite H6.
assert (Rpower 1 (INR (pred N) + 1 - 1 * / 2) =1). { apply (rpower_1 (INR (pred N) + 1 - 1 * / 2)). } rewrite H7.
assert (sqrt (a * c)  = c ). { destruct H1. rewrite H1. apply sqrt_square.  nra.  } rewrite H8.
assert (( sqrt (2 / INR (N + 1)) *1 * sin ((INR (N - 2) + 1) * INR (m+1) * PI * / INR (N + 1)))= sqrt (2 / INR (N + 1)) * sin ((INR (N - 2) + 1) * INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H9.
assert (( sqrt (2 / INR (N + 1)) *1 * sin ((INR (pred N) + 1) * INR (m+1) * PI * / INR (N + 1)))= sqrt (2 / INR (N + 1)) * sin ((INR (pred N) + 1) * INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H10.
assert ((coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) (N - 2))= a ). 
{ assert ((N-2)%nat = pred (pred N)). { omega. } rewrite H11. apply (coeff_prop_1 ). omega. omega. } rewrite H11.
assert (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) (pred N)= b ). { apply (coeff_prop_2 ). omega. omega. } rewrite H12.
assert (a = c ). { nra.   } rewrite H13.
assert (INR (N-2)= INR N - INR 2). { apply minus_INR. omega. } rewrite H14.
assert ((INR N - INR 2 + 1)=INR (N-1)).
{ assert (INR 2= 2). { reflexivity. } rewrite H15. 
  assert (INR N - 2 + 1= INR N -1).  { nra. } rewrite H16. symmetry. apply minus_INR. omega. }
rewrite H15.
assert ((INR (pred N) + 1)= INR N).
{ assert (pred N = (N-1)%nat). { omega. } rewrite H16. 
  assert (INR (N-1)=INR N - INR 1). { apply minus_INR. omega. } rewrite H17. 
  assert (INR 1= 1). { reflexivity. } rewrite H18. nra. 
}
rewrite H16.
assert (mult ( sqrt (2 / INR (N + 1)) *sin (INR N * INR (m+1) * PI * / INR (N + 1)))
            (b  + 2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))= 
          ( sqrt (2 / INR (N + 1)) *sin (INR N * INR (m+1) * PI * / INR (N + 1))) * (b ) + 
          ( sqrt (2 / INR (N + 1)) *sin (INR N * INR (m+1) * PI * / INR (N + 1)))* (2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))).
{ apply (mult_distr_l ( sqrt (2 / INR (N + 1)) *sin (INR N * INR (m+1) * PI * / INR (N + 1))) (b ) ( 2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))). }
rewrite H17.
assert ( sqrt (2 / INR (N + 1)) *sin (INR N * INR (m+1) * PI * / INR (N + 1)) *(2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))=
          mult (c ) ( sqrt (2 / INR (N + 1)) *sin (INR (N - 1) * INR (m+1) * PI * / INR (N + 1)))).
{ assert (mult (c )  (sqrt (2 / INR (N + 1)) *  sin (INR (N - 1) * INR (m + 1) * PI * / INR (N + 1)))=
            (c ) * (sqrt (2 / INR (N + 1)) *  sin (INR (N - 1) * INR (m + 1) * PI * / INR (N + 1)))). { reflexivity. } rewrite H18.
  assert (c  *(sqrt (2 / INR (N + 1)) * sin (INR (N - 1) * INR (m + 1) * PI * / INR (N + 1)))=
            (sqrt (2 / INR (N + 1)) * (c )) * sin (INR (N - 1) * INR (m + 1) * PI * / INR (N + 1))). { nra. } rewrite H19.
  assert (sqrt (2 / INR (N + 1)) *sin (INR N * INR (m + 1) * PI * / INR (N + 1)) *(2 * c  * cos (INR (m + 1) * PI * / INR (N + 1)))=
          (sqrt (2 / INR (N + 1))* (c )) * (2 * sin (INR N * INR (m + 1) * PI * / INR (N + 1))*cos (INR (m + 1) * PI * / INR (N + 1)))). { nra. } rewrite H20.
  apply Rmult_eq_compat_l. 
  assert (sin ((INR N * INR (m+1) * PI * / INR (N + 1))- (INR (m+1) * PI * / INR (N + 1)))+ sin ((INR N * INR (m+1) * PI * / INR (N + 1))+ (INR (m+1) * PI * / INR (N + 1)))=
            2 * sin (INR N * INR (m+1) * PI * / INR (N + 1)) *cos (INR (m+1) * PI * / INR (N + 1))). { apply trigo_1. } rewrite <-H21.
  assert ((INR (N - 1) * INR (m+1) * PI * / INR (N + 1))= (INR N * INR (m+1) * PI * / INR (N + 1) -
             INR (m+1) * PI * / INR (N + 1))). 
  { assert (INR (N - 1) * INR (m+1) * PI * / INR (N + 1)= INR (N - 1) * (INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H22.
    assert (INR N * INR (m+1) * PI * / INR (N + 1)= INR N * (INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H23.
    assert (INR N * (INR (m+1) * PI * / INR (N + 1)) -INR (m+1) * PI * / INR (N + 1)= INR N * (INR (m+1) * PI * / INR (N + 1)) -
              (1 * INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H24.
    assert ((1* INR (m+1) * PI * / INR (N + 1))= (INR 1)* (INR (m+1) * PI * / INR (N + 1))). { assert (INR 1=1). { reflexivity. } rewrite H25. nra. } rewrite H25.
    assert (INR (N-1)= INR N - INR 1). { apply minus_INR. omega. } rewrite H26. nra.
  }
  rewrite <-H22.
  assert ((INR (N + 1) * INR (m+1) * PI * / INR (N + 1))= (INR N * INR (m+1) * PI * / INR (N + 1) +
             INR (m+1) * PI * / INR (N + 1))). 
  { assert (INR (N + 1) * INR (m+1) * PI * / INR (N + 1)= INR (N + 1) * (INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H23.
    assert (INR N * INR (m+1) * PI * / INR (N + 1)= INR N * (INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H24.
    assert (INR N * (INR (m+1) * PI * / INR (N + 1)) +INR (m+1) * PI * / INR (N + 1)= INR N * (INR (m+1) * PI * / INR (N + 1)) +
              (1 * INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H25.
    assert ((1* INR (m+1) * PI * / INR (N + 1))= (INR 1)* (INR (m+1) * PI * / INR (N + 1))). { assert (INR 1=1). { reflexivity. } rewrite H26. nra. } rewrite H26.
    assert (INR (N+1)= INR N + INR 1). { apply plus_INR. } rewrite H27. nra.
  }
  rewrite <- H23.
  assert (sin (INR (N + 1) * INR (m+1) * PI * / INR (N + 1))=0). 
  { assert (INR (N + 1) * INR (m+1) * PI * / INR (N + 1)= INR (m+1) * PI).
    { assert (INR (N + 1) * INR (m+1) * PI * / INR (N + 1)= (INR (N+1)*/(INR (N+1)))* (INR (m+1) * PI)). { nra. } rewrite H24.
      assert (INR (N + 1) * / INR (N + 1)=1). { apply Rinv_r.
      apply not_0_INR. 
      assert ((0< (N+1))%nat -> (N+1)%nat <> 0%nat). { omega. } apply H25. omega. } rewrite H25. nra.
    } rewrite H24.
    apply trigo_3.
  }
  rewrite H24. nra.
}
assert (mult (b ) (sqrt (2 / INR (N + 1)) *sin (INR N * INR (m+1) * PI * / INR (N + 1)))=(sqrt (2 / INR (N + 1)) *sin (INR N * INR (m+1) * PI * / INR (N + 1))) * b ).
{ apply Rmult_comm. } rewrite H19. nra.
Qed.

Lemma i_1_j (a b c:R): forall (m N:nat), (2<N)%nat -> (0<=m<N)%nat -> a=c /\ 0<c ->
    mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 0)
      (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) 0 0) +
    mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 1)
      (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) 1 0) +
    mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 2)
      (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) 2 0) =
    mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) 1 0)
      (coeff_mat Hierarchy.zero (Lambda m N a b c ) 0 0).
Proof.
intros.
unfold Lambda.
assert(coeff_mat Hierarchy.zero
     (mk_matrix 1 1
        (fun _ _ : nat =>
         b  + 2 * sqrt (a * c ) * cos (INR (m+1) * PI * / INR (N + 1)))) 0 0=
        (fun _ _ : nat =>
         b  + 2 * sqrt (a * c ) * cos (INR (m+1) * PI * / INR (N + 1))) 0%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun _ _ : nat =>
         b  + 2 * sqrt (a * c ) * cos (INR (m+1) * PI * / INR (N + 1))) 0%nat 0%nat). omega. omega. }
rewrite H2. unfold Eigen_vec.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N 1
        (fun i _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1)))) 0 0=(fun i _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1))) 0%nat 0%nat).
{ apply (coeff_mat_bij   Hierarchy.zero (fun i _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1))) 0%nat 0%nat). omega. omega. }
rewrite H3.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N 1
        (fun i _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1)))) 1 0= (fun i _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1))) 1%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1))) 1%nat 0%nat). omega. omega. }
rewrite H4.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N 1
        (fun i _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1)))) 2 0= (fun i _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1))) 2%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a  * / c ) (INR i + 1 - 1 * / 2) *
         sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1))) 2%nat 0%nat). omega. omega. }
rewrite H5.
assert ((a  * / c )=1). { destruct H1. rewrite H1. apply Rinv_r. nra.  } rewrite H6.
assert (Rpower 1 (INR 0 + 1 - 1 * / 2)=1). { apply (rpower_1 (INR 0 + 1 - 1 * / 2)). } rewrite H7. 
assert (Rpower 1 (INR 1 + 1 - 1 * / 2)=1). { apply (rpower_1 (INR 1 + 1 - 1 * / 2)). } rewrite H8.
assert (Rpower 1 (INR 2 + 1 - 1 * / 2)=1). { apply (rpower_1 (INR 2 + 1 - 1 * / 2)). } rewrite H9.
assert ((sqrt (2 / INR (N + 1)) *1 * sin ((INR 0 + 1) * INR (m+1) * PI * / INR (N + 1)))=sqrt (2 / INR (N + 1)) * sin ((INR 0 + 1) * INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H10.
assert (sqrt (2 / INR (N + 1)) *1 * sin ((INR 1 + 1) * INR (m+1) * PI * / INR (N + 1))= sqrt (2 / INR (N + 1)) *sin ((INR 1 + 1) * INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H11.
assert (sqrt (2 / INR (N + 1)) *1 * sin ((INR 2 + 1) * INR (m+1) * PI * / INR (N + 1))=sqrt (2 / INR (N + 1)) * sin ((INR 2 + 1) * INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H12.
assert ((coeff_mat Hierarchy.zero (Ah N a b c ) 1 0)= a ). { apply coeff_prop_1. omega. omega. } rewrite H13.
assert ((coeff_mat Hierarchy.zero (Ah N a b c ) 1 1)= b ). { apply (coeff_prop_2 ). omega. omega. } rewrite H14.
assert ((coeff_mat Hierarchy.zero (Ah N a b c ) 1 2)= c ). { apply (coeff_prop_3 ). omega. omega. } rewrite H15.
assert ( sqrt (a * c )= c ). { destruct H1. rewrite H1. apply sqrt_square. nra.  } rewrite H16.
assert ( INR 0=0). { reflexivity. } rewrite H17. 
assert (INR 1= 1). { reflexivity. } rewrite H18.
assert (0+1=1). { nra. } rewrite H19.
assert (1+1=2). { nra. } rewrite H20.
assert (a = c ). { nra. } rewrite H21.
assert (mult (c ) (sqrt (2 / INR (N + 1)) *sin (1 * INR (m+1) * PI * / INR (N + 1))) +
          mult (b ) (sqrt (2 / INR (N + 1)) *sin (2 * INR (m+1) * PI * / INR (N + 1))) +
          mult (c ) (sqrt (2 / INR (N + 1)) *sin ((INR 2 + 1) * INR (m+1) * PI * / INR (N + 1)))=  mult (b ) (sqrt (2 / INR (N + 1)) *sin (2 * INR (m+1) * PI * / INR (N + 1)))+ 
          (mult (c ) (sqrt (2 / INR (N + 1)) *sin (1 * INR (m+1) * PI * / INR (N + 1)))+ mult (c ) (sqrt (2 / INR (N + 1)) *sin ((INR 2 + 1) * INR (m+1) * PI * / INR (N + 1))))).
{ nra. } rewrite H22.
assert ((mult (c ) (sqrt (2 / INR (N + 1)) *sin (1 * INR (m+1) * PI * / INR (N + 1))) +
            mult (c )(sqrt (2 / INR (N + 1)) *sin ((INR 2 + 1) * INR (m+1) * PI * / INR (N + 1))))= sqrt (2 / INR (N + 1)) *2* (c )*(sin (2 * INR (m+1) * PI * / INR (N + 1)))*(cos (1 * INR (m+1) * PI * / INR (N + 1)))).
{ assert (INR 2=2). { reflexivity. } rewrite H23.
  assert (mult (c )  (sqrt (2 / INR (N + 1)) *   sin (1 * INR (m + 1) * PI * / INR (N + 1))) =
              (c ) * (sqrt (2 / INR (N + 1)) *   sin (1 * INR (m + 1) * PI * / INR (N + 1)))). { reflexivity. }rewrite H24.
  assert (mult (c )  (sqrt (2 / INR (N + 1)) *  sin ((2 + 1) * INR (m + 1) * PI * / INR (N + 1)))=
          (c)  * (sqrt (2 / INR (N + 1)) *  sin ((2 + 1) * INR (m + 1) * PI * / INR (N + 1)))). { reflexivity. } rewrite H25.
  assert (c  *
            (sqrt (2 / INR (N + 1)) *
             sin (1 * INR (m + 1) * PI * / INR (N + 1))) +
            c  *
            (sqrt (2 / INR (N + 1)) *
             sin ((2 + 1) * INR (m + 1) * PI * / INR (N + 1)))= sqrt (2 / INR (N + 1))* ((c  *  sin (1 * INR (m + 1) * PI * / INR (N + 1)))+
              (c ) *  sin ((2 + 1) * INR (m + 1) * PI * / INR (N + 1)))). { nra. } rewrite H26.
  assert (sqrt (2 / INR (N + 1)) * 2 * c  *
              sin (2 * INR (m + 1) * PI * / INR (N + 1)) *
              cos (1 * INR (m + 1) * PI * / INR (N + 1))=sqrt (2 / INR (N + 1)) *(2 * c  *
              sin (2 * INR (m + 1) * PI * / INR (N + 1)) *
              cos (1 * INR (m + 1) * PI * / INR (N + 1)))). { nra. } rewrite H27. apply Rmult_eq_compat_l.
  assert (2+1=3). { nra. } rewrite H28. apply (trigo_2 ). omega. omega.
} rewrite H23. 
assert ((1 * INR (m+1) * PI * / INR (N + 1))= INR (m+1) * PI * / INR (N + 1)). { nra. } rewrite H24.
assert (mult (c ) (sqrt (2 / INR (N + 1)) *sin (INR (m+1) * PI * / INR (N + 1))) +
            mult (b ) (sqrt (2 / INR (N + 1)) *sin (2 * INR (m+1) * PI * / INR (N + 1))) +
            mult (c ) (sqrt (2 / INR (N + 1)) *sin (INR (m+1) * PI * / INR (N + 1)))= 
            mult (b ) (sqrt (2 / INR (N + 1)) *sin (2 * INR (m+1) * PI * / INR (N + 1)))+ sqrt (2 / INR (N + 1)) *2* (c )*(sin (INR (m+1) * PI * / INR (N + 1)))).
{ cut (mult (c ) (sqrt (2 / INR (N + 1)) *sin (INR (m+1) * PI * / INR (N + 1))) +
            mult (b ) (sqrt (2 / INR (N + 1)) *sin (2 * INR (m+1) * PI * / INR (N + 1))) +
            mult (c ) (sqrt (2 / INR (N + 1)) *sin (INR (m+1) * PI * / INR (N + 1)))=  mult (b ) (sqrt (2 / INR (N + 1)) *sin (2 * INR (m+1) * PI * / INR (N + 1)))+
          (mult (c ) (sqrt (2 / INR (N + 1)) *sin (INR (m+1) * PI * / INR (N + 1)))+mult (c ) (sqrt (2 / INR (N + 1)) *sin (INR (m+1) * PI * / INR (N + 1))))).
  + intros. rewrite H25.
    assert ((mult (c ) (sqrt (2 / INR (N + 1)) *sin (INR (m+1) * PI * / INR (N + 1))) +
                mult (c ) (sqrt (2 / INR (N + 1)) *sin (INR (m+1) * PI * / INR (N + 1))))= sqrt (2 / INR (N + 1)) *2 * c  * sin (INR (m+1) * PI * / INR (N + 1))).
    { assert (2=1+1). { nra. } rewrite H26.
      assert (mult (c )  (sqrt ((1 + 1) / INR (N + 1)) *   sin (INR (m + 1) * PI * / INR (N + 1)))=
                (c ) * (sqrt ((1 + 1) / INR (N + 1)) *   sin (INR (m + 1) * PI * / INR (N + 1)))). { reflexivity. }rewrite H27.
      assert (c  *
                (sqrt ((1 + 1) / INR (N + 1)) *
                 sin (INR (m + 1) * PI * / INR (N + 1))) +
                c  *
                (sqrt ((1 + 1) / INR (N + 1)) *
                 sin (INR (m + 1) * PI * / INR (N + 1)))
                = sqrt ((1 + 1) / INR (N + 1))* 
                ( c  * sin (INR (m + 1) * PI * / INR (N + 1)) + c  * ( sin (INR (m + 1) * PI * / INR (N + 1))))). { nra. } rewrite H28.
      assert (sqrt ((1 + 1) / INR (N + 1)) * (1 + 1) * c  *sin (INR (m + 1) * PI * / INR (N + 1))=
              sqrt ((1 + 1) / INR (N + 1))* ((1 + 1) * c  *sin (INR (m + 1) * PI * / INR (N + 1)))). { nra. } rewrite H29. apply Rmult_eq_compat_l.
      assert ((1 + 1) * c  * sin (INR (m+1) * PI * / INR (N + 1))= 1*c  * sin (INR (m+1) * PI * / INR (N + 1))+1*c  * sin (INR (m+1) * PI * / INR (N + 1))).
      { nra. } rewrite H30. 
      assert (1 * c  * sin (INR (m+1) * PI * / INR (N + 1))= c  * sin (INR (m+1) * PI * / INR (N + 1))). { nra. } rewrite H31.
      reflexivity.
    } rewrite H26. reflexivity. 
  + nra.
}
assert (mult (sqrt (2 / INR (N + 1))* sin (2 * INR (m+1) * PI * / INR (N + 1)))
          (b  + 2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))= 
          (sqrt (2 / INR (N + 1))*sin (2 * INR (m+1) * PI * / INR (N + 1))) * (b ) + (sqrt (2 / INR (N + 1))*sin (2 * INR (m+1) * PI * / INR (N + 1))) * (2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))).
{ apply (mult_distr_l (sqrt (2 / INR (N + 1))*sin (2 * INR (m+1) * PI * / INR (N + 1))) (b ) (2 * c  * cos (INR (m+1) * PI * / INR (N + 1))) ). } rewrite H26.
assert (sqrt (2 / INR (N + 1))*sin (2 * INR (m+1) * PI * / INR (N + 1)) *(2 * c  * cos (INR (m+1) * PI * / INR (N + 1)))=sqrt (2 / INR (N + 1))*2 *(c ) * sin (2 * INR (m+1) * PI * / INR (N + 1)) * cos (INR (m+1) * PI * / INR (N + 1))).
{ nra. } rewrite H27.
assert (mult (b ) (sqrt (2 / INR (N + 1))*sin (2 * INR (m+1) * PI * / INR (N + 1)))=(sqrt (2 / INR (N + 1))* sin (2 * INR (m+1) * PI * / INR (N + 1))) * b ). { apply Rmult_comm. } rewrite H28. reflexivity. 
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

Lemma i_eq_1 (a b c:R):  forall (m N i j: nat), (2<N)%nat -> (0<=m<N)%nat -> (j< 1)%nat ->(i=1%nat /\ (i<N)%nat) -> a=c /\ 0<c ->
sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (Ah N a b c) 1 l)
     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 
  (pred N) =
sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) 1 l)
     (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 0 
  (pred 1).
Proof.
intros.
cut(sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 
  (pred N)= sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat 2%nat+ sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 3%nat (pred N)).
+ intros. rewrite H4.
  cut(sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 3 
  (pred N) = 0).
  - intros. rewrite H5. 
    assert (sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 2 + 0 =sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 2). { nra. } rewrite H6.
    assert (pred 1=0%nat). { omega. } rewrite H7.
    cut(sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
             (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 2= sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
             (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat 0%nat +sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
             (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 1%nat 2%nat).
    * intros. rewrite H8.
      cut(sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 1 2 =
          sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 1%nat 1%nat+sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 2%nat 2%nat).
      { intros. rewrite H9. 
        assert(sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 0 +
              (sum_n_m
                 (fun l : nat =>
                  mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                    (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 1 1 +
               sum_n_m
                 (fun l : nat =>
                  mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                    (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 2 2)=sum_n_m
                        (fun l : nat =>
                         mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                           (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 0 +
                      sum_n_m
                         (fun l : nat =>
                          mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                            (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 1 1 +
                       sum_n_m
                         (fun l : nat =>
                          mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                          (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 2 2). { nra. } rewrite H10.
        assert(sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 0 = (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat).
        { apply (sum_n_n (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat). } rewrite H11.
        assert (sum_n_m
                  (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 1 1 =(fun l : nat =>
                   mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 1%nat).
        { apply (sum_n_n  (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 1%nat). } rewrite H12.
        assert (sum_n_m
                  (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 2 2= (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 2%nat).
        { apply (sum_n_n (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 2%nat). } rewrite H13.
        assert( sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) 1 l)
                   (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 0 0= (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) 1 l)
                   (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 0%nat). 
        { apply (sum_n_n (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) 1 l)
                   (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 0%nat). } rewrite H14.
        assert (j=0%nat). { omega. } rewrite H15.
        apply (i_1_j). omega. omega. nra.
        }
      { apply (sum_n_m_Chasles (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 1%nat 1%nat 2%nat). omega. omega. }
   * apply (sum_n_m_Chasles (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat 0%nat 2%nat). omega. omega.
  - cut( N=3%nat \/ (3<N)%nat).
      { intros. destruct H5.
        + rewrite H5. apply (sum_n_m_zero (fun l : nat =>
                             mult (coeff_mat Hierarchy.zero (Ah 3 a b c) 1 l)
                               (coeff_mat Hierarchy.zero (Eigen_vec m 3 a b c) l j))). nia.
        + cut (sum_n_m (fun _ => 0) 3%nat (pred N)=0).
          - intros. rewrite <-H6. apply (sum_n_m_ext_loc  (fun l : nat =>
                                     mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
                                       (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j))(fun _ : nat => 0) 3%nat (pred N)). 
            intros. 
            cut((coeff_mat Hierarchy.zero (Ah N a b c ) 1 k)= 0).
            * intros. rewrite H8. apply (mult_zero_l (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) k j)). 
            * apply (mat_prop_2 a b c k m N). nia. nia.
          - apply (sum_const_zero 3%nat (pred N)).
        + nia.
      }
      { omega. }
+ apply (sum_n_m_Chasles (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (Ah N a b c ) 1 l)
     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat 2%nat (pred N)). omega. omega. 
Qed.



Lemma eigen_belongs (a b c:R):
    forall (m N:nat), (2 < N)%nat -> (0 <= m < N)%nat -> a=c/\ 0<c-> (LHS m N a b c) = (RHS m N a b c).
Proof.
intros.
destruct H0 as [H0 H2].
unfold LHS. unfold RHS. unfold Mmult.
apply (mk_matrix_ext N 1%nat (fun i j : nat =>
   sum_n
     (fun l : nat =>
      mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
        (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
     (pred N))(fun i j : nat =>
   sum_n
     (fun l : nat =>
      mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) i l)
        (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 
     (pred 1))). 
intros. unfold sum_n.
cut((i=zero \/ ((i>zero)%nat) /\ ((i < (pred N)))%nat \/ (i= (pred N)))).
+ intros. destruct H5.
  - rewrite H5.
    cut(sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
             (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 
          (pred N)= sum_n_m (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
             (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat 1%nat + sum_n_m (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
             (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 2%nat (pred N)).
    * intros. rewrite H6.
      cut(sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 2 
            (pred N)=0).
      { intros. rewrite H7. 
        cut(sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 1 + 0= sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 1).
        + intros. rewrite H8.
          cut(sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 1= sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat 0%nat+ sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 1%nat 1%nat).
          - intros. rewrite H9. 
            assert(pred 1= 0%nat). { omega. } rewrite H10. 
            assert(sum_n_m
                    (fun l : nat =>
                     mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
                       (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 0= (fun l : nat =>
                     mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
                       (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat).
           { apply (sum_n_n (fun l : nat =>
                     mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
                       (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat). }
            rewrite H11.
            assert(sum_n_m
                    (fun l : nat =>
                     mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
                       (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 1 1=(fun l : nat =>
                     mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
                       (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 1%nat).
            { apply (sum_n_n (fun l : nat =>
                     mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
                       (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 1%nat). }
            rewrite H12.
            assert(sum_n_m
                    (fun l : nat =>
                     mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) zero l)
                       (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 0 0= (fun l : nat =>
                     mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) zero l)
                       (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 0%nat). 
            { apply (sum_n_n (fun l : nat =>
                     mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) zero l)
                       (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 0%nat).  }
            rewrite H13.
            assert ( j=0%nat). { omega. } rewrite H14. apply (i_0_j). omega. omega. nra.
          - apply (sum_n_m_Chasles (fun l : nat =>
                     mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
                       (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat 0%nat 1%nat). omega. omega. 
        + nra.
      }
      { cut (sum_n_m (fun _ => 0) 2%nat (pred N) = 0).
        + intros. rewrite <-H7. apply (sum_n_m_ext_loc (fun l : nat =>
                      mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l) (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) (fun _ : nat => 0) 2%nat (pred N)). 
          intros. 
          cut( coeff_mat Hierarchy.zero (Ah N a b c ) zero k =0).
          * intros. rewrite H9. apply (mult_zero_l (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) k j)).
          * apply (mat_prop_1  a b c k N ). apply H. apply H8.
        + apply (sum_const_zero 2%nat (pred N)). omega.
      }
    * apply (sum_n_m_Chasles (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) zero l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat 1%nat (pred N)). omega. omega. 
  - (* Case 2 on i *)
    destruct H5.
    cut( i= 1%nat \/ (1<i<pred N)%nat).
    * intros. destruct H6.
    { rewrite H6.  
      apply (i_eq_1 a b c m N i). apply H. nia. omega.  omega. nra.
    }
    { cut(sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 
            (pred N)= sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat (pred(pred i)) + sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) (S(pred(pred i))) (pred N)).
       + intros. rewrite H7. 
         cut((S(pred(pred i)))= pred i).
          - intros. rewrite H8. 
            cut(sum_n_m
                  (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                  (pred i) (pred N)= sum_n_m
                  (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) (pred i) (i+1)%nat +
                    sum_n_m
                  (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) (S (i+1)) (pred N)).
            * intros. rewrite H9. 
              assert (sum_n_m
                        (fun l : nat =>
                         mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                           (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0
                        (pred (pred i)) +
                      (sum_n_m
                         (fun l : nat =>
                          mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                            (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                         (pred i) (i + 1) +
                       sum_n_m
                         (fun l : nat =>
                          mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                            (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                         (S (i + 1)) (pred N))= sum_n_m
                                (fun l : nat =>
                                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0
                                (pred (pred i)) +
                              sum_n_m
                                 (fun l : nat =>
                                  mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                    (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                                 (pred i) (i + 1) +
                               sum_n_m
                                 (fun l : nat =>
                                  mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                    (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                                 (S (i + 1)) (pred N)). { nra. } rewrite H10.
               cut(sum_n_m
                      (fun l : nat =>
                       mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                         (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0
                      (pred (pred i))=0).
               { intros. rewrite H11. 
                  cut(sum_n_m
                      (fun l : nat =>
                       mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                         (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                      (S (i + 1)) (pred N)=0).
                  + intros. rewrite H12. 
                    assert(0 +
                            sum_n_m
                              (fun l : nat =>
                               mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                              (pred i) (i + 1) + 0=  sum_n_m
                              (fun l : nat =>
                               mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                              (pred i) (i + 1)). { nra. } rewrite H13. 
                    assert(pred 1= 0%nat). { omega. } rewrite H14.
                    cut(sum_n_m
                          (fun l : nat =>
                           mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                             (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                          (pred i) (i + 1)= sum_n_m
                          (fun l : nat =>
                           mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                             (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                          (pred i) (pred i) + sum_n_m
                          (fun l : nat =>
                           mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                             (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                          (S(pred i)) (i+1)%nat).
                    - intros. rewrite H15.
                      assert (S (pred i)= i). { omega. } rewrite H16.
                      cut(sum_n_m
                            (fun l : nat =>
                             mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) i 
                            (i + 1)= sum_n_m
                            (fun l : nat =>
                             mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) i i + sum_n_m
                            (fun l : nat =>
                             mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) (S i) (i+1)%nat).
                      * intros. rewrite H17. 
                        assert (S i = (i+1)%nat). { omega. } rewrite H18.
                        assert(sum_n_m
                                (fun l : nat =>
                                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                                (pred i) (pred i) +
                              (sum_n_m
                                 (fun l : nat =>
                                  mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                    (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) i i +
                               sum_n_m
                                 (fun l : nat =>
                                  mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                    (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                                 (i + 1) (i + 1))=sum_n_m
                                    (fun l : nat =>
                                     mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                       (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                                    (pred i) (pred i) +
                                  sum_n_m
                                     (fun l : nat =>
                                      mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                        (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) i i +
                                   sum_n_m
                                     (fun l : nat =>
                                      mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                        (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                                     (i + 1) (i + 1)). { nra. } rewrite H19.
                      assert(sum_n_m
                              (fun l : nat =>
                               mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                              (pred i) (pred i)= (fun l : nat =>
                               mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                              (pred i)).
                      { apply (sum_n_n (fun l : nat =>
                               mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                              (pred i)). } rewrite H20.
                      assert(sum_n_m
                              (fun l : nat =>
                               mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) i i= (fun l : nat =>
                               mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) i).
                      { apply (sum_n_n (fun l : nat =>
                               mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) i). } rewrite H21.
                      assert (sum_n_m
                                (fun l : nat =>
                                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                                (i + 1) (i + 1)= (fun l : nat =>
                                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                                (i + 1)%nat).
                      { apply (sum_n_n (fun l : nat =>
                                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                                (i + 1)%nat). } rewrite H22.
                      assert(sum_n_m
                              (fun l : nat =>
                               mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) i l)
                                 (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 0 0= (fun l : nat =>
                               mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) i l)
                                 (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 0%nat).
                      { apply (sum_n_n (fun l : nat =>
                               mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) i l)
                                 (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 0%nat). } rewrite H23.
                      assert ( j= 0%nat). { omega. } rewrite H24.
                      apply (i_j  a b c m N). omega. omega. omega. nra.
                    * apply (sum_n_m_Chasles (fun l : nat =>
                                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) i i (i+1)%nat). omega. omega. 
                  - apply (sum_n_m_Chasles (fun l : nat =>
                             mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) (pred i) (pred i) (i+1)%nat). omega. omega.
               +  cut( ((S (i+1)) <= (pred N))%nat \/ ((S (i+1)) > (pred N))%nat).
                  - intros. destruct H12.
                    * cut( sum_n_m (fun _ => 0) (S(i+1)) (pred N) = 0).
                      { intros. rewrite <- H13. 
                        apply (sum_n_m_ext_loc (fun l : nat =>
                                         mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                           (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) (fun _ : nat => 0) (S(i+1)) (pred N)). intros. 
                        cut((coeff_mat Hierarchy.zero (Ah N a b c ) i k)=0).
                        + intros. rewrite H15. apply (mult_zero_l ((coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) k j))).
                        + apply (mat_prop_3  a b c i k m N). apply H. omega. apply H12. apply H14. 
                      } 
                      { apply (sum_const_zero (S (i+1)) (pred N)). apply H12. }
                   * apply (sum_n_m_zero (fun l : nat =>
                                         mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                           (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j))). apply H12.
                - omega.
            }
            {  cut(i=2%nat \/ (2<i<N)%nat).
                        - intros. destruct H11.
                          * intros. rewrite H11.
                            cut( pred(pred 2)= 0%nat).
                            {  intros. rewrite H12.
                                cut(sum_n_m
                                (fun l : nat =>
                                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) 2 l)
                                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 0=  (fun l : nat =>
                                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) 2 l)
                                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat). 
                               + intros. rewrite H13. 
                                 cut(coeff_mat Hierarchy.zero (Ah N a b c ) 2 0 = 0).
                                 - intros. rewrite H14. apply (mult_zero_l (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) 0 j)). 
                                 - apply (mat_prop_4  a b c N). nia. 
                               + apply (sum_n_n (fun l : nat =>
                                           mult (coeff_mat Hierarchy.zero (Ah N a b c ) 2 l)
                                             (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j))).
                            }
                            { nia. }
                         * cut (sum_n_m (fun _ =>0) 0%nat (pred(pred i)) = 0).
                          + intros. rewrite <- H12. apply (sum_n_m_ext_loc (fun l : nat =>
                                             mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                                               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) (fun _ : nat => 0) 0%nat (pred(pred i))).
                            intros. 
                            cut( (coeff_mat Hierarchy.zero (Ah N a b c ) i k) = 0).
                            { intros. rewrite H14. apply (mult_zero_l (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) k j)). }
                            { apply (mat_prop_6  a b c i k N). nia. nia. nia. }
                          + apply (sum_const_zero 0%nat (pred (pred i))). omega.
                      -  omega.
            }
          * apply (sum_n_m_Chasles (fun l : nat =>
                     mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                       (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) (pred i) (i+1)%nat (pred N)). omega. omega.
        - omega.
      + apply (sum_n_m_Chasles  (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) i l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat (pred(pred i)) (pred N)). omega. omega.
     }
    * omega.
  - (* Case 3 on i *)
    rewrite H5.
    cut(sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
             (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 
          (pred N)= sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 (N-3)%nat+ sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) (S(N-3)) (pred N)).
    * intros. rewrite H6. 
      cut(sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0 
            (N - 3)=0).
      { intros. rewrite H7. 
        assert(0 +
              sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                (S (N - 3)) (pred N)= sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                (S (N - 3)) (pred N)). { nra. } rewrite H8. 
       assert (S (N-3)= (N-2)%nat). { omega. } rewrite H9.
       cut(sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
            (N - 2) (pred N)= sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) (N-2)%nat (N-2)%nat+sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) (S(N-2)) (pred N)).
      + intros. rewrite H10. 
        assert( S(N-2)= pred N). { omega. } rewrite H11. 
        assert (pred 1 = 0%nat). { omega. } rewrite H12.
        assert(sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                (N - 2) (N - 2)= (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                (N - 2)%nat).
        { apply (sum_n_n (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
                (N - 2)%nat). } rewrite H13.
        assert(sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
              (pred N) (pred N)= (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
              (pred N)). 
        { apply (sum_n_n (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
                 (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 
              (pred N)).  } rewrite H14.
        assert (sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) (pred N) l)
                   (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 0 0= (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) (pred N) l)
                   (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 0%nat). 
        { apply (sum_n_n (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) (pred N) l)
                   (coeff_mat Hierarchy.zero (Lambda m N a b c ) l j)) 0%nat). } rewrite H15.
        assert ( j=0%nat). { omega. } rewrite H16.
        apply (i_predN_j ). omega. omega. nra.  
      + apply (sum_n_m_Chasles  (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
                     (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) (N-2)%nat (N-2)%nat (pred N)). omega. omega.
    }
  { cut( N=3%nat \/ (3<N)%nat).
    { intros. destruct H7.
      + rewrite H7. assert((3-3)%nat=0%nat). { omega. } rewrite H8.
        assert (sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (Ah 3 a b c) (pred 3) l)
                   (coeff_mat Hierarchy.zero (Eigen_vec m 3 a b c) l j)) 0 0= (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero (Ah 3 a b c) 2 l)
                     (coeff_mat Hierarchy.zero (Eigen_vec m 3 a b c) l j)) 0%nat).
        { apply (sum_n_n (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero (Ah 3 a b c) 2 l)
                     (coeff_mat Hierarchy.zero (Eigen_vec m 3 a b c) l j)) 0%nat). } rewrite H9.
          assert(j=0%nat). { omega. } rewrite H10.
          cut(coeff_mat Hierarchy.zero (Ah 3 a b c) 2 0=0).
          - intros. rewrite  H11. apply Rmult_0_l. 
          - apply (mat_prop_4 ). omega.
      + cut(sum_n_m (fun _ => 0) 0%nat (N-3)%nat = 0).
        - intros. rewrite <- H8. apply (sum_n_m_ext_loc   (fun l : nat =>
                             mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
                               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j))  (fun _ : nat => 0)  0%nat (N-3)%nat). 
          intros. 
          cut((coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) k)=0).
          * intros. rewrite H10. apply (mult_zero_l (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) k j)).
          * apply (mat_prop_5 a b c i k N). omega. omega.
        - apply (sum_const_zero 0%nat (N-3)%nat). nia.
     }
     { omega. }
  }
  { apply (sum_n_m_Chasles (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (Ah N a b c ) (pred N) l)
               (coeff_mat Hierarchy.zero (Eigen_vec m N a b c ) l j)) 0%nat (N-3)%nat (pred N)). omega. omega. }
+ clear H1 H2 H4 H0. destruct i.
  - left. reflexivity. 
  - right.  
    cut(S i = pred N \/ ((S i) < pred N)%nat).
    * intros. destruct H0 as [H0 | H1]. right. apply H0. left. split.
      cut((S i >= zero)%nat /\ (zero <> (S i))).
      { intros. omega.  }
      { split. apply (le_0_n (S i)). apply (O_S i). }
  apply H1. omega.
Qed.

