Require Import Reals Psatz.
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.Rbar.
Require Import Top.linear_map.
Require Import Top.continuous_linear_map.
Require Import Omega Init.Nat Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import Ah_properties.
Require Import Eigen_system.

Variable h:R. (* h is the discretization step *)
Hypothesis h_gt_0: 0<h. (* assumption that the discretization step > 0 *)

Lemma inv_sqr_h_ge_0: 0 <= 1 * / (h * h).
Proof.
assert( 0< h -> 0 <= 1 * / (h * h)). { intros. apply Rlt_le. assert( 0<h -> 0<(h*h)). { nra. }
assert(0 < h * h->0 < 1 * / (h * h)). 
assert(1 * / (h * h)= /(h*h)). { nra. } rewrite H1.  apply (Rinv_0_lt_compat (h*h)).
apply H1. nra. } apply H. apply h_gt_0.
Qed.


Lemma N_not_zero: forall N:nat, (2<N)%nat -> INR (N+1) <> 0.
Proof.
intros.
assert ( 0 < INR (N+1) -> INR (N+1) <> 0). { nra. } apply H0.
apply lt_0_INR. omega.
Qed.

Require Import R_sqrt Rpower.

(** This is where we instatiate the eigen value for Ah(a, b, a) with a= (1/h^2), b= -2 / (h^2) **)
Lemma lambda : forall (m N:nat) , (2<N)%nat -> (0<=m<N)%nat ->
  coeff_mat 0 (Lambda m N (1/(h^2)) (-2/ (h^2)) (1/(h^2))) 0%nat 0%nat= - (4/ (h^2))* (sin ( (INR (m+1) * PI)*/(2* INR (N+1))))^2.
Proof.
intros. unfold Lambda.
assert (coeff_mat 0
        (mk_matrix 1 1
           (fun _ _ : nat =>
            -2 / h ^ 2 + 2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR (m + 1) * PI * / INR (N + 1)))) 0 0=(fun _ _ : nat =>
            -2 / h ^ 2 + 2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR (m + 1) * PI * / INR (N + 1))) 0%nat 0%nat).
{ apply (coeff_mat_bij 0 (fun _ _ : nat =>
            -2 / h ^ 2 + 2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR (m + 1) * PI * / INR (N + 1))) 0%nat 0%nat).
  omega. omega.
} rewrite H1.
assert (sqrt (1 / h ^ 2 * (1 / h ^ 2))= (1 / h ^ 2)). { apply sqrt_square. assert (h^2 = h* h). { nra. } rewrite H2. apply inv_sqr_h_ge_0. }
rewrite H2.
assert (-2 / h ^ 2 + 2 * (1 / h ^ 2) * cos (INR (m + 1) * PI * / INR (N + 1))=
          (2 / h ^ 2) * (-1+  cos (INR (m + 1) * PI * / INR (N + 1)))). { nra. } rewrite H3.
cut((-1 + cos (INR (m+1) * PI * / INR (N + 1)))= -2* sin (INR (m+1) * PI * / (2 * INR (N + 1))) ^ 2).
+ intros. rewrite H4. nra.
+ assert(cos (INR (m+1) * PI * / INR (N + 1))= cos (2* ((INR (m+1) * PI)*/(2* INR (N+1))))).
  { assert((INR (m+1) * PI * / INR (N + 1))= (2 * (INR (m+1) * PI * / (2 * INR (N + 1))))).
    { assert(/ (2 * INR (N + 1))= (/2)* (/ INR (N+1))). { apply Rinv_mult_distr. nra. apply N_not_zero. omega. } rewrite H4. nra. }
      rewrite H4. reflexivity.
    } rewrite H4.
  assert (-2 * sin (INR (m+1) * PI * / (2 * INR (N + 1))) ^ 2= -1 + (1-2 * sin (INR (m+1) * PI * / (2 * INR (N + 1))) ^ 2)).
  { nra. } rewrite H5.
  apply Rplus_eq_compat_l. 
  assert (sin (INR (m+1) * PI * / (2 * INR (N + 1))) ^ 2= sin (INR (m+1) * PI * / (2 * INR (N + 1)))* sin (INR (m+1) * PI * / (2 * INR (N + 1)))). { nra. } rewrite H6.
  assert (2 * (sin (INR (m+1) * PI * / (2 * INR (N + 1))) * sin (INR (m+1) * PI * / (2 * INR (N + 1))))=
                2 * sin (INR (m+1) * PI * / (2 * INR (N + 1))) * sin (INR (m+1) * PI * / (2 * INR (N + 1)))). { nra. } rewrite H7.
  apply cos_2a_sin.
Qed.

(*** Proving the uniform boundedness of 1/ | lambda_min| for Ah (1/h^2, -2/h^2, 1/h^2) **)

(* Define a real valued concae function *)
Definition concave (f:R->R) (x y c:R):= 0<=c<=1 ->f(c*x + (1-c) * y) >= c* f x + (1-c) * f y.

Lemma inverse_a_b: forall (a b:R), (a <> 0) /\ (b<>0)-> a/b= 1/(b/a).
Proof.
intros.
assert ( 1 / (b / a)= /(b * /a)). { nra. } rewrite H0.
assert (/ (b * / a)= /b * //a). { apply Rinv_mult_distr. nra. apply Rinv_neq_0_compat. nra. }
rewrite H1. assert ( / / a= a). { apply Rinv_involutive. nra. } rewrite H2. nra.
Qed.


Definition g (f:R-> R)(pr:derivable f) (x:R):= derive_pt f x (pr x).

(** Stating the property of a concave function that in the interval [a,b], the 2nd derivative of a differentiable function g is <=0 ***)
Hypothesis concave_def: forall (f:R->R) (g:R->R) (a b c x:R) (pr: derivable f) (pr1:derivable g), a<=x<=b -> concave f a b c<-> 
      derive_pt g x (pr1 x) <=0.


Lemma sin_concave_1 (x:R) : 0<=x<=PI/2 -> concave sin 0 (PI / 2) (1-(2/PI)*x).
Proof.
intros.
assert (concave sin 0 (PI/2) (1-(2/PI)*x)<-> derive_pt cos x (derivable_pt_cos x) <=0). { apply (concave_def sin  cos 0 (PI/2) (1-(2/PI)*x) x  ( derivable_pt_sin) (derivable_pt_cos )).  nra. } 
destruct H0.
apply H1. 
assert (derive_pt cos x (derivable_pt_cos x)= -sin x). { apply derive_pt_cos. } rewrite H2.
assert ( 0 = -0). { nra. } rewrite H3.
apply Ropp_le_contravar.
apply sin_ge_0. nra. nra.
Qed.

Lemma sin_concave (x:R):0<=x<=PI/2 ->  sin x >= 2 / PI * x <-> concave sin 0 (PI/2) (1-(2/PI)*x).
Proof.
split.
+ intros. unfold concave.
  intros.
  assert(sin 0 = 0). { apply sin_0. } rewrite H2.
  assert (sin (PI/2) =1). { apply sin_PI2. } rewrite H3.
  assert ((1 - 2 / PI * x) * 0=0). { nra. } rewrite H4. 
  assert ((1 - (1 - 2 / PI * x)) * 1= (2/PI)*x). { nra. } rewrite H5. 
  assert ((1 - (1 - 2 / PI * x)) * (PI / 2)=x). 
  { assert ((1 - (1 - 2 / PI * x))= (2/PI)*x). { nra. } rewrite H6.
    assert (2 / PI * x * (PI / 2)= ((2/PI)* (PI/2))*x). { nra. } rewrite H7.
    assert (2 / PI * (PI / 2)=1).
    { assert (2 / PI= 1/ (PI/2)).  apply (inverse_a_b 2 PI). 
      split.
      - nra.
      - apply PI_neq0.
      rewrite H8. 
      assert (1 / (PI / 2)= / (PI / 2)). { nra. } rewrite H9.
      symmetry. apply Rinv_l_sym .  
      assert (0 < (PI/2) -> PI / 2 <> 0). { nra. } apply H10. apply PI2_RGT_0.
    } rewrite H8. nra.
  } 
  assert (0 + (1 - (1 - 2 / PI * x)) * (PI / 2)= x). { nra. } rewrite H7.
  assert (0 + 2 / PI * x= 2 / PI * x). { nra. } rewrite H8. apply H0.
+ intros.
  unfold concave in H0. 
    assert ( 0 <= 1 - 2 / PI * x <= 1). 
    { split.
      - assert ( 0 = 1-1). { nra. } rewrite H1.
        apply Rplus_le_compat_l. apply Ropp_ge_le_contravar. 
        assert ( 1= (/ (PI /2)) * (PI/2)). { apply Rinv_l_sym.  
        assert (0 < (PI/2) -> PI / 2 <> 0). { nra. } apply H2. apply PI2_RGT_0. }
       rewrite H2.
        assert ( 2/ PI = /(PI/2)). 
        { assert (/ (PI / 2)= 1/ (PI/2)).  { nra. } rewrite H3. apply inverse_a_b. 
          split. nra. apply PI_neq0. } rewrite H3.
        apply Rmult_ge_compat_l. nra.  nra.
      - assert (1= 1-0). { nra. } rewrite H1.
        assert ( 1 - 0 - 2 / PI * x= 1 - 2 / PI * x). { nra. } rewrite H2.
        apply Rplus_le_compat. nra.
        apply Ropp_ge_le_contravar. 
        assert (0 =(2/PI)*0). { nra. } rewrite H3. apply Rmult_ge_compat_l. 
        apply Rle_ge. apply Rlt_le. 
        assert (2 / PI= 1/ (PI/2)). { apply inverse_a_b. split. nra. apply PI_neq0. } rewrite H4.
        assert (1 / (PI / 2)= / (PI/2)). { nra. } rewrite H5. apply Rinv_0_lt_compat. apply PI2_RGT_0. nra.
    }
    specialize (H0 H1). 
    assert(sin 0 = 0). { apply sin_0. } rewrite H2 in H0.
    assert (sin (PI/2) =1). { apply sin_PI2. } rewrite H3 in H0.
    assert ((1 - 2 / PI * x) * 0=0). { nra. } rewrite H4 in H0. 
    assert ((1 - (1 - 2 / PI * x)) * 1= (2/PI)*x). { nra. } rewrite H5 in H0.
    assert ((1 - (1 - 2 / PI * x)) * (PI / 2)=x). 
    { assert ((1 - (1 - 2 / PI * x))= (2/PI)*x). { nra. } rewrite H6.
      assert (2 / PI * x * (PI / 2)= ((2/PI)* (PI/2))*x). { nra. } rewrite H7.
      assert (2 / PI * (PI / 2)=1).
      { assert (2 / PI= 1/ (PI/2)).  apply (inverse_a_b 2 PI). 
        split.
        - nra.
        - apply PI_neq0.
        rewrite H8. 
        assert (1 / (PI / 2)= / (PI / 2)). { nra. } rewrite H9.
        symmetry. apply Rinv_l_sym .  
        assert (0 < (PI/2) -> PI / 2 <> 0). { nra. } apply H10. apply PI2_RGT_0.
      } rewrite H8. nra.
    } 
    assert (0 + (1 - (1 - 2 / PI * x)) * (PI / 2)= x). { nra. } rewrite H7 in H0.
    assert (0 + 2 / PI * x= 2 / PI * x). { nra. } rewrite H8 in H0. apply H0.
Qed.


Lemma limit_trigo : forall x:R, 0<=x<=(PI/2) -> (2* x)/PI <= sin x.
Proof.
intros.
apply Rge_le. 
assert (sin x >= 2 / PI * x <-> concave sin 0 (PI/2) (1-(2/PI)*x)). { apply sin_concave. nra. } 
destruct H0. 
assert (2 * x / PI= 2 / PI * x). { nra. } rewrite H2. apply H1. apply sin_concave_1. nra.
Qed.


Lemma spectral_intermed: forall x:R, 0<x<=PI/2 -> (x^2)/ (sin x)^2 <= (PI^2)/4.
Proof.
intros.
assert (x ^ 2 / sin x ^ 2= Rsqr ( x / sin x)). 
{ assert ( x^2 = Rsqr x). { simpl. unfold Rsqr. nra. } rewrite H0.
  assert (sin x ^ 2= Rsqr (sin x)). { simpl. unfold Rsqr. nra. } rewrite H1.
  symmetry. apply Rsqr_div. 
  assert (0< sin x -> sin x <> 0). { nra. } apply H2. apply sin_gt_0. nra. nra. 
} rewrite H0.
assert (PI ^ 2 / 4= Rsqr (PI/2)).
{ assert (PI^2 = Rsqr PI). { simpl. unfold Rsqr. nra. } rewrite H1.
  assert (4 = Rsqr 2). { auto. } rewrite H2. symmetry. apply Rsqr_div. auto. }
  rewrite H1.
  apply Rsqr_incr_1.
  apply Rmult_le_reg_r with (2/PI). 
  assert ( 2/ PI = 1/ (PI/2)). { apply inverse_a_b. nra. } rewrite H2.
  assert (1 / (PI / 2)= / (PI/2)). { nra. } rewrite H3. apply Rinv_0_lt_compat. nra.
  assert (PI / 2 * (2 / PI)=1). 
  { assert ((2 / PI)= 1/ (PI/2)). { apply inverse_a_b. nra. } rewrite H2.
    assert ((1 / (PI / 2))= / (PI/2)). { nra. } rewrite H3. apply Rinv_r. nra.
  }   rewrite H2.
  apply Rmult_le_reg_r with (sin x).
  apply sin_gt_0. nra. nra.
  assert (x / sin x * (2 / PI) * sin x= (x * 2/PI) * (/sin x * sin x)). { nra. } rewrite H3.
  assert ((/ sin x * sin x)= 1). { symmetry. apply Rinv_l_sym. assert ( 0< sin x -> sin x <> 0). { nra. } apply H4.
  apply sin_gt_0. nra. nra. }
  rewrite H4.
  assert ( (2* x)/PI= x * 2 / PI * 1). { nra. } rewrite <- H5.
  assert (1 * sin x= sin x). { nra. } rewrite H6. apply limit_trigo. nra.
  apply Rlt_le. assert (x / sin x= x* (/sin x)). { nra. } rewrite H2. 
  apply Rmult_lt_0_compat. nra. apply Rinv_0_lt_compat. apply sin_gt_0. nra. nra. nra.
Qed.

(*** Define the minimum eigen value for Ah (1/h^2, -2/(h^2), 1/h^2). m=1 ***)
Definition Lambda_min (N:nat):= (-2/(h^2)) + 2 * (1/(h^2)) * cos (INR 1 * PI * / INR (N + 1)).

Variable L:R. (* L is the length of the domain *)
Hypothesis L_ge_0: 0< L.

Lemma L_PI_gt_0 (L:R): 0 < L /\ 0 < PI -> 0 < L / PI.
Proof.
intros. 
assert ( L / PI= L * (/PI)). { nra. } rewrite H0.
apply Rmult_lt_0_compat. nra. apply Rinv_0_lt_compat. nra.
Qed.


Hypothesis h_L: forall (N:nat), h = L/ INR (N+1). 

Lemma inv_gt_0: forall a b:R, 0<a /\ 0< b -> 0< a/b.
Proof.
intros.
assert (a / b= a * (/b)). { nra. } rewrite H0. apply Rmult_lt_0_compat.
+ nra.
+ apply Rinv_0_lt_compat. nra.
Qed.

(*** Proof that 1/|lambda_min| for Ah (1/h^2, -2/h^2, 1/h^2) is uniformly bounded by L^2/4 **)
Lemma spectral : forall N:nat , (2<N)%nat -> 1/ Rabs( Lambda_min N) <= L^2 / 4.
Proof.
intros.
cut ( 1 / Rabs (Lambda_min  N)= (L^2/ (PI^2)) * ( (PI/ (2* INR (N+1)))^2 / (sin (PI/ (2* INR (N+1))))^2)).
+ intros. rewrite H0.
  assert (( (PI/ (2* INR (N+1)))^2 / (sin (PI/ (2* INR (N+1))))^2)<= (PI^2)/4).
  { apply spectral_intermed.
    split.
    + assert ( 0< PI /\ 0<(2 * INR (N + 1)) -> 0 < PI / (2 * INR (N + 1))). { apply inv_gt_0. }
      apply H1.
      split.
      - apply PI_RGT_0.
      - apply Rmult_lt_0_compat. nra. apply lt_0_INR. omega.
    + assert (PI / (2 * INR (N + 1))= PI * /(2 * INR (N + 1))). { nra. } rewrite H1.
      assert (PI / 2= PI * (/2)). { nra. } rewrite H2.
      apply Rmult_le_compat_l. apply Rlt_le. apply PI_RGT_0.
      apply Rlt_le. apply Rinv_1_lt_contravar. nra. 
      assert (2= 2* 1). { nra. } rewrite H3.
      assert (2 * 1 * INR (N + 1)= 2* (INR (N+1))). { nra. } rewrite H4.
      apply Rmult_lt_compat_l. nra.
      apply lt_1_INR. omega.
  }
  assert (L ^ 2 / 4= (L^2 /(PI^2)) * (PI^2/4)).  
  {  assert ( L ^ 2 / PI ^ 2 * (PI ^ 2 / 4)= (L^2/4) * ( / (PI^2) * (PI^2))). { nra. } rewrite H2.
     assert ( 1= ( / (PI^2) * (PI^2))). { apply Rinv_l_sym. assert ( PI <> 0 -> PI ^ 2 <> 0). { nra. } apply H3. apply PI_neq0. }
  rewrite <-H3. nra.
  } rewrite H2.
  apply Rmult_le_compat_l.  apply Rlt_le.
  assert (0< L/PI ->  0 <L ^ 2 / PI ^ 2). 
  { intros. 
    assert (L ^ 2 = Rsqr L). { simpl. unfold Rsqr. nra. } rewrite H4.
    assert (PI ^ 2= Rsqr PI). { simpl. unfold Rsqr. nra. } rewrite H5.
    assert (Rsqr (L/PI) = L² / PI²). { apply Rsqr_div. apply PI_neq0. } rewrite <- H6.
    apply Rsqr_pos_lt.
    assert (0 < L/PI -> L / PI <> 0). { nra. } apply H7. apply L_PI_gt_0. split. apply L_ge_0. apply PI_RGT_0.
  }
  apply H3.
  apply L_PI_gt_0. split. apply L_ge_0. apply PI_RGT_0. apply H1.
+ assert ( (Lambda_min  N)<0 -> Rabs (Lambda_min  N)= - (Lambda_min  N)). 
  { apply Rabs_left. } rewrite H0.
  unfold Lambda_min. 
  cut ((-2/(h^2))  + 2 * (1/(h^2))* cos (INR 1 * PI * / INR (N + 1))= (2*/ (h^2))* (-1+ cos (INR 1 * PI * / INR (N + 1)))).
  - intros. rewrite H1.
    assert ((-1 + cos (INR 1 * PI * / INR (N + 1)))= -2 *sin (PI / (2 * INR (N + 1))) ^ 2).
    { assert (INR 1 * PI * / INR (N + 1)= 2* (PI/ (2* INR (N+1)))).
      { assert (INR 1= 1). { reflexivity. } rewrite H2. 
      assert (1=2* (/2)). { nra. } rewrite H3.
      assert (2 * / 2 * PI * / INR (N + 1)= (2* PI) * (/2 * / INR (N+1))). { nra. } rewrite H4.
      assert (2 * (PI / (2 * INR (N + 1)))= (2* PI) * (/ (2* INR (N+1)))). { nra. } rewrite H5.
      apply Rmult_eq_compat_l. symmetry. apply Rinv_mult_distr. nra. 
      assert (0 < INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H6.
      apply lt_0_INR. omega.
    } rewrite H2.
    assert ( -2 * sin (PI / (2 * INR (N + 1))) ^ 2= -1 + (1 -2 * sin (PI / (2 * INR (N + 1))) ^ 2)). { nra. } rewrite H3.
    apply Rplus_eq_compat_l. 
    assert (1 - 2 * sin (PI / (2 * INR (N + 1))) ^ 2= 1 - 2 * sin (PI / (2 * INR (N + 1)))* sin (PI / (2 * INR (N + 1)))). { nra. } rewrite H4.
    apply cos_2a_sin.
    }
    rewrite H2.
    assert (-(2 * / h ^ 2 * (-2 * sin (PI / (2 * INR (N + 1))) ^ 2))= (4* / (h^2)) * sin (PI / (2 * INR (N + 1)))^2). { nra. } 
    rewrite H3.
    assert (1 /(4 * / h ^ 2 * sin (PI / (2 * INR (N + 1))) ^ 2)= / ((4* / (h^2)) * (sin (PI / (2 * INR (N + 1))) ^ 2))).
    { nra. } rewrite H4.
    assert (/ ((4* / (h^2)) * (sin (PI / (2 * INR (N + 1))) ^ 2))= / (4/ (h^2)) * /(sin (PI / (2 * INR (N + 1))) ^ 2)).
    { apply Rinv_mult_distr. 
      assert (0 < 4/ (h^2) -> 4 / h ^ 2 <> 0). { nra. } apply H5. 
      assert ( 4 / h ^ 2= 4 * (/ h^2)). { nra. } rewrite H6.
      apply Rmult_lt_0_compat. nra. apply Rinv_0_lt_compat. 
      assert (0< h -> 0 < h ^ 2). { nra. } apply H7. apply h_gt_0.
      assert (sin (PI / (2 * INR (N + 1))) <> 0 -> sin (PI / (2 * INR (N + 1))) ^ 2 <> 0). { nra. } apply H5.
      assert (0 < sin (PI / (2 * INR (N + 1))) -> sin (PI / (2 * INR (N + 1))) <> 0). { nra. } apply H6.
      assert ( sin 0 = 0). { apply sin_0. } rewrite <- H7.
      apply sin_increasing_1. assert (0=-0). { nra. } rewrite H8. 
      apply Ropp_ge_le_contravar. apply Rgt_ge. apply PI2_RGT_0. apply Rlt_le. apply PI2_RGT_0.
      apply Rle_trans with 0. assert (0=-0). { nra. } rewrite H8. 
      apply Ropp_ge_le_contravar. apply Rgt_ge. apply PI2_RGT_0. apply Rlt_le. assert (0 = PI * 0). { nra. } rewrite H8.
      assert (PI / (2 * INR (N + 1))= PI * (/ (2 * INR (N + 1)))). { nra. } rewrite H9. apply Rmult_lt_compat_l.
      apply PI_RGT_0. apply Rinv_0_lt_compat. assert (0=2* 0). { nra. } rewrite H10. apply Rmult_lt_compat_l. nra. apply lt_0_INR. omega.
      apply Rlt_le. assert (PI / (2 * INR (N + 1))= PI * (/ (2* INR (N+1)))). { nra. } rewrite H8.
      assert (PI / 2= PI * (/2)). { nra. } rewrite H9. apply Rmult_lt_compat_l. apply PI_RGT_0. apply Rinv_1_lt_contravar. nra. 
      assert (2= 2 * 1). { nra. } rewrite H10. 
      assert (2 * 1 * INR (N + 1)= 2* INR (N+1)). { nra. } rewrite H11. apply Rmult_lt_compat_l.
      nra. apply lt_1_INR. omega.
      assert ( 0 = PI * 0). { nra. } rewrite H8.
      assert ( PI / (2 * INR (N + 1))= PI * (/ (2* INR (N+1)))). { nra. } rewrite H9.
      apply Rmult_lt_compat_l. apply PI_RGT_0. apply Rinv_0_lt_compat. assert (0=2* 0). { nra. } rewrite H10.
      apply Rmult_lt_compat_l. nra. apply lt_0_INR. omega.
    }
    rewrite H5. 
    assert (/ (4 / h ^ 2) = 1/ (4 / h ^ 2)). { nra. } rewrite H6.
    assert ( (h^2)/4 = 1 / (4 / h ^ 2)). { apply inverse_a_b. split.
     assert (0<h -> h ^ 2 <> 0). { nra. } apply H7. apply h_gt_0. nra. }
    rewrite <-H7.
    assert (h ^ 2 / 4= L ^ 2 / PI ^ 2 * (PI / (2 * INR (N + 1))) ^ 2). 
    { assert (h= L/ INR (N+1)). { apply h_L. } rewrite H8.
      assert ((L / INR (N + 1)) ^ 2= (L^2) / (INR (N+1))^2). 
      { assert ((L / INR (N + 1)) ^ 2= Rsqr (L/ INR (N+1))). { simpl. unfold Rsqr. nra. } rewrite H9.
        assert (L ^ 2 = Rsqr L). { simpl. unfold Rsqr. nra. } rewrite H10.
        assert (INR (N + 1) ^ 2= Rsqr (INR (N+1))). { simpl. unfold Rsqr. nra. } rewrite H11.
        apply Rsqr_div. assert ( 0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H12. apply lt_0_INR. omega. 
      }
      assert ( 4= Rsqr 2). { auto. } rewrite H10.
      assert ((L / INR (N + 1)) ^ 2= Rsqr ( L/ INR (N+1))). 
      { simpl. unfold Rsqr. nra. } rewrite H11.
      assert (Rsqr ((L / INR (N + 1))/ 2)= (L / INR (N + 1))² / 2²). { apply Rsqr_div. nra. } rewrite <-H12.
      assert (L / INR (N + 1) / 2= L * (/INR (N+1)) * /2). { nra. } rewrite H13.
      assert (L * (/INR (N+1)) * /2= L * (/ INR (N+1) * /2)). { nra. } rewrite H14.
      assert ( / (INR (N+1) * 2) =(/ INR (N+1) * /2)). { apply Rinv_mult_distr. 
        assert (0< INR (N+1) -> INR (N + 1) <> 0). { nra. } apply H15. apply lt_0_INR. omega. nra. }
      rewrite<- H15.
      assert ((INR (N + 1) * 2) = 2* INR (N+1)). { apply Rmult_comm. } rewrite H16. 
      assert (PI * / (2* INR (N+1)) * (L */ PI) = L * / (2 * INR (N + 1))). { apply Rinv_mult_simpl. apply PI_neq0. } rewrite <-H17.
      assert ((L * / PI)= L/ PI). { nra. } rewrite H18.
      assert (PI * / (2 * INR (N + 1))= PI/ (2* INR (N+1))). { nra. } rewrite H19.
      assert ((PI / (2 * INR (N + 1)) * (L / PI))² = Rsqr (PI/ (2* INR (N+1))) * Rsqr (L/PI)). { apply Rsqr_mult. } rewrite H20.
      assert (L ^ 2 / PI ^ 2= Rsqr (L/PI)). 
      { assert (L ^ 2= Rsqr L). { simpl. unfold Rsqr. nra. } rewrite H21.
        assert (PI ^ 2= Rsqr PI). { simpl. unfold Rsqr. nra. } rewrite H22.
        symmetry.  apply Rsqr_div. apply PI_neq0. 
      } rewrite H21.
      assert ((PI / (2 * INR (N + 1))) ^ 2= Rsqr (PI/ (2* INR (N+1)))). 
      { simpl. unfold Rsqr. nra. } rewrite H22. nra.
     } rewrite H8. nra.
  - nra.
unfold Lambda_min. 
assert (-2 / h ^ 2 +2 * (1 / h ^ 2) *cos (INR 1 * PI * / INR (N + 1))= (2/ h^2) * (-1 + cos (INR 1 * PI * / INR (N + 1)))).
{ nra. } rewrite H1.
assert (0= (2/ h^2) * 0). { nra. } rewrite H2.
apply Rmult_lt_compat_l. assert ( 0 = 2* 0). { nra. } rewrite H3.
assert ( 2 / h ^ 2= 2* (/ h^2)). { apply Rmult_eq_compat_l. reflexivity. } rewrite H4. apply Rmult_lt_compat_l. nra.
apply Rinv_0_lt_compat. assert ( 0 < h -> 0< h ^ 2). { nra. } apply H5. apply h_gt_0.
assert (0=-1+1). { nra. } rewrite H3.
apply Rplus_lt_compat_l.
assert ((INR 1 * PI * / INR (N + 1))= PI / INR (N + 1)).
{ assert (INR 1 = 1). { reflexivity. } rewrite H4. nra. } rewrite H4.
assert (cos 0 =1). { apply cos_0. } rewrite <- H5.
apply cos_decreasing_1. nra. apply Rlt_le. apply PI_RGT_0. apply Rlt_le.
assert (0 = PI * 0). { nra. } rewrite H6.
assert (PI / INR (N + 1)= PI * (/ INR (N+1))). { nra. } rewrite H7.
apply Rmult_lt_compat_l. apply PI_RGT_0. apply Rinv_0_lt_compat. apply lt_0_INR. omega.
apply Rlt_le. assert (PI= PI * 1). { nra. } rewrite H6.
assert (PI * 1 / INR (N + 1)= PI * (/INR (N+1))). { nra. } rewrite H7.
apply Rmult_lt_compat_l. apply PI_RGT_0. assert (1 = /1). { nra. } rewrite H8. apply Rinv_1_lt_contravar. nra.
apply lt_1_INR. omega.
assert (0= PI * 0). { nra. } rewrite H6.
assert ( PI / INR (N + 1)= PI * (/ INR (N+1))). { nra. } rewrite H7.
apply Rmult_lt_compat_l. apply PI_RGT_0. apply Rinv_0_lt_compat. apply lt_0_INR. omega.
Qed.


(* Proof that for any vector v , y^{T} * \Lambda ^{-2} y = \sum y_{i}^2/ \lambda_{i} *)

Definition lam (j N:nat) (a b c:R):= 1/(coeff_mat 0 (Lambda j N a b c) 0%nat 0%nat).

(* Proof on boundedness of eigen values *)
Lemma inverse_rel: forall (a b:R), (0<a /\ 0< b) -> (b<=a) -> 1/a <= 1/b.
Proof.
intros.
apply Rmult_le_reg_r with a.
+ nra.
+ assert (1 / a * a= 1). { assert (1 / a= / a). { nra. } rewrite H1. symmetry. apply Rinv_l_sym. nra. } rewrite H1.
apply Rmult_le_reg_r with b.
+ nra.
+  assert (1 / b * a * b= ( / b *b) * a). { nra. } rewrite H2.
   assert (/ b * b =1). { symmetry. apply Rinv_l_sym. nra. } rewrite H3.
   apply Rmult_le_compat_l. 
   - nra.
   - apply H0.
Qed.

(** Proof that all eigen values of Ah (1/h^2, -2/h^2, 1/h^2) are negative ***)

Lemma eig_0: forall (i N:nat), (2<N)%nat -> (0<= i < N)%nat -> (-2/(h^2)) + 2 * sqrt ((1/(h^2))* (1/(h^2))) * cos (INR (i+1) * PI * / INR (N + 1)) < 0.
Proof.
intros.
assert (sqrt (1 / h ^ 2 * (1 / h ^ 2))=1 / h ^ 2 ). { apply sqrt_square. assert (h ^ 2= h* h). { nra. } rewrite H1. apply inv_sqr_h_ge_0. } rewrite H1.
assert (-2 / h ^ 2 + 2 * (1 / h ^ 2) * cos (INR (i + 1) * PI * / INR (N + 1))= 
          (2/ (h^2)) * (- 1 +  cos (INR (i + 1) * PI * / INR (N + 1)))). { nra. } rewrite H2.
assert ( 0 = (2/ (h^2))*0). { nra. } rewrite H3.
apply Rmult_lt_compat_l. 
+ assert ( 0 < 1/ (h^2) ->0 < 2 / h ^ 2). { nra. } apply H4. assert (1 / h ^ 2= / (h^2)). { nra. } rewrite H5.
  apply Rinv_0_lt_compat. assert ( 0< h -> 0 < h ^ 2). { nra. } apply H6. apply h_gt_0.
+ assert (0 = -1 +1). { nra. } rewrite H4.
  apply Rplus_lt_compat_l.
  assert ( cos 0 = 1). { apply cos_0. } rewrite <- H5.
  apply cos_decreasing_1.
  - nra.
  - apply Rlt_le. apply PI_RGT_0.
  - assert (INR (i + 1) * PI * / INR (N + 1)= (INR (i+1)) * (PI * / INR (N + 1))). { nra. } rewrite H6.
    apply Rlt_le. apply Rmult_lt_0_compat. apply lt_0_INR. omega. apply Rmult_lt_0_compat. apply PI_RGT_0. apply Rinv_0_lt_compat. apply lt_0_INR. omega.
  - apply Rmult_le_reg_r with (INR (N+1)). apply lt_0_INR. omega.
    assert (INR (i + 1) * PI * / INR (N + 1) * INR (N + 1)= PI * INR (i+1) * ( / INR (N+1) * INR (N+1))). { nra. } rewrite H6.
    assert (( / INR (N+1) * INR (N+1))=1). { symmetry. apply Rinv_l_sym. assert ( 0< INR (N+1) -> INR (N+1) <> 0). { nra. } apply H7. apply lt_0_INR. omega. }
    rewrite H7.
    assert (PI * INR (i + 1) * 1= PI * INR (i+1)). { nra. } rewrite H8.
    apply Rmult_le_compat_l. apply Rlt_le. apply PI_RGT_0. apply le_INR. omega.
  - assert (INR (i + 1) * PI * / INR (N + 1)= (INR (i+1)) * (PI * / INR (N + 1))). { nra. } rewrite H6.
    apply Rmult_lt_0_compat. apply lt_0_INR. omega. apply Rmult_lt_0_compat. apply PI_RGT_0. apply Rinv_0_lt_compat. apply lt_0_INR. omega.
Qed.

(** Proof that all eigen values of Ah(1/h^2, -2/h^2, 1/h^2) are non-zero ***)
Lemma eig_1: forall (i N:nat) , (2< N)%nat /\ (0<=i<N)%nat-> coeff_mat 0 (Lambda i N (1/(h^2)) (-2/(h^2)) (1/(h^2))) 0 0 <> 0.
Proof.
intros.
unfold Lambda.
assert (coeff_mat 0
          (mk_matrix 1 1
             (fun _ _ : nat =>
              (-2/(h^2))  +
              2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR (i+1) * PI * / INR (N + 1))))
          0 0= (fun _ _ : nat =>
              (-2/(h^2)) +
              2 *  sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR (i+1) * PI * / INR (N + 1))) 0%nat 0%nat).
{ apply (coeff_mat_bij 0 (fun _ _ : nat =>
              (-2/(h^2)) +
              2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR (i+1) * PI * / INR (N + 1))) 0%nat 0%nat). omega. omega. } rewrite H0.
assert (-2 / h ^ 2  + 2 *sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR (i+1) * PI * / INR (N + 1)) < 0  -> 
              -2 / h ^ 2  + 2 * sqrt (1 / h ^ 2 * (1 / h ^ 2))* cos (INR (i+1) * PI * / INR (N + 1)) <>0).
{ nra. } apply H1. apply eig_0. destruct H. apply H. destruct H. apply H2.
Qed.

(** proof that the minimum eigen value of Ah(1/h^2, -2/h^2, 1/h^2) is non-zero. ***)
Lemma eig_2: forall (N:nat), (2<N)%nat -> Lambda_min  N <> 0.
Proof.
intros.
unfold Lambda_min. 
assert (sqrt (1 / h ^ 2 * (1 / h ^ 2))=1 / h ^ 2 ). { apply sqrt_square. assert (h ^ 2= h* h). { nra. } rewrite H0. apply inv_sqr_h_ge_0. } rewrite <-H0.
assert (-2 / h ^ 2 + 2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR 1 * PI * / INR (N + 1)) <0 ->
           -2 / h ^ 2 + 2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR 1 * PI * / INR (N + 1)) <> 0). { nra. } apply H1. 
 assert (1%nat = (0+1)%nat).  { omega. } rewrite H2. apply eig_0. omega. omega.
Qed.


(** Proof that 1/|lambda_min| is the maximum absolute eigen value of the inverse A^{-1} (1/h^2, -2/h^2, 1/h^2) **)
Lemma eigen_relation: forall (i N:nat), (2<N)%nat -> (0<=i<N)%nat -> Rabs (lam i N (1/(h^2)) (-2/(h^2)) (1/(h^2)) ) <= 1/ Rabs( Lambda_min  N).
Proof.
intros.
unfold lam.
assert ((1 / coeff_mat 0 (Lambda i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2)) 0 0)= (/ (coeff_mat 0 (Lambda i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2)) 0 0))). 
{ nra. } rewrite H1.
assert (Rabs (/ coeff_mat 0 (Lambda i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2)) 0 0)= / Rabs ( coeff_mat 0 (Lambda i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2)) 0 0)).
{  apply Rabs_Rinv. apply eig_1. omega. }
rewrite H2.
assert (/ Rabs (coeff_mat 0 (Lambda i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2)) 0 0)= 1/ Rabs (coeff_mat 0 (Lambda i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2)) 0 0)). { nra. } rewrite H3.
apply inverse_rel.
+ split.
  - apply Rabs_pos_lt. apply eig_1. omega.
  - apply Rabs_pos_lt. apply eig_2. omega.
+ unfold Lambda_min. unfold Lambda.
  assert (coeff_mat 0
             (mk_matrix 1 1
                (fun _ _ : nat =>
                 -2 / h ^ 2  +
                 2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) *
                 cos (INR (i+1) * PI * / INR (N + 1)))) 0 0=  (fun _ _ : nat =>
                 -2 / h ^ 2 +
                 2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) *
                 cos (INR (i+1) * PI * / INR (N + 1))) 0%nat 0%nat).
  { apply (coeff_mat_bij 0 (fun _ _ : nat =>
                 -2 / h ^ 2  +
                 2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) *
                 cos (INR (i+1) * PI * / INR (N + 1))) 0%nat 0%nat). omega. omega. } rewrite H4.
  assert (i=0%nat \/ (0< i < N)%nat). { omega. }
  destruct H5.
  + rewrite H5. assert ( 1%nat = (0+1)%nat). { omega. } rewrite <-H6.
    assert (sqrt (1 / h ^ 2 * (1 / h ^ 2)) =(1 / h ^ 2)). { apply sqrt_square. assert (h^2 = h*h). { nra. } rewrite H7. apply inv_sqr_h_ge_0. } rewrite H7. nra.
  + assert (sqrt (1 / h ^ 2 * (1 / h ^ 2)) =(1 / h ^ 2)). { apply sqrt_square. assert (h^2 = h*h). { nra. } rewrite H6. apply inv_sqr_h_ge_0. } 
    assert (Rabs (-2 / h ^ 2 + 2 * (1 / h ^ 2) * cos (INR 1 * PI * / INR (N + 1)))=Rabs  (-2 / h ^ 2+  2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR 1 * PI * / INR (N + 1)))).
    { rewrite H6. nra. } rewrite H7.
    assert (Rabs  (-2 / h ^ 2+  2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR 1 * PI * / INR (N + 1)))= 
              -(-2 / h ^ 2  +  2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR 1 * PI * / INR (N + 1)))). { apply Rabs_left. assert (1%nat = (0+1)%nat). { omega. } rewrite H8. apply eig_0. omega. omega. }
    assert ( Rabs (-2 / h ^ 2  +  2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR (i+1) * PI * / INR (N + 1)))=
              - (-2 / h ^ 2  +  2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR (i+1) * PI * / INR (N + 1)))). { apply Rabs_left. apply eig_0. omega. omega. }
    rewrite H8. rewrite H9.
    apply Ropp_ge_le_contravar.
    apply (Rplus_ge_compat_l (-2 / h ^ 2 ) (2 * sqrt (1 / h ^ 2 * (1 / h ^ 2))* cos (INR 1 * PI * / INR (N + 1))) 
                (2 *  sqrt (1 / h ^ 2 * (1 / h ^ 2)) * cos (INR (i+1) * PI * / INR (N + 1)))). 
    apply Rmult_ge_compat_l.
    - assert ( 0 = 2 * 0). { nra. } rewrite H10. apply Rmult_ge_compat_l. nra. 
      assert (0 <= sqrt (1 / h ^ 2 * (1 / h ^ 2)) -> sqrt (1 / h ^ 2 * (1 / h ^ 2)) >= 0). { nra. } apply H11. apply sqrt_pos.
    - assert (cos (INR (i+1) * PI * / INR (N + 1)) <= cos (INR 1 * PI * / INR (N + 1)) -> cos (INR 1 * PI * / INR (N + 1)) >=cos (INR (i+1) * PI * / INR (N + 1))).
      { nra. } apply H10. apply Rlt_le.
      apply cos_decreasing_1. 
      * assert (INR 1 =1). { reflexivity. } rewrite H11. assert (1 * PI * / INR (N + 1) = PI * (/ INR (N+1))). { nra. } rewrite H12.
        apply Rlt_le. apply Rmult_lt_0_compat. apply PI_RGT_0. apply Rinv_0_lt_compat. apply lt_0_INR. omega.
      * assert (INR 1= 1). { reflexivity. } rewrite H11. assert (PI = PI * (/1)). { nra. } rewrite H12. 
        assert (1 * (PI * / 1) * / INR (N + 1)= PI * (/ INR (N+1))). { nra. } rewrite H13.
        apply Rmult_le_compat_l. apply Rlt_le. apply PI_RGT_0. apply Rlt_le. apply Rinv_lt_contravar.
        assert (1 * INR (N + 1)= INR (N+1)). { nra. } rewrite H14. apply lt_0_INR. omega.
      * apply lt_1_INR. omega.
      * apply Rlt_le. assert (INR (i+1) * PI * / INR (N + 1) = (INR (i+1)) * ( PI * (/ INR (N+1)))). { nra. } rewrite H11.
        apply Rmult_lt_0_compat. apply lt_0_INR. omega. apply Rmult_lt_0_compat. apply PI_RGT_0.
        apply Rinv_0_lt_compat. apply lt_0_INR. omega.
      * assert (PI =1 * PI). { nra. } rewrite H11.
        assert (INR (i+1) * (1 * PI) * / INR (N + 1)= ((INR (i+1)) *(/ INR (N+1))) * PI). { nra. } rewrite H12.
        apply Rmult_le_compat.
        - apply Rlt_le. apply Rmult_lt_0_compat. apply lt_0_INR. omega. apply Rinv_0_lt_compat. apply lt_0_INR. omega.
        - apply Rlt_le. apply PI_RGT_0.
        - assert ( 1 = INR (N+1) */ (INR (N+1))). { apply Rinv_r_sym. assert ( 0 < INR (N+1) -> INR (N+1) <> 0). { nra. } apply H13. apply lt_0_INR. omega. } rewrite H13.
          apply Rmult_le_compat_r. apply Rlt_le. apply Rinv_0_lt_compat. apply lt_0_INR. omega.
          apply le_INR. omega.
        - nra.
      * assert (INR 1 * PI * / INR (N + 1) = (INR 1) * (PI * / INR (N + 1))). { nra. } rewrite H11.
        assert (INR (i+1) * PI * / INR (N + 1) = (INR (i+1)) * (PI * / INR (N + 1))). { nra. } rewrite H12.
        apply Rmult_lt_compat_r. 
        { apply Rmult_lt_0_compat. apply PI_RGT_0. apply Rinv_0_lt_compat. apply lt_0_INR. omega. }
        { apply lt_INR. omega. }
Qed.

Lemma sum_n_m_le : forall (n m N:nat) (a: nat -> R) (b : nat -> R), (2<N)%nat -> (0<n<=m)%nat -> (n<N)%nat /\ (m<N)%nat ->  (forall i:nat , (0<=i<N)%nat -> a i <= b i) -> 
    sum_n_m (fun l:nat => a l) n m <=sum_n_m (fun l:nat => b l) n m.
Proof.
intros.
induction m. contradict H. omega.
assert ( n= S m \/ (0<n<S m)%nat). { omega. } destruct H3.
+ rewrite H3.
  assert (sum_n_m (fun l : nat => a l) (S m) (S m)= (fun l : nat => a l) (S m)).
  { apply (sum_n_n (fun l : nat => a l) (S m)). } rewrite H4.
  assert (sum_n_m (fun l : nat => b l) (S m) (S m) = (fun l : nat => b l) (S m)).
  { apply (sum_n_n (fun l : nat => b l) (S m)). } rewrite H5.
  specialize (H2 (S m)). apply H2. omega.
+ clear H0. 
   assert ((0 < n < S m)%nat -> (0 < n <= m)%nat). { omega. }  specialize (H0 H3). specialize (IHm H0).
    assert ( sum_n_m (fun l : nat => a l) n (S m) = sum_n_m (fun l : nat => a l) n m + (fun l : nat => a l) (S m)).
    { apply (sum_n_Sm (fun l : nat => a l)). omega. } rewrite H4.
    assert (sum_n_m (fun l : nat => b l) n (S m) =sum_n_m (fun l : nat => b l) n m + (fun l : nat => b l) (S m)).
    { apply (sum_n_Sm  (fun l : nat => b l)). omega. } rewrite H5.
    apply Rplus_le_compat. apply IHm. specialize (H2 (S m)). omega. apply H2. omega.
Qed.  

Require Import linear_algebra.

Lemma max_spectral: forall (N:nat) (v: matrix N 1%nat),(2<N)%nat ->  vec_norm_2 N v =1 -> 
    sqrt (sum_n_m (fun i:nat => (coeff_mat 0 v i 0%nat)^2 * (lam i N (1/(h^2)) (-2/(h^2)) (1/(h^2)))^2) 0%nat (pred N)) <= 1/ Rabs(Lambda_min  N).
Proof.
intros.
assert (1 / Rabs (Lambda_min  N) =sqrt (Rsqr ( 1 / Rabs (Lambda_min  N)))). 
{ symmetry. apply sqrt_Rsqr. assert (1 / Rabs (Lambda_min  N)= / Rabs (Lambda_min  N)). { nra. } rewrite H1.
assert (Rabs (/(Lambda_min  N)) = / Rabs (Lambda_min  N)). { apply Rabs_Rinv. apply eig_2. omega. } rewrite <-H2. apply Rabs_pos. }
rewrite H1.  apply sqrt_le_1_alt. 
assert ((1 / Rabs (Lambda_min  N))²= Rsqr (1) / Rsqr(Rabs (Lambda_min  N))). 
{ apply Rsqr_div. apply Rabs_no_R0. apply eig_2. omega. } rewrite H2.
assert ( 1² / (Rabs (Lambda_min  N))²= Rsqr(vec_norm_2 N v)/ (Rabs (Lambda_min  N))²). 
{ rewrite <- H0. reflexivity. } rewrite H3. unfold vec_norm_2.
assert ( (sqrt (sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0  (pred N)))²= (sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0  (pred N))).
{ apply Rsqr_sqrt. 
  assert (sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0 (pred N)= sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0%nat 0%nat +
            sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 1%nat (pred N)).
  { apply (sum_n_m_Chasles (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0%nat 0%nat (pred N)). omega. omega. } rewrite H4.
  apply Rplus_le_le_0_compat. 
  + assert (sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0 0= (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0%nat). 
    { apply (sum_n_n (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0%nat). } rewrite H5. nra.
  + apply sum_elem_pos. omega.
    intros. nra.
} rewrite H4.
assert (sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0 (pred N) /(Rabs (Lambda_min  N))²= 
          sum_n_m (fun l:nat => (coeff_mat 0 v l 0)^2 * (1/ Rsqr (Rabs( Lambda_min  N)))) 0%nat (pred N)).
{ symmetry. 
  assert (sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0 (pred N) /(Rabs (Lambda_min  N))²= 
            sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0 (pred N) * (1/ Rsqr(Rabs (Lambda_min  N)))). { nra. } rewrite H5.
  apply (sum_n_m_mult_r (1 / (Rabs (Lambda_min  N))²)(fun l : nat => coeff_mat 0 v l 0 ^ 2) 0%nat (pred N)).
} rewrite H5.
assert (sum_n_m (fun i : nat => coeff_mat 0 v i 0 ^ 2 * lam i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ^ 2  )  0 (pred N)= sum_n_m (fun i : nat => coeff_mat 0 v i 0 ^ 2 * lam i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ^ 2 ) 0%nat 0%nat +
          sum_n_m (fun i : nat => coeff_mat 0 v i 0 ^ 2 * lam i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ^ 2  ) 1%nat (pred N)).
{ apply (sum_n_m_Chasles (fun i : nat => coeff_mat 0 v i 0 ^ 2 * lam i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ^ 2 ) 0%nat 0%nat (pred N)). omega. omega. } rewrite H6.
assert (sum_n_m  (fun l : nat =>   coeff_mat 0 v l 0 ^ 2 *   (1 / (Rabs (Lambda_min  N))²)) 0   (pred N)= 
          sum_n_m  (fun l : nat =>   coeff_mat 0 v l 0 ^ 2 *   (1 / (Rabs (Lambda_min  N))²)) 0%nat 0%nat + 
            sum_n_m  (fun l : nat =>   coeff_mat 0 v l 0 ^ 2 *   (1 / (Rabs (Lambda_min  N))²)) 1%nat (pred N)).
{ apply (sum_n_m_Chasles (fun l : nat =>   coeff_mat 0 v l 0 ^ 2 *   (1 / (Rabs (Lambda_min  N))²)) 0%nat 0%nat (pred N)). omega. omega. } rewrite H7.
apply Rplus_le_compat.
+ assert (sum_n_m (fun i : nat => coeff_mat 0 v i 0 ^ 2 * lam i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ^ 2)  0 0= (fun i : nat => coeff_mat 0 v i 0 ^ 2 * lam i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ^ 2) 0%nat).
  { apply (sum_n_n (fun i : nat => coeff_mat 0 v i 0 ^ 2 *lam i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ^ 2) 0%nat). } rewrite H8.
  assert (sum_n_m  (fun l : nat =>   coeff_mat 0 v l 0 ^ 2 *   (1 / (Rabs (Lambda_min  N))²)) 0 0= 
            (fun l : nat =>   coeff_mat 0 v l 0 ^ 2 *   (1 / (Rabs (Lambda_min  N))²)) 0%nat).
  { apply (sum_n_n  (fun l : nat =>   coeff_mat 0 v l 0 ^ 2 *   (1 / (Rabs (Lambda_min  N))²)) 0%nat). } rewrite H9.
  apply Rmult_le_compat_l. nra. 
  assert (lam 0 N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ^ 2 = Rsqr (Rabs (lam 0 N (1/(h^2)) (-2/(h^2)) (1/(h^2)) ))).
  { assert (lam 0 N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ^ 2= Rsqr (lam 0 N (1/(h^2)) (-2/(h^2)) (1/(h^2)) )). { simpl. unfold Rsqr. nra. } rewrite H10. apply Rsqr_abs. }
  rewrite H10. assert ( Rsqr 1 = 1). { apply Rsqr_1. } rewrite <- H11.
  assert (Rsqr (1 / Rabs( Lambda_min  N)) = 1² / (Rabs (Lambda_min  N))²). { apply Rsqr_div. apply Rabs_no_R0. apply eig_2. omega. } rewrite <-H12.
  apply Rsqr_incr_1.  unfold lam. 
  assert ( (1 / coeff_mat 0 (Lambda 0 N (1² / h ^ 2) (-2 / h ^ 2) (1² / h ^ 2)) 0 0)= / (coeff_mat 0 (Lambda 0 N (1² / h ^ 2) (-2 / h ^ 2) (1² / h ^ 2)) 0 0)). { nra. } rewrite H13.
  assert (Rabs (/ coeff_mat 0 (Lambda 0 N (1² / h ^ 2) (-2 / h ^ 2) (1² / h ^ 2) ) 0 0) = / Rabs (coeff_mat 0 (Lambda 0 N (1² / h ^ 2) (-2 / h ^ 2) (1² / h ^ 2) ) 0 0)). { apply Rabs_Rinv.  rewrite H11. apply eig_1. omega. } rewrite H14.
  assert (1 / Rabs (Lambda_min  N) = / Rabs (Lambda_min  N)). { nra. } rewrite H15. rewrite H11.
  apply Rmult_le_reg_r with (Rabs (coeff_mat 0 (Lambda 0 N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ) 0 0) *  Rabs (Lambda_min  N)).
  assert (Rabs ( (coeff_mat 0 (Lambda 0 N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ) 0 0) * (Lambda_min  N)) = Rabs (coeff_mat 0 (Lambda 0 N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ) 0 0) * Rabs (Lambda_min  N)). { apply Rabs_mult. } rewrite <- H16. apply Rabs_pos_lt.
  apply Rmult_integral_contrapositive_currified. apply eig_1. omega. apply eig_2. omega.
  assert (/ Rabs (coeff_mat 0 (Lambda 0 N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2)) 0 0) *(Rabs (coeff_mat 0 (Lambda 0 N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ) 0 0) * Rabs (Lambda_min  N))=
          (/ Rabs (coeff_mat 0 (Lambda 0 N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2)) 0 0) * (Rabs (coeff_mat 0 (Lambda 0 N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ) 0 0))) * Rabs (Lambda_min  N)). { nra. } rewrite H16.
  assert ( (/ Rabs (coeff_mat 0 (Lambda 0 N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ) 0 0) * (Rabs (coeff_mat 0 (Lambda 0 N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ) 0 0)))=1).
  { symmetry. apply Rinv_l_sym. apply Rabs_no_R0. apply eig_1. omega. } rewrite H17.
  assert (/ Rabs (Lambda_min  N) *(Rabs (coeff_mat 0 (Lambda 0 N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2)) 0 0) * Rabs (Lambda_min  N))=
          (/ Rabs (Lambda_min  N) *  Rabs (Lambda_min  N)) * Rabs (coeff_mat 0 (Lambda 0 N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ) 0 0)). { nra. } rewrite H18.
  assert ( (/ Rabs (Lambda_min  N) *  Rabs (Lambda_min  N))=1).
  { symmetry. apply Rinv_l_sym. apply Rabs_no_R0. apply eig_2. omega. } rewrite H19.
  apply Rmult_le_compat_l. nra. unfold Lambda_min. unfold Lambda.
  assert (coeff_mat 0
     (mk_matrix 1 1
        (fun _ _ : nat =>
        -2 / h ^ 2  +
         2 * sqrt (1 / h ^ 2 * (1 / h ^ 2))*
         cos (INR (0 + 1) * PI * / INR (N + 1)))) 0 0= (fun _ _ : nat =>
         -2 / h ^ 2  +
         2 * sqrt (1 / h ^ 2 * (1 / h ^ 2))*
         cos (INR (0 + 1) * PI * / INR (N + 1))) 0%nat 0%nat).
  { apply (coeff_mat_bij 0  (fun _ _ : nat =>
                  -2 / h ^ 2  +
                  2 * sqrt (1 / h ^ 2 * (1 / h ^ 2)) *
                  cos (INR (0 + 1) * PI * / INR (N + 1))) 0%nat 0%nat). omega. omega. } 
  rewrite H20.
  assert ((0 + 1)%nat = 1%nat). { omega. } rewrite H21.
  assert (sqrt (1 / h ^ 2 * (1 / h ^ 2))= (1/(h^2))). { apply sqrt_square. assert (h^2= h*h). nra. rewrite H22. apply inv_sqr_h_ge_0. } rewrite H22. 
  apply Rle_refl.
  apply Rabs_pos. apply Rlt_le. 
  assert (1 / Rabs (Lambda_min  N)= /Rabs (Lambda_min  N)). { nra. } rewrite H13. apply Rinv_0_lt_compat. apply Rabs_pos_lt. apply eig_2. omega.
+ apply (sum_n_m_le 1%nat (pred N) N (fun i : nat => coeff_mat 0 v i 0 ^ 2 * lam i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ^ 2) (fun l : nat =>
                          coeff_mat 0 v l 0 ^ 2 *   (1 / (Rabs (Lambda_min  N))²))). omega. omega. omega.
  intros. apply Rmult_le_compat_l. nra. 
  assert (lam i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ^ 2 = Rsqr (Rabs (lam i N (1/(h^2)) (-2/(h^2)) (1/(h^2))))).
  { assert (lam i N (1 / h ^ 2) (-2 / h ^ 2) (1 / h ^ 2) ^ 2= Rsqr (lam i N (1/(h^2)) (-2/(h^2)) (1/(h^2)) )). { simpl. unfold Rsqr. nra. } rewrite H9. apply Rsqr_abs. }
  rewrite H9. assert ( Rsqr 1 = 1). { apply Rsqr_1. } rewrite <- H10.
  assert (Rsqr (1 / Rabs( Lambda_min  N)) = 1² / (Rabs (Lambda_min  N))²). { apply Rsqr_div. apply Rabs_no_R0. apply eig_2. omega. } rewrite <-H11.
  apply Rsqr_incr_1. rewrite H10. apply eigen_relation. omega. omega. apply Rabs_pos. apply Rlt_le.
  assert ( 1 / Rabs (Lambda_min  N)= /  Rabs (Lambda_min  N)). { nra. } rewrite H12. apply Rinv_0_lt_compat. apply Rabs_pos_lt. apply eig_2. omega.
Qed.

(* Define matrix norm *)
Definition matrix_norm (N:nat):= 1/ Rabs(Lambda_min N ).

(* Applying the stability definition from the formalization of the Lax equivalence theorem to the numerical scheme *)

Require Import lax_equivalence.

Variable m:nat.
Hypothesis size: forall m:nat , (2<m)%nat. (* condition on the size of the matrix *)


Notation Xh:= lax_equivalence.Xh.
Notation X:= lax_equivalence.X.
Notation Y:= lax_equivalence.Y.
Notation Yh:= lax_equivalence.Yh.
Notation E:= lax_equivalence.E.
Notation F:= lax_equivalence.F.
Notation Aop:= lax_equivalence.Aop.
Notation Ah_op:= lax_equivalence.Ah_op.

Hypothesis mat_op_norm: 
  forall (u:X) (f:Y) (h:R) (uh: Xh h) (rh: forall (h:R), X -> (Xh h)) (sh: forall (h:R), Y->(Yh h))
 (E: Y->X) (Eh:forall (h:R), (Yh h)->(Xh h)), operator_norm (Eh h) = matrix_norm m .


Theorem stability: 
  forall (u:X) (f:Y) (h:R) (uh: Xh h) (rh: forall (h:R), X -> (Xh h)) (sh: forall (h:R), Y->(Yh h))
  (E: Y->X) (Eh:forall (h:R), (Yh h)->(Xh h)), exists K:R , forall (h:R), operator_norm(Eh h)<=K.
Proof.
intros.
exists (L^2 / 4).
intros.
assert  (operator_norm (Eh h1)= matrix_norm m ).
{ apply mat_op_norm. auto. auto. auto. auto. auto. auto. } rewrite H.
unfold matrix_norm. apply spectral.  apply size.
Qed.