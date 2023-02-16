(* Proof that inv(A) * v = (1/lambda)* v *)
Require Import Reals Psatz.
Require Import Coquelicot.Hierarchy.
Require Import Omega Init.Nat Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import R_sqrt Rpower.
Require Import Ah_properties.
Require Import Ah_inverse.
Require Import Eigen_system.



Lemma iden_mat_prop_1 (m N:nat) (a b:R) : (2 < N)%nat -> (0 <= m < N)%nat -> 0<a -> sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (identity N) 0 l)
     (coeff_mat Hierarchy.zero
        (mk_matrix N 1
           (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
            Rpower (a * / a)
              (INR i0 + 1 - 1 * / 2) *
            sin
              ((INR i0 + 1) * INR (m+1) * PI *
               / INR (N + 1)))) l 0)) 1 
  (pred N) = 0.
Proof.
intros.
assert (sum_n_m (fun l:nat => 0) 1 (pred N) = 0). { apply sum_const_zero. omega. }
rewrite <-H2.
apply sum_n_m_ext_loc.
intros.
assert ((coeff_mat Hierarchy.zero (identity N) 0 k)=0).
{ unfold identity.
  assert (coeff_mat Hierarchy.zero
            (mk_matrix N N
               (fun i j : nat => if i =? j then 1 else 0)) 0 k= (fun i j : nat => if i =? j then 1 else 0) 0%nat k).
  { apply (coeff_mat_bij Hierarchy.zero (fun i j : nat => if i =? j then 1 else 0) 0%nat k). omega. omega. }
  rewrite H4. 
  assert (0 =? k=false).
  { assert ((0 =? k) = false <-> 0%nat<>k). { apply (beq_nat_false_iff 0%nat k). } destruct H5. apply H6.
    assert ( (0<k)%nat -> 0%nat <> k). { omega. } apply H7. omega.
  } rewrite H5. nra.
} rewrite H4.
apply (mult_zero_l (coeff_mat Hierarchy.zero
     (mk_matrix N 1
        (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a * / a)
           (INR i0 + 1 - 1 * / 2) *
         sin
           ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))))
     k 0)).
Qed.


Lemma iden_mat_prop_2 (m N:nat) (a b:R): (2< N)%nat -> (0<=m<N)%nat -> 0<a -> sum_n_m
  (fun l : nat =>
   mult
     (coeff_mat Hierarchy.zero (identity N)
        (pred N) l)
     (coeff_mat Hierarchy.zero
        (mk_matrix N 1
           (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
            Rpower (a * / a)
              (INR i0 + 1 - 1 * / 2) *
            sin
              ((INR i0 + 1) * INR (m+1) * PI *
               / INR (N + 1)))) l 0)) 0
  (pred (pred N)) = 0.
Proof.
intros.
assert ( sum_n_m (fun l:nat => 0) 0%nat (pred (pred N))=0).
{ apply sum_const_zero. omega. } rewrite <-H2.
apply sum_n_m_ext_loc. 
intros.
assert ((coeff_mat Hierarchy.zero (identity N) (pred N) k)=0).
{ unfold identity.
  assert (coeff_mat Hierarchy.zero
            (mk_matrix N N
               (fun i j : nat => if i =? j then 1 else 0))
            (pred N) k= (fun i j : nat => if i =? j then 1 else 0) (pred N) k).
  { apply (coeff_mat_bij Hierarchy.zero (fun i j : nat => if i =? j then 1 else 0) (pred N) k). omega. omega. } rewrite H4.
assert (pred N =? k=false). 
{ assert ((pred N =? k) = false <-> (pred N) <> k). { apply (beq_nat_false_iff (pred N) k). } destruct H5. apply H6.
  assert ( (k< (pred N))%nat -> pred N <> k). { omega. } apply H7. omega.
} rewrite H5. nra.
} rewrite H4.
apply (mult_zero_l 
        (coeff_mat Hierarchy.zero
           (mk_matrix N 1
              (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
               Rpower (a * / a)
                 (INR i0 + 1 - 1 * / 2) *
               sin
                 ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))))
           k 0)).
Qed.

Lemma iden_mat_prop_3 (i m N:nat) (a b:R): (2<N)%nat -> (0<=m<N)%nat -> (0<i<pred N)%nat -> 0<a -> sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (identity N) i l)
     (coeff_mat Hierarchy.zero
        (mk_matrix N 1
           (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
            Rpower (a * / a)
              (INR i0 + 1 - 1 * / 2) *
            sin
              ((INR i0 + 1) * INR (m+1) * PI *
               / INR (N + 1)))) l 0)) 0 
  (pred i) = 0.
Proof.
intros.
assert (sum_n_m (fun l:nat => 0) 0%nat (pred i) =0).
{ apply sum_const_zero. omega. } rewrite <-H3.
apply sum_n_m_ext_loc.
intros.
assert ( (coeff_mat Hierarchy.zero (identity N) i k)=0).
{ unfold identity.
  assert (coeff_mat Hierarchy.zero
            (mk_matrix N N
               (fun i0 j : nat => if i0 =? j then 1 else 0)) i k=  (fun i0 j : nat => if i0 =? j then 1 else 0) i k).
  { apply (coeff_mat_bij Hierarchy.zero (fun i0 j : nat => if i0 =? j then 1 else 0) i k). omega. omega. } rewrite H5.
  assert (i =? k=false).
  { assert ((i =? k) = false <-> i <> k). { apply (beq_nat_false_iff i k). } destruct H6. apply H7.
    assert ( (k<i)%nat -> i <> k). { omega. } apply H8. omega.
  } rewrite H6. nra.
} rewrite H5.
apply (mult_zero_l (coeff_mat Hierarchy.zero
     (mk_matrix N 1
        (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a * / a)
           (INR i0 + 1 - 1 * / 2) *
         sin
           ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))))
     k 0)).
Qed.

Lemma iden_mat_prop_4 (i m N:nat) (a b:R): (2< N)%nat -> (0<=m<N)%nat -> (0<i<(pred N))%nat -> 0<a -> 
sum_n_m
  (fun l : nat =>
   mult (coeff_mat Hierarchy.zero (identity N) i l)
     (coeff_mat Hierarchy.zero
        (mk_matrix N 1
           (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
            Rpower (a * / a)
              (INR i0 + 1 - 1 * / 2) *
            sin
              ((INR i0 + 1) * INR (m+1) * PI *
               / INR (N + 1)))) l 0)) 
  (S i) (pred N) = 0.
Proof.
intros.
assert (sum_n_m (fun l:nat => 0) (S i) (pred N)=0).
{ apply sum_const_zero. omega. } rewrite <-H3.
apply sum_n_m_ext_loc.
intros.
assert ((coeff_mat Hierarchy.zero (identity N) i k)=0).
{ unfold identity.
  assert (coeff_mat Hierarchy.zero
  (mk_matrix N N
     (fun i0 j : nat => if i0 =? j then 1 else 0)) i k= (fun i0 j : nat => if i0 =? j then 1 else 0) i k).
  { apply (coeff_mat_bij Hierarchy.zero (fun i0 j : nat => if i0 =? j then 1 else 0) i k). omega. omega. }
  rewrite H5. 
  assert (i =? k =false). 
  { assert ((i =? k) = false <-> i <> k). { apply (beq_nat_false_iff i k). } destruct H6. apply H7.
    assert ( (i<k)%nat -> i <> k). { omega. } apply H8. omega.
  } rewrite H6. nra.
} rewrite H5.
apply (mult_zero_l (coeff_mat Hierarchy.zero
     (mk_matrix N 1
        (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a * / a)
           (INR i0 + 1 - 1 * / 2) *
         sin
           ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))))
     k 0)).
Qed.

Lemma iden_mat (m N:nat) (a b:R): (2<N)%nat -> (0 <= m < N)%nat -> 0< a -> Eigen_vec m N a b a = Mmult (identity N) (Eigen_vec m N a b a).
Proof.
intros.
unfold Mmult. unfold Eigen_vec.
apply (mk_matrix_ext N 1%nat (fun i _ : nat =>sqrt (2 / INR (N + 1)) *
             Rpower (a * / a) (INR i + 1 - 1 * / 2) *
             sin ((INR i + 1) * INR (m+1) * PI * / INR (N + 1)))   (fun i j : nat =>
           sum_n
             (fun l : nat =>
              mult (coeff_mat Hierarchy.zero (identity N) i l)
                (coeff_mat Hierarchy.zero
                   (mk_matrix N 1
                      (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                       Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                       sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))))
                   l j)) (pred N))). 
intros. unfold sum_n.
assert (j=0%nat). { omega. } rewrite H4.
assert ( i=0%nat \/ (0<i<pred N)%nat \/ (i=pred N)). { omega. } destruct H5.
+ rewrite H5.
  assert (sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (identity N) 0 l)
               (coeff_mat Hierarchy.zero
                  (mk_matrix N 1
                     (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                      Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                      sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0))
            0 (pred N)= sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (identity N) 0 l)
               (coeff_mat Hierarchy.zero
                  (mk_matrix N 1
                     (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                      Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                      sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0)) 0%nat 0%nat + sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (identity N) 0 l)
               (coeff_mat Hierarchy.zero
                  (mk_matrix N 1
                     (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                      Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                      sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0)) 1%nat (pred N)).
  { apply (sum_n_m_Chasles 
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (identity N) 0 l)
               (coeff_mat Hierarchy.zero
                  (mk_matrix N 1
                     (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                      Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                      sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0)) 0%nat 0%nat (pred N)). omega. omega. } rewrite H6.
  assert (sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (identity N) 0 l)
               (coeff_mat Hierarchy.zero
                  (mk_matrix N 1
                     (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                      Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                      sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0))
            1 (pred N)= 0). { apply iden_mat_prop_1. auto.  omega. omega. nra. } rewrite H7.
  assert (sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (identity N) 0 l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                        sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0))
              0 0 + 0= sum_n_m
                        (fun l : nat =>
                         mult (coeff_mat Hierarchy.zero (identity N) 0 l)
                           (coeff_mat Hierarchy.zero
                              (mk_matrix N 1
                                 (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                                  Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                                  sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0))
                        0 0). { nra. } rewrite H8.
  assert (sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (identity N) 0 l)
               (coeff_mat Hierarchy.zero
                  (mk_matrix N 1
                     (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                      Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                      sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0))
            0 0=  (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (identity N) 0 l)
               (coeff_mat Hierarchy.zero
                  (mk_matrix N 1
                     (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                      Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                      sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0)) 0%nat).
  { apply (sum_n_n (fun l : nat =>
             mult (coeff_mat Hierarchy.zero (identity N) 0 l)
               (coeff_mat Hierarchy.zero
                  (mk_matrix N 1
                     (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                      Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                      sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0)) 0%nat). } rewrite H9.
   assert ( (coeff_mat Hierarchy.zero (identity N) 0 0)=1).
   { unfold identity. 
     assert (coeff_mat Hierarchy.zero
              (mk_matrix N N (fun i0 j0 : nat => if i0 =? j0 then 1 else 0))
              0 0 = (fun i0 j0 : nat => if i0 =? j0 then 1 else 0) 0%nat 0%nat).
     { apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat => if i0 =? j0 then 1 else 0) 0%nat 0%nat). omega. omega. }
     rewrite H10. assert (0=?0=true). { auto. } rewrite H11. reflexivity.
   } rewrite H10.
   assert (coeff_mat Hierarchy.zero
     (mk_matrix N 1
        (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
         sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) 0 0=  (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
         sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))) 0%nat 0%nat). 
  { apply (coeff_mat_bij Hierarchy.zero (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
         Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
         sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))) 0%nat 0%nat). omega. omega. } rewrite H11.
  symmetry. apply (mult_one_l (sqrt (2 / INR (N + 1)) *Rpower (a * / a) (INR 0 + 1 - 1 * / 2) *
                      sin ((INR 0 + 1) * INR (m+1) * PI * / INR (N + 1)))). 
+ destruct H5.
  - assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (identity N) i l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a)
                          (INR i0 + 1 - 1 * / 2) *
                        sin
                          ((INR i0 + 1) * INR (m+1) * PI *
                           / INR (N + 1)))) l 0)) 0 (pred N)= sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (identity N) i l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a)
                          (INR i0 + 1 - 1 * / 2) *
                        sin
                          ((INR i0 + 1) * INR (m+1) * PI *
                           / INR (N + 1)))) l 0)) 0%nat (pred i) + sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (identity N) i l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a)
                          (INR i0 + 1 - 1 * / 2) *
                        sin
                          ((INR i0 + 1) * INR (m+1) * PI *
                           / INR (N + 1)))) l 0)) (S (pred i)) (pred N)).
    { apply (sum_n_m_Chasles (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (identity N) i l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a)
                          (INR i0 + 1 - 1 * / 2) *
                        sin
                          ((INR i0 + 1) * INR (m+1) * PI *
                           / INR (N + 1)))) l 0)) 0%nat (pred i) (pred N)). omega. omega. } rewrite H6.
    assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (identity N) i l)
                   (coeff_mat Hierarchy.zero
                      (mk_matrix N 1
                         (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                          Rpower (a * / a)
                            (INR i0 + 1 - 1 * / 2) *
                          sin
                            ((INR i0 + 1) * INR (m+1) * PI *
                             / INR (N + 1)))) l 0)) 0 (pred i)= 0). { apply iden_mat_prop_3. auto.  omega. omega. omega. nra. } rewrite H7.
    assert (S (pred i)=i). { omega. } rewrite H8.
    assert (sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (identity N) i l)
                   (coeff_mat Hierarchy.zero
                      (mk_matrix N 1
                         (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                          Rpower (a * / a)
                            (INR i0 + 1 - 1 * / 2) *
                          sin
                            ((INR i0 + 1) * INR (m+1) * PI *
                             / INR (N + 1)))) l 0)) i (pred N) = sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (identity N) i l)
                   (coeff_mat Hierarchy.zero
                      (mk_matrix N 1
                         (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                          Rpower (a * / a)
                            (INR i0 + 1 - 1 * / 2) *
                          sin
                            ((INR i0 + 1) * INR (m+1) * PI *
                             / INR (N + 1)))) l 0)) i i + sum_n_m
                (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (identity N) i l)
                   (coeff_mat Hierarchy.zero
                      (mk_matrix N 1
                         (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                          Rpower (a * / a)
                            (INR i0 + 1 - 1 * / 2) *
                          sin
                            ((INR i0 + 1) * INR (m+1) * PI *
                             / INR (N + 1)))) l 0)) (S i) (pred N)).
    { apply (sum_n_m_Chasles  (fun l : nat =>
                 mult
                   (coeff_mat Hierarchy.zero (identity N) i l)
                   (coeff_mat Hierarchy.zero
                      (mk_matrix N 1
                         (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                          Rpower (a * / a)
                            (INR i0 + 1 - 1 * / 2) *
                          sin
                            ((INR i0 + 1) * INR (m+1) * PI *
                             / INR (N + 1)))) l 0)) i i (pred N)). omega. omega. } rewrite H9.
    assert (sum_n_m
                 (fun l : nat =>
                  mult
                    (coeff_mat Hierarchy.zero (identity N) i l)
                    (coeff_mat Hierarchy.zero
                       (mk_matrix N 1
                          (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                           Rpower (a * / a)
                             (INR i0 + 1 - 1 * / 2) *
                           sin
                             ((INR i0 + 1) * INR (m+1) * PI *
                              / INR (N + 1)))) l 0)) 
                 (S i) (pred N)=0). { apply iden_mat_prop_4. auto.  omega. omega. omega. nra. } rewrite H10.
    assert (0 +
                (sum_n_m
                   (fun l : nat =>
                    mult
                      (coeff_mat Hierarchy.zero (identity N) i l)
                      (coeff_mat Hierarchy.zero
                         (mk_matrix N 1
                            (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                             Rpower (a * / a)
                               (INR i0 + 1 - 1 * / 2) *
                             sin
                               ((INR i0 + 1) * INR (m+1) * PI *
                                / INR (N + 1)))) l 0)) i i + 0)= sum_n_m
                   (fun l : nat =>
                    mult
                      (coeff_mat Hierarchy.zero (identity N) i l)
                      (coeff_mat Hierarchy.zero
                         (mk_matrix N 1
                            (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                             Rpower (a * / a)
                               (INR i0 + 1 - 1 * / 2) *
                             sin
                               ((INR i0 + 1) * INR (m+1) * PI *
                                / INR (N + 1)))) l 0)) i i ). { nra. } rewrite H11.
    assert (sum_n_m
              (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (identity N) i l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a)
                          (INR i0 + 1 - 1 * / 2) *
                        sin
                          ((INR i0 + 1) * INR (m+1) * PI *
                           / INR (N + 1)))) l 0)) i i= (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (identity N) i l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a)
                          (INR i0 + 1 - 1 * / 2) *
                        sin
                          ((INR i0 + 1) * INR (m+1) * PI *
                           / INR (N + 1)))) l 0)) i).
    { apply (sum_n_n (fun l : nat =>
               mult
                 (coeff_mat Hierarchy.zero (identity N) i l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a)
                          (INR i0 + 1 - 1 * / 2) *
                        sin
                          ((INR i0 + 1) * INR (m+1) * PI *
                           / INR (N + 1)))) l 0)) i). } rewrite H12.
    assert ((coeff_mat Hierarchy.zero (identity N) i i)=1).
    { unfold identity.
      assert (coeff_mat Hierarchy.zero
                (mk_matrix N N
                   (fun i0 j0 : nat => if i0 =? j0 then 1 else 0))
                i i = (fun i0 j0 : nat => if i0 =? j0 then 1 else 0) i i).
      { apply (coeff_mat_bij  Hierarchy.zero (fun i0 j0 : nat => if i0 =? j0 then 1 else 0) i i). omega. omega. } rewrite H13.
      assert ( i =? i= true). { symmetry. apply (beq_nat_refl i). } rewrite H14. nra.
    } rewrite H13.
    assert (mult 1
                (coeff_mat Hierarchy.zero
                   (mk_matrix N 1
                      (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                       Rpower (a * / a)
                         (INR i0 + 1 - 1 * / 2) *
                       sin
                         ((INR i0 + 1) * INR (m+1) * PI *
                          / INR (N + 1)))) i 0)= (coeff_mat Hierarchy.zero
                   (mk_matrix N 1
                      (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                       Rpower (a * / a)
                         (INR i0 + 1 - 1 * / 2) *
                       sin
                         ((INR i0 + 1) * INR (m+1) * PI *
                          / INR (N + 1)))) i 0)).
    { apply (mult_one_l (coeff_mat Hierarchy.zero
                   (mk_matrix N 1
                      (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                       Rpower (a * / a)
                         (INR i0 + 1 - 1 * / 2) *
                       sin
                         ((INR i0 + 1) * INR (m+1) * PI *
                          / INR (N + 1)))) i 0)). } rewrite H14.
    assert (coeff_mat Hierarchy.zero
                (mk_matrix N 1
                   (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                    Rpower (a * / a)
                      (INR i0 + 1 - 1 * / 2) *
                    sin
                      ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))))
                i 0= (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                    Rpower (a * / a)
                      (INR i0 + 1 - 1 * / 2) *
                    sin
                      ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))) i 0%nat).
     { apply (coeff_mat_bij Hierarchy.zero (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                    Rpower (a * / a)
                      (INR i0 + 1 - 1 * / 2) *
                    sin
                      ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))) i 0%nat). omega. omega. } rewrite H15.
      reflexivity.
  - rewrite H5.
    assert (sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (identity N) (pred N) l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                        sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0))
              0 (pred N)= sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (identity N) (pred N) l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                        sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0)) 0%nat (pred (pred N)) +
              sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (identity N) (pred N) l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                        sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0)) (S (pred (pred N))) (pred N)).
    { apply (sum_n_m_Chasles (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (identity N) (pred N) l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                        sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0)) 0%nat (pred (pred N)) (pred N)). omega. omega. }
    rewrite H6. 
    assert (sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero (identity N) (pred N) l)
                   (coeff_mat Hierarchy.zero
                      (mk_matrix N 1
                         (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                          Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                          sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0))
                0 (pred (pred N))=0). { apply iden_mat_prop_2. auto.  omega. omega. nra. } rewrite H7.
    assert (0 +
            sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (identity N) (pred N) l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                        sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0))
              (S (pred (pred N))) (pred N)= 
                sum_n_m
                  (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero (identity N) (pred N) l)
                     (coeff_mat Hierarchy.zero
                        (mk_matrix N 1
                           (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                            Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                            sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0))
                  (S (pred (pred N))) (pred N)). { nra. } rewrite H8.
    assert (S (pred (pred N))= pred N). { omega. } rewrite H9.
    assert ( sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (identity N) (pred N) l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                        sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0))
              (pred N) (pred N)= (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (identity N) (pred N) l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                        sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0)) (pred N)).
    { apply (sum_n_n (fun l : nat =>
               mult (coeff_mat Hierarchy.zero (identity N) (pred N) l)
                 (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                        Rpower (a * / a) (INR i0 + 1 - 1 * / 2) *
                        sin ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1)))) l 0)) (pred N)). } rewrite H10.
    assert ((coeff_mat Hierarchy.zero (identity N) (pred N) (pred N))=1).
    { unfold identity.
      assert (coeff_mat Hierarchy.zero
                (mk_matrix N N (fun i0 j0 : nat => if i0 =? j0 then 1 else 0))
                (pred N) (pred N)= (fun i0 j0 : nat => if i0 =? j0 then 1 else 0) (pred N) (pred N)).
      { apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat => if i0 =? j0 then 1 else 0) (pred N) (pred N)). omega. omega. }
      rewrite H11.
      assert (pred N =? pred N= true). { symmetry. apply (beq_nat_refl (pred N)). } rewrite H12. nra.
    }
    rewrite H11. 
    assert (mult 1
                  (coeff_mat Hierarchy.zero
                     (mk_matrix N 1
                        (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                         Rpower (a * / a)
                           (INR i0 + 1 - 1 * / 2) *
                         sin
                           ((INR i0 + 1) * INR (m+1) * PI *
                            / INR (N + 1)))) (pred N) 0)=  (coeff_mat Hierarchy.zero
                     (mk_matrix N 1
                        (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                         Rpower (a * / a)
                           (INR i0 + 1 - 1 * / 2) *
                         sin
                           ((INR i0 + 1) * INR (m+1) * PI *
                            / INR (N + 1)))) (pred N) 0)).
    { apply (mult_one_l  (coeff_mat Hierarchy.zero
                     (mk_matrix N 1
                        (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                         Rpower (a * / a)
                           (INR i0 + 1 - 1 * / 2) *
                         sin
                           ((INR i0 + 1) * INR (m+1) * PI *
                            / INR (N + 1)))) (pred N) 0)). } rewrite H12.
    assert (coeff_mat Hierarchy.zero
                (mk_matrix N 1
                   (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                    Rpower (a * / a)
                      (INR i0 + 1 - 1 * / 2) *
                    sin
                      ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))))
                (pred N) 0= (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                    Rpower (a * / a)
                      (INR i0 + 1 - 1 * / 2) *
                    sin
                      ((INR i0 + 1) * INR (m+1) * PI * / INR (N + 1))) (pred N) 0%nat).
    { apply (coeff_mat_bij Hierarchy.zero  (fun i0 _ : nat =>sqrt (2 / INR (N + 1)) *
                         Rpower (a * / a)
                           (INR i0 + 1 - 1 * / 2) *
                         sin
                           ((INR i0 + 1) * INR (m+1) * PI *
                            / INR (N + 1))) (pred N) 0). omega. omega. } rewrite H13. reflexivity.
Qed.


Lemma inverse_eigen (m N:nat) (a b:R) :(2< N)%nat -> (0<=m<N)%nat -> 0<a -> ((invertible N (Ah N a b a) (inverse_A N a b)) /\ (LHS m N a b a= RHS m N a b a)) ->
      (Eigen_vec m N a b a) = Mmult (inverse_A N a b) (Mmult (Eigen_vec m N a b a) (Lambda m N a b a)).
Proof.
intros.
destruct H2.
unfold invertible in H2. destruct H2.
assert (Eigen_vec m N a b a= Mmult(identity N) (Eigen_vec m N a b a)). { apply iden_mat. omega. omega. nra.  }
rewrite H5. 
assert (Mmult (inverse_A N a b) (Mmult (Mmult (identity N) (Eigen_vec m N a b a)) (Lambda m N a b a))= 
        Mmult (inverse_A N a b) (Mmult (Eigen_vec m N a b a) (Lambda m N a b a))).
{  rewrite <- H5. reflexivity.  } rewrite H6.
assert ( (identity N)=  Mmult (inverse_A N a b) (Ah N a b a)). { rewrite H2. reflexivity. } rewrite H7.
assert (Mmult (inverse_A N a b) (Mmult (Ah N a b a) (Eigen_vec m N a b a))= Mmult (Mmult (inverse_A N a b) (Ah N a b a)) (Eigen_vec m N a b a)).
{ apply Mmult_assoc. } rewrite <-H8. 
assert ((Mmult (Ah N a b a) (Eigen_vec m N a b a))= LHS m N a b a). { unfold LHS. reflexivity. } rewrite H9.
assert ( (Mmult (Eigen_vec m N a b a) (Lambda m N a b a))= RHS m N a b a). { unfold RHS. reflexivity. } rewrite H10.
rewrite H3. reflexivity.
Qed.
