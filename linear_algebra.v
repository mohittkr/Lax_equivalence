(******* Some linear algebra tools we developed for the Coquelicot definition of matrices.
    **************************************************************************************)

Require Import Reals Psatz Omega.
Require Import Coquelicot.Hierarchy.
Require Import Coq.Init.Nat.
Require Import R_sqrt Rpower.

(* Property that (AB)^{T}= (B^{T}) * (A ^ {T}) *)
Definition mat_transpose (N:nat) (A: matrix N N):= mk_matrix N N (fun i j => coeff_mat 0 A j i).

Lemma sym_mat1: forall (N:nat) (A:matrix N N) (B: matrix N N), mat_transpose N (Mmult A B) = Mmult (mat_transpose N B) (mat_transpose N A).
Proof.
intros.
unfold mat_transpose. unfold Mmult.
apply (mk_matrix_ext N N (fun i j : nat =>
           coeff_mat 0
             (mk_matrix N N
                (fun i0 j0 : nat =>
                 sum_n
                   (fun l : nat =>
                    mult
                      (coeff_mat Hierarchy.zero A i0 l)
                      (coeff_mat Hierarchy.zero B l j0))
                   (pred N))) j i) (fun i j : nat =>
           sum_n
             (fun l : nat =>
              mult
                (coeff_mat Hierarchy.zero
                   (mk_matrix N N
                      (fun i0 j0 : nat =>
                       coeff_mat 0 B j0 i0)) i l)
                (coeff_mat Hierarchy.zero
                   (mk_matrix N N
                      (fun i0 j0 : nat =>
                       coeff_mat 0 A j0 i0)) l j))
             (pred N))).
intros.
assert (coeff_mat 0
          (mk_matrix N N
             (fun i0 j0 : nat =>
              sum_n
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i0 l)
                   (coeff_mat Hierarchy.zero B l j0))
                (pred N))) j i=  (fun i0 j0 : nat =>
              sum_n
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i0 l)
                   (coeff_mat Hierarchy.zero B l j0))
                (pred N)) j i).
{ apply (coeff_mat_bij 0 (fun i0 j0 : nat =>
              sum_n
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i0 l)
                   (coeff_mat Hierarchy.zero B l j0))
                (pred N)) j i). omega. omega. }
rewrite H1.
apply sum_n_m_ext_loc.
intros.
assert (coeff_mat Hierarchy.zero
           (mk_matrix N N
              (fun i0 j0 : nat => coeff_mat 0 B j0 i0))
           i k= (fun i0 j0 : nat => coeff_mat 0 B j0 i0) i k).
{ apply (coeff_mat_bij 0 (fun i0 j0 : nat => coeff_mat 0 B j0 i0) i k). omega. omega. } rewrite H3.
assert (coeff_mat Hierarchy.zero
             (mk_matrix N N
                (fun i0 j0 : nat => coeff_mat 0 A j0 i0))
             k j= (fun i0 j0 : nat => coeff_mat 0 A j0 i0) k j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat => coeff_mat 0 A j0 i0) k j). omega. omega. } rewrite H4.
apply Rmult_comm.
Qed.

(* Properties on symmetry and normal matrices *)

Definition symmetric_mat (N:nat) (A: matrix N N):= A = mat_transpose N A.

Lemma is_normal_mat: forall (N:nat) (A:matrix N N), symmetric_mat N A -> Mmult A (mat_transpose N A) = Mmult (mat_transpose N A) A.
Proof.
intros.
unfold symmetric_mat in H.
unfold Mmult.
apply (mk_matrix_ext N N (fun i j : nat =>
             sum_n
               (fun l : nat =>
                mult (coeff_mat Hierarchy.zero A i l)
                  (coeff_mat Hierarchy.zero (mat_transpose N A) l j))
               (pred N)) (fun i j : nat =>
   sum_n
     (fun l : nat =>
      mult (coeff_mat Hierarchy.zero (mat_transpose N A) i l)
        (coeff_mat Hierarchy.zero A l j)) 
     (pred N))).
intros. unfold sum_n.
apply sum_n_m_ext_loc.
intros.
rewrite <-H. reflexivity.
Qed.


(* Proof that (Ax)^{T} = (x^{T}) * (A ^ {T}) *)

Definition vec_transpose (N:nat) (v: matrix N 1%nat) := mk_matrix 1%nat N (fun i j => coeff_mat 0 v j i).

Lemma vec_transpose_1 : forall (N:nat) (v: matrix N 1%nat) (A: matrix N N), vec_transpose N (Mmult A v) = Mmult (vec_transpose N v) (mat_transpose N A).
Proof.
intros.
unfold vec_transpose. unfold Mmult.
apply (mk_matrix_ext 1%nat N  (fun i j : nat =>
           coeff_mat 0
             (mk_matrix N 1
                (fun i0 j0 : nat =>
                 sum_n
                   (fun l : nat =>
                    mult
                      (coeff_mat Hierarchy.zero A i0 l)
                      (coeff_mat Hierarchy.zero v l j0))
                   (pred N))) j i) (fun i j : nat =>
             sum_n
               (fun l : nat =>
                mult
                  (coeff_mat Hierarchy.zero
                     (mk_matrix 1 N
                        (fun i0 j0 : nat =>
                         coeff_mat 0 v j0 i0)) i l)
                  (coeff_mat Hierarchy.zero
                     (mat_transpose N A) l j)) 
               (pred N))).
intros.
assert (coeff_mat 0
          (mk_matrix N 1
             (fun i0 j0 : nat =>
              sum_n
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i0 l)
                   (coeff_mat Hierarchy.zero v l j0))
                (pred N))) j i= (fun i0 j0 : nat =>
              sum_n
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i0 l)
                   (coeff_mat Hierarchy.zero v l j0))
                (pred N)) j i).
{ apply (coeff_mat_bij 0  (fun i0 j0 : nat =>
              sum_n
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i0 l)
                   (coeff_mat Hierarchy.zero v l j0))
                (pred N)) j i). omega. omega. } rewrite H1.
apply sum_n_m_ext_loc.
intros.
assert (coeff_mat Hierarchy.zero
           (mk_matrix 1 N
              (fun i0 j0 : nat => coeff_mat 0 v j0 i0))
           i k= (fun i0 j0 : nat => coeff_mat 0 v j0 i0) i k). 
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat => coeff_mat 0 v j0 i0) i k). omega. omega. } rewrite H3.
unfold mat_transpose.
assert ( coeff_mat Hierarchy.zero
           (mk_matrix N N
              (fun i0 j0 : nat => coeff_mat 0 A j0 i0))
           k j= (fun i0 j0 : nat => coeff_mat 0 A j0 i0) k j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j0 : nat => coeff_mat 0 A j0 i0) k j). omega. omega. } rewrite H4.
apply Rmult_comm.
Qed.


Definition dot_product (N:nat) (v1: matrix N 1%nat) (v2: matrix N 1%nat) := Mmult (vec_transpose N v1) v2.

Definition identity (N:nat):= mk_matrix N N (fun i j => 
      if (eqb i j) then 1 else 0).

Lemma identity_def : forall (N:nat), identity N = Mone.
Proof.
intros.
unfold Mone. unfold identity. apply mk_matrix_ext. 
intros. 
assert ( i = j \/ (i <> j)). { omega. } destruct H1.
+ rewrite H1. 
  assert (Mone_seq j j= 1). { assert (1= Hierarchy.one). { reflexivity. } rewrite H2. apply (Mone_seq_diag j j). omega. }
  rewrite H2. assert (j =? j =true). { symmetry. apply (beq_nat_refl j). } rewrite H3. nra.
+ assert (Mone_seq i j= @Hierarchy.zero R_Ring).  { apply (Mone_seq_not_diag i j). apply H1. } rewrite H2.
  assert (Hierarchy.zero=0). { reflexivity. } rewrite <- H3.
  assert (i =? j=false). 
  { assert (i =? j=false <-> i <> j). { apply (beq_nat_false_iff i j). } destruct H4. apply H5. apply H1. }
  rewrite H4. reflexivity.
Qed.


Lemma iden_mat_prop: forall (N:nat) (A:matrix N N), Mmult (identity N) A = A /\ Mmult A (identity N)= A.
Proof.
intros.
split.
+ assert( (identity N) = Mone). { apply identity_def. } rewrite H. apply Mmult_one_l.
+ assert( (identity N) = Mone). { apply identity_def. } rewrite H. apply Mmult_one_r.
Qed.


(* Proof that AB = A [B_1 B_2 ... B_n] *)

Definition A_col (m N:nat) (A:matrix N N):= mk_matrix N 1%nat (fun i j => coeff_mat 0 A i m).

Lemma linear_prop_1: forall (N:nat) (A:matrix N N) (B:matrix N N), Mmult A B = mk_matrix N N (fun i j => coeff_mat 0 (Mmult A (A_col j N B)) i 0%nat).
Proof.
intros.
unfold Mmult.
apply (mk_matrix_ext N N  (fun i j : nat =>
           sum_n
             (fun l : nat =>
              mult (coeff_mat Hierarchy.zero A i l)
                (coeff_mat Hierarchy.zero B l j))
             (pred N))(fun i j : nat =>
   coeff_mat 0
     (mk_matrix N 1
        (fun i0 j0 : nat =>
         sum_n
           (fun l : nat =>
            mult
              (coeff_mat Hierarchy.zero A i0 l)
              (coeff_mat Hierarchy.zero
                 (A_col j N B) l j0)) 
           (pred N))) i 0)).
intros.
assert (coeff_mat 0
  (mk_matrix N 1
     (fun i0 j0 : nat =>
      sum_n
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero A i0 l)
           (coeff_mat Hierarchy.zero 
              (A_col j N B) l j0)) 
        (pred N))) i 0 =  (fun i0 j0 : nat =>
      sum_n
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero A i0 l)
           (coeff_mat Hierarchy.zero 
              (A_col j N B) l j0)) 
        (pred N)) i 0%nat).
{ apply (coeff_mat_bij 0 (fun i0 j0 : nat =>
      sum_n
        (fun l : nat =>
         mult (coeff_mat Hierarchy.zero A i0 l)
           (coeff_mat Hierarchy.zero 
              (A_col j N B) l j0)) 
        (pred N)) i 0%nat). omega. omega. } rewrite H1.
apply sum_n_ext_loc.
intros.
unfold A_col.
assert (coeff_mat Hierarchy.zero
     (mk_matrix N 1
        (fun i0 _ : nat => coeff_mat 0 B i0 j)) n 0= (fun i0 _ : nat => coeff_mat 0 B i0 j) n 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 _ : nat => coeff_mat 0 B i0 j) n 0%nat). omega. omega. } rewrite H3.
reflexivity.
Qed.



(* Lemma to extract mth column of matrix A *)

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

Definition single_elem_vec (m N:nat):= mk_matrix N 1%nat (fun i j => if (eqb i m) then 1 else 0).

Lemma linear_prop_2: forall (m N:nat) (A: matrix N N),(2<N)%nat /\ (0<=m<N)%nat -> Mmult A (single_elem_vec m N) = A_col m N A.
Proof.
intros.
unfold A_col. unfold Mmult.
apply (mk_matrix_ext N 1%nat (fun i j : nat =>
   sum_n
     (fun l : nat =>
      mult (coeff_mat Hierarchy.zero A i l)
        (coeff_mat Hierarchy.zero
           (single_elem_vec m N) l j)) 
     (pred N)) (fun i _ : nat => coeff_mat 0 A i m)).
intros.
assert (j=0%nat). { omega. } rewrite H2. unfold sum_n.
assert ( m= 0%nat \/ (0<m)%nat). { omega. } destruct H3.
+ rewrite H3.
  assert (sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero A i l)
               (coeff_mat Hierarchy.zero
                  (single_elem_vec 0 N) l 0)) 0 
            (pred N) =  sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero A i l)
               (coeff_mat Hierarchy.zero
                  (single_elem_vec 0 N) l 0)) 0%nat 0%nat + sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero A i l)
               (coeff_mat Hierarchy.zero
                  (single_elem_vec 0 N) l 0)) 1%nat (pred N)).
  { apply (sum_n_m_Chasles (fun l : nat =>
             mult (coeff_mat Hierarchy.zero A i l)
               (coeff_mat Hierarchy.zero
                  (single_elem_vec 0 N) l 0)) 0%nat 0%nat (pred N)). omega. omega. } rewrite H4.
  assert (sum_n_m
          (fun l : nat =>
           mult (coeff_mat Hierarchy.zero A i l)
             (coeff_mat Hierarchy.zero
                (single_elem_vec 0 N) l 0)) 1 
          (pred N)= 0).
  { assert (sum_n_m (fun l:nat => 0) 1%nat (pred N)=0). { apply sum_const_zero. omega. }  rewrite <- H5.
    apply sum_n_m_ext_loc.
    intros.
    assert (coeff_mat Hierarchy.zero  (single_elem_vec 0 N) k 0=0).
    { unfold single_elem_vec.
      assert (coeff_mat Hierarchy.zero
              (mk_matrix N 1
                 (fun i0 _ : nat =>
                  if i0 =? 0 then 1 else 0)) k 0= (fun i0 _ : nat =>
                  if i0 =? 0 then 1 else 0) k 0%nat).
      { apply (coeff_mat_bij Hierarchy.zero (fun i0 _ : nat =>
                  if i0 =? 0 then 1 else 0) k 0%nat). omega. omega. } rewrite H7.
        assert (k =? 0= false). { assert ((k =? 0) = false <-> k <> 0%nat). { apply (beq_nat_false_iff k 0%nat). } destruct H8. apply H9. omega. } 
        rewrite H8. nra. 
    } rewrite H7. apply (mult_zero_r (coeff_mat Hierarchy.zero A i k)). 
  } rewrite H5.
  assert (sum_n_m
            (fun l : nat =>
             mult (coeff_mat Hierarchy.zero A i l)
               (coeff_mat Hierarchy.zero
                  (single_elem_vec 0 N) l 0)) 0 0=  (fun l : nat =>
             mult (coeff_mat Hierarchy.zero A i l)
               (coeff_mat Hierarchy.zero
                  (single_elem_vec 0 N) l 0)) 0%nat).
  { apply (sum_n_n (fun l : nat =>
             mult (coeff_mat Hierarchy.zero A i l)
               (coeff_mat Hierarchy.zero
                  (single_elem_vec 0 N) l 0)) 0%nat). } rewrite H6.
   assert ((coeff_mat Hierarchy.zero (single_elem_vec 0 N) 0 0)=1). 
   { unfold single_elem_vec.
     assert (coeff_mat Hierarchy.zero
              (mk_matrix N 1
                 (fun i0 _ : nat =>
                  if i0 =? 0 then 1 else 0)) 0 0= (fun i0 _ : nat =>
                  if i0 =? 0 then 1 else 0) 0%nat 0%nat).
    { apply (coeff_mat_bij Hierarchy.zero (fun i0 _ : nat =>
                  if i0 =? 0 then 1 else 0) 0%nat 0%nat). omega. omega. } rewrite H7. 
    assert (0 =? 0= true). { auto. } rewrite H8. nra.
   } rewrite H7. 
   assert ( mult (coeff_mat Hierarchy.zero A i 0) 1 =  (coeff_mat Hierarchy.zero A i 0)). { apply (mult_one_r  (coeff_mat Hierarchy.zero A i 0)). } rewrite H8. 
   assert (Hierarchy.zero=0). { reflexivity. } rewrite <-H9. 
  assert ( coeff_mat Hierarchy.zero A i 0 + Hierarchy.zero = coeff_mat Hierarchy.zero A i 0). { nra. } rewrite H10. reflexivity.
+  destruct H. destruct H4. clear H4. 
   assert ((0 <m < pred N)%nat \/ (m= pred N)). { omega. } destruct H4.
   - assert (sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero A i l)
                 (coeff_mat Hierarchy.zero
                    (single_elem_vec m N) l 0)) 0 
              (pred N)= sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero A i l)
                 (coeff_mat Hierarchy.zero
                    (single_elem_vec m N) l 0)) 0%nat (pred m) + sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero A i l)
                 (coeff_mat Hierarchy.zero
                    (single_elem_vec m N) l 0)) (S (pred m)) (pred N)).
      { apply (sum_n_m_Chasles (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i l)
                   (coeff_mat Hierarchy.zero
                      (single_elem_vec m N) l 0)) 0%nat (pred m) (pred N)). omega. omega. } rewrite H6.
      assert ( S (pred m) = m). { omega. } rewrite H7.
      assert (sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i l)
                   (coeff_mat Hierarchy.zero
                      (single_elem_vec m N) l 0)) 0 
                (pred m)=0).
      { assert (sum_n_m (fun l:nat => 0) 0%nat (pred m)= 0). { apply sum_const_zero. omega. } rewrite <- H8.
        apply sum_n_m_ext_loc. intros.
        assert (coeff_mat Hierarchy.zero (single_elem_vec m N) k 0 =0).
        { unfold single_elem_vec.
          assert (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>
                        if i0 =? m then 1 else 0)) k 0= (fun i0 _ : nat =>
                        if i0 =? m then 1 else 0) k 0%nat). 
          { apply (coeff_mat_bij Hierarchy.zero (fun i0 _ : nat =>
                        if i0 =? m then 1 else 0) k 0%nat).  omega. omega. } rewrite H10.
          assert (k =? m = false). { assert ((k =? m) = false <-> k <> m). { apply (beq_nat_false_iff k m). } destruct H11. 
            apply H12. omega. } rewrite H11. nra.
        } rewrite H10. apply (mult_zero_r (coeff_mat Hierarchy.zero A i k) ).
      } rewrite H8.
      assert (sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i l)
                   (coeff_mat Hierarchy.zero
                      (single_elem_vec m N) l 0)) m 
                (pred N)= sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i l)
                   (coeff_mat Hierarchy.zero
                      (single_elem_vec m N) l 0)) m m + sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i l)
                   (coeff_mat Hierarchy.zero
                      (single_elem_vec m N) l 0)) (S m) (pred N)).
      { apply (sum_n_m_Chasles  (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i l)
                   (coeff_mat Hierarchy.zero
                      (single_elem_vec m N) l 0)) m m (pred N)). omega. omega. } rewrite H9.
      assert ( sum_n_m
                 (fun l : nat =>
                  mult (coeff_mat Hierarchy.zero A i l)
                    (coeff_mat Hierarchy.zero
                       (single_elem_vec m N) l 0)) 
                 (S m) (pred N)=0).
      { assert (sum_n_m (fun l:nat => 0) (S m) (pred N)=0). { apply sum_const_zero. omega. } rewrite <-H10.
        apply sum_n_m_ext_loc.
        intros.
        assert ((coeff_mat Hierarchy.zero (single_elem_vec m N) k 0) =0).
        { unfold single_elem_vec.
          assert (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>
                        if i0 =? m then 1 else 0)) k 0= (fun i0 _ : nat =>
                        if i0 =? m then 1 else 0) k 0%nat).
          { apply (coeff_mat_bij Hierarchy.zero (fun i0 _ : nat =>
                        if i0 =? m then 1 else 0) k 0%nat). omega. omega.
          } rewrite H12.
          assert (k =? m = false). { assert ((k =? m) = false <-> k <> m). { apply (beq_nat_false_iff k m). } destruct H13. apply H14. omega. }
          rewrite H13. nra.
        } rewrite H12.
        apply (mult_zero_r  (coeff_mat Hierarchy.zero A i k)).
      } rewrite H10.  
      assert (0 +
                  (sum_n_m
                     (fun l : nat =>
                      mult (coeff_mat Hierarchy.zero A i l)
                        (coeff_mat Hierarchy.zero
                           (single_elem_vec m N) l 0)) m m + 0)= sum_n_m
                     (fun l : nat =>
                      mult (coeff_mat Hierarchy.zero A i l)
                        (coeff_mat Hierarchy.zero
                           (single_elem_vec m N) l 0)) m m). { nra. } rewrite H11.
      assert (sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i l)
                   (coeff_mat Hierarchy.zero
                      (single_elem_vec m N) l 0)) m m= (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i l)
                   (coeff_mat Hierarchy.zero
                      (single_elem_vec m N) l 0)) m).
      { apply (sum_n_n (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i l)
                   (coeff_mat Hierarchy.zero
                      (single_elem_vec m N) l 0)) m). } rewrite H12.
      assert ((coeff_mat Hierarchy.zero  (single_elem_vec m N) m 0)=1).
      { unfold single_elem_vec. 
        assert (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>
                        if i0 =? m then 1 else 0)) m 0 =(fun i0 _ : nat =>
                        if i0 =? m then 1 else 0) m 0%nat).
        { apply (coeff_mat_bij Hierarchy.zero (fun i0 _ : nat =>
                        if i0 =? m then 1 else 0) m 0%nat). omega. omega. } rewrite H13.
        assert (m =? m= true). { symmetry. apply (beq_nat_refl m). } rewrite H14. nra.
      } rewrite H13. assert (mult (coeff_mat Hierarchy.zero A i m) 1= (coeff_mat Hierarchy.zero A i m)). { apply (mult_one_r (coeff_mat Hierarchy.zero A i m)). } 
      rewrite H14. reflexivity.
  - rewrite H4.
    assert (sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero A i l)
                 (coeff_mat Hierarchy.zero
                    (single_elem_vec (pred N) N) l 0)) 0
              (pred N)= sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero A i l)
                 (coeff_mat Hierarchy.zero
                    (single_elem_vec (pred N) N) l 0)) 0%nat (pred (pred N)) + sum_n_m
              (fun l : nat =>
               mult (coeff_mat Hierarchy.zero A i l)
                 (coeff_mat Hierarchy.zero
                    (single_elem_vec (pred N) N) l 0)) (S (pred (pred N))) (pred N)).
     { apply (sum_n_m_Chasles  (fun l : nat =>
               mult (coeff_mat Hierarchy.zero A i l)
                 (coeff_mat Hierarchy.zero
                    (single_elem_vec (pred N) N) l 0)) 0%nat (pred (pred N)) (pred N)). omega. omega. }
     rewrite H6.
     assert ((S (pred (pred N)))= pred N). { omega. } rewrite H7.
     assert (sum_n_m
                  (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero A i l)
                     (coeff_mat Hierarchy.zero
                        (single_elem_vec (pred N) N) l 0)) 0
                  (pred (pred N))=0).
      { assert (sum_n_m (fun l:nat => 0) 0%nat (pred (pred N)) = 0). { apply sum_const_zero. omega. }
        rewrite <-H8. apply sum_n_m_ext_loc. intros.
        assert (coeff_mat Hierarchy.zero  (single_elem_vec (pred N) N) k 0 =0).
        { unfold single_elem_vec.
          assert (coeff_mat Hierarchy.zero
                    (mk_matrix N 1
                       (fun i0 _ : nat =>
                        if i0 =? pred N then 1 else 0)) k 0= (fun i0 _ : nat =>
                        if i0 =? pred N then 1 else 0) k 0%nat).
          { apply (coeff_mat_bij Hierarchy.zero (fun i0 _ : nat =>
                        if i0 =? pred N then 1 else 0) k 0%nat). omega. omega. }
          rewrite H10. 
          assert ( k =? pred N = false). { assert ((k =? pred N) = false <-> k <> pred N). { apply (beq_nat_false_iff k (pred N)). } destruct H11. apply H12. omega. }
          rewrite H11. nra.
        } rewrite H10. apply (mult_zero_r (coeff_mat Hierarchy.zero A i k)).
      } rewrite H8. 
     assert (0 +
              sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i l)
                   (coeff_mat Hierarchy.zero
                      (single_elem_vec (pred N) N) l 0))
                (pred N) (pred N)= sum_n_m
                (fun l : nat =>
                 mult (coeff_mat Hierarchy.zero A i l)
                   (coeff_mat Hierarchy.zero
                      (single_elem_vec (pred N) N) l 0))
                (pred N) (pred N)). { nra. } rewrite H9.
      assert (sum_n_m
                  (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero A i l)
                     (coeff_mat Hierarchy.zero
                        (single_elem_vec (pred N) N) l 0))
                  (pred N) (pred N)= (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero A i l)
                     (coeff_mat Hierarchy.zero
                        (single_elem_vec (pred N) N) l 0)) (pred N)).
      { apply (sum_n_n (fun l : nat =>
                   mult (coeff_mat Hierarchy.zero A i l)
                     (coeff_mat Hierarchy.zero
                        (single_elem_vec (pred N) N) l 0)) (pred N)). } rewrite H10.
      assert ((coeff_mat Hierarchy.zero (single_elem_vec (pred N) N)  (pred N) 0) =1).
      { unfold single_elem_vec. 
        assert (coeff_mat Hierarchy.zero
                (mk_matrix N 1
                   (fun i0 _ : nat =>
                    if i0 =? pred N then 1 else 0)) 
                (pred N) 0 = (fun i0 _ : nat =>
                    if i0 =? pred N then 1 else 0) (pred N) 0%nat).
        { apply (coeff_mat_bij Hierarchy.zero (fun i0 _ : nat =>
                    if i0 =? pred N then 1 else 0) (pred N) 0%nat). omega. omega. } rewrite H11.
        assert ( pred N =? pred N=true). { symmetry. apply (beq_nat_refl (pred N)). } rewrite H12. nra.
      } rewrite H11. 
      assert (mult (coeff_mat Hierarchy.zero A i (pred N)) 1= (coeff_mat Hierarchy.zero A i (pred N))). 
      { apply (mult_one_r (coeff_mat Hierarchy.zero A i (pred N))). } rewrite H12. reflexivity.
Qed.


(* To prove that ||x|| = sqrt ( x^{T} * x) *)

Definition vec_norm_2 (N:nat) (v: matrix N 1%nat) := sqrt ( sum_n_m (fun l:nat => (coeff_mat 0 v l 0%nat)^2) 0%nat (pred N)).

Definition sum_elem_vec (N:nat) (v:matrix N 1%nat) := sum_n_m (fun l:nat => (coeff_mat 0 (vec_transpose N v) 0%nat l) * (coeff_mat 0 v l 0%nat)) 0 (pred N).

Lemma sum_elem_pos : forall (n m:nat) (a:nat -> R), (0<n<=m)%nat -> (forall i:nat , (n<=i<=m)%nat -> 0<= (a i)) -> 0<= sum_n_m (fun l:nat => a l) n m.
Proof.
intros.
induction m. contradict H. omega.
assert (n= S m \/ (0< n<S m)%nat). { omega. } destruct H1. 
+ rewrite H1. 
  assert (sum_n_m (fun l : nat => a l) (S m) (S m)= (fun l : nat => a l) (S m)).
  { apply (sum_n_n (fun l : nat => a l) (S m)). } rewrite H2. specialize (H0 (S m)). apply H0. omega.
  clear H.
  assert ((0 < n < S m)%nat -> (0 < n <= m)%nat). { omega. } specialize (H H1). specialize (IHm H). 
  assert (sum_n_m (fun l : nat => a l) n (S m)= sum_n_m (fun l : nat => a l) n m + (fun l : nat => a l) (S m)).
  { apply (sum_n_Sm (fun l : nat => a l)). omega. } 
  rewrite H2.
  apply Rplus_le_le_0_compat. apply IHm.
  intros. specialize (H0 i). apply H0. omega. specialize (H0 (S m)). apply H0. omega.
Qed.


Lemma elem_sqr_ge_0: forall (N:nat) (v: matrix N 1%nat) , (2< N)%nat -> 0 <= sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0 (pred N).
Proof.
intros.
assert (sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0  (pred N)= sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0%nat 0%nat + 
          sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 1%nat (pred N)).
{ apply (sum_n_m_Chasles (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0%nat 0%nat (pred N)). omega. omega. } rewrite H0.
apply Rplus_le_le_0_compat.
+ assert (sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0 0= (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0%nat).
  { apply (sum_n_n (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0%nat). } rewrite H1. nra.
+ apply sum_elem_pos. omega.
  intros. nra.
Qed.

Lemma elem_sqr_ge_0_1: forall (N:nat) (v:matrix N 1%nat), (2< N)%nat -> 0 <= sum_n_m  (fun l : nat =>  coeff_mat 0 (vec_transpose N v) 0 l *  coeff_mat 0 v l 0) 0 (pred N).
Proof.
intros.
assert (sum_n_m
          (fun l : nat =>
           coeff_mat 0 (vec_transpose N v) 0 l *
           coeff_mat 0 v l 0) 0 (pred N)= sum_n_m
                        (fun l : nat =>
                         coeff_mat 0 (vec_transpose N v) 0 l *
                         coeff_mat 0 v l 0) 0%nat 0%nat + sum_n_m
                        (fun l : nat =>
                         coeff_mat 0 (vec_transpose N v) 0 l *
                         coeff_mat 0 v l 0) 1%nat (pred N)).
{ apply (sum_n_m_Chasles  (fun l : nat =>
                 coeff_mat 0 (vec_transpose N v) 0 l *
                 coeff_mat 0 v l 0) 0%nat 0%nat (pred N)). omega. omega. } rewrite H0.
apply Rplus_le_le_0_compat.
assert (sum_n_m
            (fun l : nat =>
             coeff_mat 0 (vec_transpose N v) 0 l *
             coeff_mat 0 v l 0) 0 0= (fun l : nat =>
             coeff_mat 0 (vec_transpose N v) 0 l *
             coeff_mat 0 v l 0) 0%nat).
{ apply (sum_n_n (fun l : nat =>
             coeff_mat 0 (vec_transpose N v) 0 l *
             coeff_mat 0 v l 0) 0%nat). } rewrite H1.
unfold vec_transpose. 
assert (coeff_mat 0
            (mk_matrix 1 N
               (fun i j : nat => coeff_mat 0 v j i)) 0 0 = (fun i j : nat => coeff_mat 0 v j i) 0%nat 0%nat).
{ apply (coeff_mat_bij 0 (fun i j : nat => coeff_mat 0 v j i) 0%nat 0%nat). omega. omega. } rewrite H2. nra.
apply sum_elem_pos. omega.
intros.
unfold vec_transpose.
assert (coeff_mat 0
            (mk_matrix 1 N
               (fun i0 j : nat => coeff_mat 0 v j i0)) 0 i= (fun i0 j : nat => coeff_mat 0 v j i0) 0%nat i).
{ apply (coeff_mat_bij 0 (fun i0 j : nat => coeff_mat 0 v j i0) 0%nat i). omega. omega. }
rewrite H2. nra.
Qed.



Lemma vec_norm_prop: forall (N:nat) (v:matrix N 1%nat), (2<N)%nat -> vec_norm_2 N v = sqrt (sum_elem_vec N v).
Proof.
intros.
unfold vec_norm_2. unfold sum_elem_vec.
apply Rsqr_inj.
+ apply sqrt_pos.
+ apply sqrt_pos.
+ assert ((sqrt
   (sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2)
      0 (pred N)))²= sum_n_m (fun l : nat => coeff_mat 0 v l 0 ^ 2) 0 (pred N)). { apply Rsqr_sqrt. apply elem_sqr_ge_0. omega. } rewrite H0.
  assert ((sqrt
               (sum_n_m
                  (fun l : nat =>
                   coeff_mat 0 (vec_transpose N v) 0 l *
                   coeff_mat 0 v l 0) 0 (pred N)))² = (sum_n_m
                  (fun l : nat =>
                   coeff_mat 0 (vec_transpose N v) 0 l *
                   coeff_mat 0 v l 0) 0 (pred N))). { apply Rsqr_sqrt. apply elem_sqr_ge_0_1. omega. } rewrite H1.
  apply sum_n_m_ext_loc.
  intros.
  unfold vec_transpose. 
  assert (coeff_mat 0
              (mk_matrix 1 N
                 (fun i j : nat => coeff_mat 0 v j i)) 0 k = (fun i j : nat => coeff_mat 0 v j i) 0%nat k).
  { apply (coeff_mat_bij 0 (fun i j : nat => coeff_mat 0 v j i) 0%nat k). omega. omega. } 
  rewrite H3. nra.
Qed.


