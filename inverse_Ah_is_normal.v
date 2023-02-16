(*************** Verify that Ah_inverse is a normal matrix *****************)

Require Import Reals Psatz Omega.
Require Import Coquelicot.Hierarchy.
Require Import linear_algebra.
Require Import Ah_inverse.


Lemma inverse_is_normal (a b:R): forall (N:nat), 
  Mmult (inverse_A N a b ) (mat_transpose N (inverse_A N a b )) = 
  Mmult (mat_transpose N (inverse_A N a b )) (inverse_A N a b ).
Proof.
intros.
apply (is_normal_mat N (inverse_A N a b )).
unfold symmetric_mat.
unfold mat_transpose. unfold inverse_A. apply mk_matrix_ext.
intros.
assert (coeff_mat 0
        (mk_matrix N N
           (fun i0 j0 : nat =>
            if i0 <=? j0
            then 1 / a * (-1) ^ (i0 + j0) * (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
            else 1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) * / Mk N (b / a))) j i= 
            (fun i0 j0 : nat =>
            if i0 <=? j0
            then 1 / a * (-1) ^ (i0 + j0) * (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
            else 1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) * / Mk N (b / a)) j i).
{ apply (coeff_mat_bij 0  (fun i0 j0 : nat =>
            if i0 <=? j0
            then 1 / a * (-1) ^ (i0 + j0) * (Mk i0 (b / a) * Mk (N - j0 - 1) (b / a) * / Mk N (b / a))
            else 1 / a * (-1) ^ (i0 + j0) * (Mk j0 (b / a) * Mk (N - i0 - 1) (b / a)) * / Mk N (b / a)) j i).
  omega. omega. 
} rewrite H1. 
assert ( i=j \/ (i<j)%nat \/ (i>j)%nat). { omega. } 
destruct H2.
+ rewrite H2. assert (j <=? j=true). 
  { apply leb_correct. omega. } 
  rewrite H3. reflexivity.
+ destruct H2.
  assert (i <=? j=true). { apply leb_correct. omega. } rewrite H3.
  assert (j <=? i=false). { apply leb_correct_conv. omega. } rewrite H4. 
  assert ((i + j)%nat=(j + i)%nat ). { omega. } rewrite H5. nra.
+ assert ( i <=? j=false). { apply leb_correct_conv. omega. } rewrite H3. 
  assert (j <=? i=true). { apply leb_correct. omega. } rewrite H4.
  assert ((i + j)%nat=(j + i)%nat ). { omega. } rewrite H5. nra.
Qed.
