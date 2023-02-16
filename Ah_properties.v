Require Import Reals Psatz.
Require Import Coquelicot.Hierarchy.
Require Import Omega Init.Nat Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import R_sqrt Rpower.
Require Import obvio_lemmas.



(************ Define a tri diagonal system Ah (a, b, c). b is on the diagonal, a is on the lower (sub) diagonal
    and c is on the upper (super) diagonal *********************************************************************)

Definition Ah (m:nat) (a b c:R) := mk_matrix m m
             (fun i j => if (eqb i j) then b else
                if (eqb (sub i j) one) then a else
                  if (eqb (sub j i) one) then c else 0).

(* lemma to verify that the subdiagonal entries are a *)
Lemma coeff_prop_1 (a b c:R): forall (i N:nat), (2<N)%nat ->(0<i <N)%nat ->
      coeff_mat Hierarchy.zero (Ah N a b c) i (pred i) = a .
Proof.
intros.
unfold Ah.
assert (coeff_mat Hierarchy.zero
          (mk_matrix N N  (fun i0 j : nat => 
            if i0 =? j then b else if i0 - j =? one then a else if j - i0 =? one then c else 0)) i (pred i)=(fun i0 j : nat => 
            if i0 =? j then b else if i0 - j =? one then a else if j - i0 =? one then c else 0) i (pred i)).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j : nat => 
            if i0 =? j then b else if i0 - j =? one then a else if j - i0 =? one then c else 0) i (pred i)).
  omega. omega.
} rewrite H1.
cut( i =? pred i = false).
+ intros. rewrite H2. 
  cut( i- pred i =? one = true).
  { intros. rewrite H3. nra. }
  { cut((i - pred i)% nat = one).
    + intros. rewrite H3. auto.
    + destruct i. contradict H. omega. 
      cut( pred (S i) = i).
      - intros. rewrite H3. 
        cut( (S i - i)%nat = S(i-i)).
        * intros. rewrite H4. 
          cut( (i-i)%nat = zero).
          { intros. rewrite H5. auto. }
          { apply (obvio_3 i). }
        * omega.
      - omega.
   }
+ assert (i=?pred i = false <-> i <> pred i). { apply (beq_nat_false_iff i (pred i)). }
  destruct H2. apply H3. omega.
Qed.

(* Verify that the diagonal entries are b *)
Lemma coeff_prop_2 (a b c:R): forall (i N:nat), (2<N)%nat ->(i <N)%nat ->coeff_mat Hierarchy.zero (Ah N a b c) i i = b.
Proof.
intros. unfold Ah.
assert (coeff_mat Hierarchy.zero
        (mk_matrix N N
          (fun i0 j : nat => if i0 =? j then b else if i0 - j =? one then a else if j - i0 =? one then c else 0)) i i=
           (fun i0 j : nat => if i0 =? j then b else if i0 - j =? one then a else if j - i0 =? one then c else 0) i i).
{ apply (coeff_mat_bij Hierarchy.zero 
          (fun i0 j : nat => if i0 =? j then b else if i0 - j =? one then a else if j - i0 =? one then c else 0) i i).
  omega. omega.
} rewrite H1.
assert(i=?i=true). { symmetry. apply (beq_nat_refl i). } rewrite H2.
assert(0=?0=true). { auto. } nra.
Qed.


(* verify that the super-diagonal entries are c *)
Lemma coeff_prop_3 (a b c:R): forall (i N:nat), (2<N)%nat -> (i< pred N)%nat ->
    coeff_mat Hierarchy.zero (Ah N a b c) i (i + 1) = c.
Proof.
intros. unfold Ah.
assert (coeff_mat Hierarchy.zero
        (mk_matrix N N
         (fun i0 j : nat => if i0 =? j then b else if i0 - j =? one then a else if j - i0 =? one then c else 0)) i(i + 1)=
         (fun i0 j : nat => if i0 =? j then b else if i0 - j =? one then a else if j - i0 =? one then c else 0) i (i + 1)%nat).
{ apply (coeff_mat_bij Hierarchy.zero 
          (fun i0 j : nat => if i0 =? j then b else if i0 - j =? one then a else if j - i0 =? one then c else 0) i (i + 1)%nat).
  omega. omega.
} rewrite H1.
cut( i =? i+1 = false).
+ intros. rewrite H2.
  cut(i + 1 - i =? one = true).
  * intros. rewrite H3.
  * cut((i+ 1 - i)%nat = (1+ (i-i))%nat).
    - intros. 
      cut( (i- (i+1))%nat =((i-i) -1)%nat).
      { intros. rewrite H5. 
        cut( (i-i)%nat = 0%nat).
        + intros. rewrite H6. auto.
        + apply (obvio_3 i).
      }
      { omega. }
    - omega.
    assert ((i + 1 - i)%nat= 1%nat). { omega. } rewrite H3. auto.
+ assert ((i =? i + 1) = false <-> i <> (i+1)%nat). { apply (beq_nat_false_iff i (i+1)%nat). }
  destruct H2. apply H3. omega.
Qed.


(***** Lemmas to extract zeros from Ah, i.e., work on the tridiagonal structure of Ah *)

Lemma mat_prop_1(a b c:R): forall (k N:nat) , (2 < N)%nat -> (2 <= k <= pred N)%nat -> 
      coeff_mat Hierarchy.zero (Ah N a b c) zero k = 0.
Proof.
intros. unfold Ah. 
assert (coeff_mat Hierarchy.zero
          (mk_matrix N N
             (fun i j : nat =>
              if i =? j then b
              else if i - j =? one then a
               else if j - i =? one then c else 0)) zero k =
                (fun i j : nat =>
                    if i =? j then b
                      else if i - j =? one then a
                        else if j - i =? one then c else 0) zero k).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
              if i =? j then b
               else if i - j =? one then a
                else if j - i =? one then c else 0) zero k). 
  apply obvio_1. omega. omega.
} rewrite H1.
cut( zero =? k =false).
+ intros. rewrite H2. 
  cut( zero-k =? one =false).
  - intros. rewrite H3. 
    cut( k-zero =? one=false).
    * intros. rewrite H4. nra.
    * assert ( k-zero =?one = false <-> (k-zero)%nat <> one). 
      { apply (beq_nat_false_iff (k-zero) one). }
      destruct H4. apply H5. 
      cut((k-zero)%nat = k).
      { intros. rewrite H6.
        cut( (2<= k) %nat -> (1<k)%nat).
        + intros. 
          cut( (1<k)%nat -> k <> one).
          - intros. apply H8. omega.
          - intros. destruct H8. auto. destruct H8. auto. auto.
        + omega.
      }
      { destruct k. omega. destruct k. omega. simpl. reflexivity. }
  - assert ( zero - k =? one =false <-> (zero -k)%nat <> one). 
    { apply (beq_nat_false_iff (zero-k) one). }
    destruct H3. apply H4. 
    cut( k=2%nat \/ (2<k)%nat).
    { intros. destruct H5.  
      rewrite H5. auto.
      destruct H5. auto. auto.
    }
    { omega. }
+ assert ( zero=? k = false <-> zero <> k). { apply (beq_nat_false_iff zero k). }
  destruct H2. apply H3. 
  cut( k=2%nat \/ (2<k)%nat).
  { intros. destruct H4. rewrite H4. auto. destruct H4. auto. auto. }
  { omega. }
Qed.

Lemma mat_prop_2 (a b c:R): forall (k m N:nat), (2<N)%nat -> (3 <= k <= pred N)%nat ->
    coeff_mat Hierarchy.zero (Ah N a b c) 1 k = 0.
Proof.
intros. unfold Ah.
assert (coeff_mat Hierarchy.zero (mk_matrix N N (fun i j : nat =>
            if i =? j then b
              else if i - j =? one then a
                else if j - i =? one  then c else 0)) 1 k = (fun i j : nat =>
            if i =? j then b
              else if i - j =? one then a
                else if j - i =? one  then c else 0) 1%nat k).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
            if i =? j then b
              else if i - j =? one then a
                else if j - i =? one  then c else 0) 1%nat k).
  omega. omega.
} rewrite H1.
cut(1=?k=false).
+ intros. rewrite H2.  
  cut(1 - k =? one=false).
  - intros. rewrite H3.
    cut(k-1=?one=false).
    * intros. rewrite H4. nra.
    * assert ((k - 1 =? one) = false <-> (k-1)%nat <> one). 
      { apply (beq_nat_false_iff (k-1)%nat one). }
      destruct H4. apply H5.
      cut( (3<=k)%nat -> (2 <= (k-1))%nat).
      { intros. 
        cut( (2<=(k-1))%nat -> (1< (k-1))%nat).
        + intros. 
          cut( (1 < (k-1))%nat -> (k-1)%nat <> one).
          - intros. apply H8. apply H7. omega. 
          - intros. destruct H8. auto. destruct H8. auto. auto. 
        + omega.
      }
      { omega. }
   - cut( k= 3%nat \/ (3<k)%nat).
     + intros. destruct H3.
       rewrite H3. auto.
       destruct H3. auto. auto.
     + omega.
+ cut ( k=3%nat \/ (3<k)%nat).
  - intros. destruct H2. 
    rewrite H2. auto.
  - assert ( 1=?k = false <-> 1%nat <> k). { apply (beq_nat_false_iff 1%nat k). }
     destruct H3. apply H4.
     cut( (3<=k)%nat -> 1%nat <> k).
     { intros. apply H5. omega. }
     { omega. } omega.
Qed.

Lemma mat_prop_3 (a b c:R) : forall (i k m N :nat), (2<N)%nat -> (1<i<pred N)%nat -> 
  (S (i+1) <= pred N)%nat -> (S(i+1) <= k <= pred N)%nat ->
    coeff_mat Hierarchy.zero (Ah N a b c) i k =0.
Proof.
intros. unfold Ah.
assert (coeff_mat Hierarchy.zero (mk_matrix N N (fun i0 j : nat =>
            if i0 =? j then b
              else if i0 - j =? one then a
                else if j - i0 =? one then c else 0)) i k=(fun i0 j : nat =>
            if i0 =? j then b
              else if i0 - j =? one then a
                else if j - i0 =? one then c else 0) i k).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j : nat =>
            if i0 =? j then b
              else if i0 - j =? one then a
                else if j - i0 =? one then c else 0) i k).
  omega. omega.
} rewrite H3.
cut( i=?k = false).
+ intros. rewrite H4.
  cut( i-k =?one =false).
  - intros. rewrite H5. 
    cut( k-i=?one =false).
    * intros. rewrite H6. nra.
    * assert ( k-i =?one =false <-> (k-i)%nat <> one). 
      { apply (beq_nat_false_iff (k-i) one). }
      destruct H6. apply H7. 
      cut( (S(i+1) <=k)%nat -> (2<=k-i)%nat).
      { intros.
        cut( (2<=k-i)%nat -> (1< k-i)%nat).
        + intros.
          cut( (1<k-i)%nat ->  (k-i)%nat<> one). 
          - intros. apply H10. apply H9. omega.
          - intros. destruct H10. auto. destruct H10. auto. auto.
        + omega.
      }
      { omega. }
  - assert (i-k=?one =false <-> (i-k)%nat <> one). 
    { apply (beq_nat_false_iff (i-k) one). }
    destruct H5. apply H6.
    cut ((S(i+1)<=k)%nat -> (i < k)%nat).
    * intros. 
      cut( (i<k)%nat -> (i-k)%nat = zero).
      { intros. rewrite H8. discriminate. apply H7. omega. }
      { intros. apply obvio_2. apply H8. }
    * omega.
+ assert (i=?k = false <-> i <> k). { apply (beq_nat_false_iff i k). }
  destruct H4. apply H5. omega.
Qed.

Lemma mat_prop_4 (a b c:R): forall (N:nat) , (2<N)%nat -> 
    coeff_mat Hierarchy.zero (Ah N a b c) 2 0 = 0.
Proof.
intros. unfold Ah.
assert (coeff_mat Hierarchy.zero (mk_matrix N N (fun i j : nat =>
            if i =? j then b
              else if i - j =? one then a
                else if j - i =? one then c else 0)) 2 0 =(fun i j : nat =>
            if i =? j then b
              else if i - j =? one then a
                else if j - i =? one then c else 0) 2%nat 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
            if i =? j then b
              else if i - j =? one then a
                else if j - i =? one then c else 0) 2%nat 0%nat).
  omega. omega.
} rewrite H0.
cut( 2=?0 = false).
+ intros. rewrite H1. 
  cut( 2-0 =? one = false).
  - intros. rewrite H2. 
    cut( 0-2=?one = false).
    * intros. rewrite H3. nra.
    * auto.
  - auto.
+ auto.
Qed. 

Lemma mat_prop_5 (a b c:R) : forall (i k N:nat) , (2<N)%nat ->(0 <= k <= N - 3)%nat -> 
  coeff_mat Hierarchy.zero (Ah N a b c) (pred N) k = 0.
Proof.
intros. unfold Ah.
assert (coeff_mat Hierarchy.zero (mk_matrix N N (fun i0 j : nat =>
            if i0 =? j then b
              else if i0 - j =? one then a
                else if j - i0 =? one then c else 0)) (pred N) k= (fun i0 j : nat =>
            if i0 =? j then b
              else if i0 - j =? one then a
                else if j - i0 =? one then c else 0)(pred N) k).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j : nat =>
            if i0 =? j then b
              else if i0 - j =? one then a
                else if j - i0 =? one then c else 0)(pred N) k).
  omega. omega.
} rewrite H1.
cut( pred N =? k = false).
+ intros. rewrite H2. 
  cut(pred N - k =? one =false).
  - intros. rewrite H3. 
    cut( k- pred N=?one =false).
    * intros. rewrite H4. nra.
    * assert (k - pred N=?one =false <-> (k -pred N)%nat<> one). 
      { apply (beq_nat_false_iff (k-pred N) one). }
      destruct H4. apply H5.
      cut( (k <= (N-3))%nat -> (k < pred N)%nat).
      { intros.
        cut ( (k < pred N)%nat -> (k-pred N)%nat = zero).
        + intros. rewrite H7. discriminate.
        + omega. intros. apply (obvio_2 k (pred N)). apply H7. 
      }
      { omega. }
  - assert (pred N - k =?one =false <-> (pred N -k)%nat <> one). 
    { apply (beq_nat_false_iff (pred N - k) one). }
    destruct H3. apply H4.
    cut (((pred N - k)%nat >= 2)%nat).
    * intros.
      destruct H5. auto. destruct H5. auto. auto.
    * omega. 
+ assert (pred N =?k = false <-> pred N<> k). { apply (beq_nat_false_iff (pred N) k). }
  destruct H2. apply H3. omega.
Qed.

Lemma mat_prop_6 (a b c:R): forall (i k N :nat), (2<N)%nat -> (1<i < pred N)%nat -> 
  ( 0 <= k <= pred (pred i))%nat->  coeff_mat Hierarchy.zero (Ah N a b c) i k =0.
Proof.
intros. unfold Ah.
assert (coeff_mat Hierarchy.zero (mk_matrix N N (fun i0 j : nat =>
            if i0 =? j then b
              else if i0 - j =? one then a
                else if j - i0 =? one then c else 0)) i k= (fun i0 j : nat =>
            if i0 =? j then b
              else if i0 - j =? one then a
                else if j - i0 =? one then c else 0) i k).
{ apply (coeff_mat_bij Hierarchy.zero (fun i0 j : nat =>
            if i0 =? j then b
              else if i0 - j =? one then a
                else if j - i0 =? one then c else 0) i k).
  omega. omega.
} rewrite H2.
cut (i =? k = false).
+ intros. rewrite H3. 
  cut( i- k =? one = false).
  - intros. rewrite H4. 
    cut( k - i =? one =false).
    * intros. rewrite H5. nra.
    * assert ( k- i =?one = false <-> (k-i)%nat <> one). 
      { apply (beq_nat_false_iff (k-i) one). }
      destruct H5. apply H6. 
      cut ( k = (pred (pred i)) \/ (k< (pred (pred i)))%nat).
      { intros. destruct H7. 
        rewrite H7. 
        cut((pred(pred i) - i)%nat =zero).
        + intros. rewrite H8. discriminate.
        + destruct i. simpl. reflexivity. simpl. apply obvio_2. omega.
        cut ((k < pred (pred i))%nat -> (k-i)%nat =zero).
        - intros. rewrite H8. discriminate.
        - apply H7. intros. apply obvio_2. omega.
      }
      { omega. }
  - assert ( i-k =?one = false <-> (i-k)%nat <> one). 
    { apply (beq_nat_false_iff (i-k) one). }
    destruct H4. apply H5.
    cut( (i-k)%nat =2%nat \/ ((i-k)>2)%nat).
    { intros. destruct H6. rewrite H6. auto.
      destruct H6. auto. destruct H6. auto. auto.
    }
    { omega. }
+ assert ( i=? k = false <-> i <> k). {apply (beq_nat_false_iff i k). }
  destruct H3. apply H4. omega.
Qed.


(***** destructing Ah along the column *****)
Lemma Ah_j_0 (a b c:R): forall (k N:nat), (2< N)%nat -> (2<=k<=pred N)%nat -> 
    coeff_mat Hierarchy.zero (Ah N a b c) k 0 = 0.
Proof.
intros.
unfold Ah.
assert (coeff_mat Hierarchy.zero (mk_matrix N N (fun i j : nat =>
            if i =? j then b
              else if i - j =? one then a
                else if j - i =? one then c else 0)) k 0=(fun i j : nat =>
            if i =? j then b
              else if i - j =? one then a
                else if j - i =? one then c else 0) k 0%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
            if i =? j then b
              else if i - j =? one then a
                else if j - i =? one then c else 0) k 0%nat).
  omega. omega.
} rewrite H1.
assert (k =? 0= false). 
{ assert ((k =? 0) = false <-> k <> 0%nat). { apply (beq_nat_false_iff k 0%nat). } 
destruct H2. apply H3. 
assert ( (0<k)%nat -> k <> 0%nat). { omega. } apply H4. omega. } rewrite H2.
assert (k - 0 =? one=false). assert ( (k -0)%nat = k). { omega.  } rewrite H3.
{ assert ((k =? one) = false <-> k <> one). { apply (beq_nat_false_iff k one). } destruct H4. apply H5. 
cut ( k = 2%nat \/ (2< k)%nat).
+ intros. destruct H6. rewrite H6. auto. destruct k. discriminate. destruct k. contradict H6. omega. auto.
+ omega.
} rewrite H3.
assert (0 - k =? one= false). { auto. } rewrite H4. nra.
Qed.


Lemma Ah_j_predN (a b c:R): forall (k N:nat) , (2<N)%nat -> (0<=k<=(N-3)%nat)%nat -> 
  (coeff_mat Hierarchy.zero (Ah N a b c) k (pred N))=0.
Proof.
intros.
unfold Ah.
assert (coeff_mat Hierarchy.zero (mk_matrix N N (fun i j : nat =>
          if i =? j then b
            else if i - j =? one then a
              else if j - i =? one then c else 0)) k (pred N)=(fun i j : nat =>
          if i =? j then b
            else if i - j =? one then a
              else if j - i =? one then c else 0) k (pred N)).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
          if i =? j then b
            else if i - j =? one then a
              else if j - i =? one then c else 0) k (pred N)).
  omega. omega.
} rewrite H1.
assert (k - pred N =? one=false).
{ assert ((k - pred N =? one) = false <-> (k-pred N)%nat <> one). 
  { apply (beq_nat_false_iff (k-pred N)%nat one). } 
  destruct H2. apply H3. 
  assert ( (k - pred N)%nat=zero). { apply obvio_2.  omega. } rewrite H4. discriminate. 
} rewrite H2. 
assert (pred N - k =? one =false). 
{ assert ((pred N - k =? one) = false <-> (pred N - k)%nat <> one). 
  { apply (beq_nat_false_iff (pred N -k)%nat one). } 
  destruct H3. apply H4.
  cut (((pred N - k)%nat >= 2)%nat).
  * intros.
    destruct H5. auto. destruct H5. auto. auto.
  * omega.  
} rewrite H3. 
assert ( k =? pred N = false <-> (k <> pred N)%nat).
{ apply (beq_nat_false_iff k (pred N)). }
destruct H4. rewrite H5. nra. omega.
Qed.

Lemma Ah_j_1 (a b c:R): forall (k N:nat), (2<N)%nat -> (3<=k<=pred N)%nat ->  
    (coeff_mat Hierarchy.zero (Ah N a b c) k 1)=0.
Proof.
intros.
unfold Ah.
assert (coeff_mat Hierarchy.zero (mk_matrix N N (fun i j : nat =>
            if i =? j then b
              else if i - j =? one then a
                else if j - i =? one then c else 0)) k 1= (fun i j : nat =>
            if i =? j then b
              else if i - j =? one then a
                else if j - i =? one then c else 0) k 1%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j : nat =>
            if i =? j then b
              else if i - j =? one then a
                else if j - i =? one then c else 0) k 1%nat).
  omega. omega.
} rewrite H1.
assert (k =? 1=false). 
{  assert ((k =? 1) = false <-> k <> 1%nat). 
   { apply (beq_nat_false_iff k 1%nat). } 
   destruct H2. apply H3. omega. 
} rewrite H2. 
assert (k - 1 =? one = false). 
{ assert ((k - 1 =? one) = false <-> (k-1%nat)%nat <> one). 
  { apply (beq_nat_false_iff (k-1)%nat one). } 
  destruct H3. apply H4.
  assert (k=3%nat \/ (3<k)%nat). { omega. } 
  destruct H5. rewrite H5. simpl. auto. destruct k. simpl. discriminate.
  simpl. destruct k. simpl. discriminate. simpl. destruct k. contradict H5. omega. auto. 
} rewrite H3.
assert (1 - k =? one= false). 
{ assert ((1 - k =? one) = false <-> (1-k)%nat <> one). 
  { apply (beq_nat_false_iff (1-k)%nat one). } destruct H4. apply H5. 
  assert ((1 - k)%nat =0%nat). { apply obvio_2. omega. } rewrite H6. discriminate.
} rewrite H4. nra.
Qed.

Lemma Ah_pred_j (a b c:R): forall (j k N:nat), (2<N)%nat -> (1<j<pred N)%nat -> 
  (0 <= k <= pred (pred j))%nat -> coeff_mat Hierarchy.zero (Ah N a b c) k j = 0.
Proof.
intros.
unfold Ah.
assert (coeff_mat Hierarchy.zero (mk_matrix N N (fun i j0 : nat =>
          if i =? j0 then b
            else if i - j0 =? one then a
              else if j0 - i =? one then c else 0)) k j= (fun i j0 : nat =>
          if i =? j0 then b
            else if i - j0 =? one then a
              else if j0 - i =? one then c else 0) k j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j0 : nat =>
          if i =? j0 then b
            else if i - j0 =? one then a
              else if j0 - i =? one then c else 0) k j).
  omega. omega.
} rewrite H2.
assert (k =? j =false). 
{ assert ((k =? j) = false <-> k <> j). 
  { apply (beq_nat_false_iff k j). } 
  destruct H3. apply H4. omega. 
} rewrite H3.
assert (k - j =? one = false).
{ assert ((k - j =? one) = false <-> (k-j)%nat <> one). 
  { apply (beq_nat_false_iff (k-j)%nat one). } 
  destruct H4. apply H5.
  assert ((k - j)%nat = 0%nat). { apply obvio_2. omega. } rewrite H6. discriminate.
} rewrite H4.
assert ( j - k =? one=false).
{ assert ((j - k =? one) = false <-> (j-k)%nat <> one). 
  { apply (beq_nat_false_iff (j-k)%nat one). } destruct H5. apply H6. 
    assert ((k <= pred (pred j))%nat -> (2<= (j-k)%nat)%nat). { omega. }
    destruct H1. specialize (H7 H8).
    destruct (j-k)%nat. discriminate. destruct n. contradict H8. omega. auto.
} rewrite H5. nra.
Qed.

Lemma Ah_Sj (a b c:R):forall (j k N:nat), (2<N)%nat -> (1<j<(N-2)%nat)%nat -> 
  (S (S j) <= k <= pred N)%nat ->coeff_mat Hierarchy.zero (Ah N a b c) k j = 0.
Proof.
intros.
unfold Ah.
assert (coeff_mat Hierarchy.zero (mk_matrix N N (fun i j0 : nat =>
          if i =? j0 then b
            else if i - j0 =? one then a
              else if j0 - i =? one then c else 0)) k j=(fun i j0 : nat =>
          if i =? j0 then b
            else if i - j0 =? one then a
              else if j0 - i =? one then c else 0) k j).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j0 : nat =>
          if i =? j0 then b
            else if i - j0 =? one then a
              else if j0 - i =? one then c else 0) k j).
  omega. omega.
} rewrite H2.
assert (k =? j=false).
{ assert ((k =? j) = false <-> k <> j). 
  { apply (beq_nat_false_iff k j). } destruct H3. apply H4. omega. 
} rewrite H3.
assert ((S (S j) <= k)%nat -> (2<=(k-j)%nat)%nat). { omega. } 
destruct H1. specialize (H4 H1).
assert ( k - j =? one=false).
{ assert ((k - j =? one) = false <-> (k-j)%nat <> one). 
  { apply (beq_nat_false_iff (k-j)%nat one). } destruct H6. apply H7.
  destruct (k-j)%nat. discriminate. destruct n. contradict H5. omega. auto.
} rewrite H6.
assert (j - k =? one =false).
{ assert ((j - k =? one) = false <-> (j-k)%nat <> one). 
  { apply (beq_nat_false_iff (j-k)%nat one). } destruct H7. apply H8. 
  assert ((j - k)%nat= 0%nat). { apply obvio_2. omega. } rewrite H9. discriminate. 
} rewrite H7. nra.
Qed.


Lemma Ah_j_Nminus2 (a b c:R): forall (j k N:nat), (3<N)%nat -> (0<=k<=(N-4)%nat)%nat -> 
  coeff_mat Hierarchy.zero (Ah N a b c) k (N - 2) = 0.
Proof.
intros.
unfold Ah.
assert (coeff_mat Hierarchy.zero (mk_matrix N N (fun i j0 : nat =>
          if i =? j0 then b
            else if i - j0 =? one then a
              else if j0 - i =? one then c else 0)) k (N - 2)=(fun i j0 : nat =>
          if i =? j0 then b
            else if i - j0 =? one then a
              else if j0 - i =? one then c else 0) k (N - 2)%nat).
{ apply (coeff_mat_bij Hierarchy.zero (fun i j0 : nat =>
          if i =? j0 then b
            else if i - j0 =? one then a
              else if j0 - i =? one then c else 0) k (N - 2)%nat).
  omega. omega.
} rewrite H1.
assert (k - (N - 2) =? one=false).
{ assert ((k - (N - 2) =? one) = false <-> (k - (N-2)%nat)%nat <> one). 
  { apply (beq_nat_false_iff (k - (N-2)%nat)%nat one). } destruct H2. apply H3.
  assert ((k - (N - 2))%nat=0%nat). { apply obvio_2. omega. }rewrite H4. discriminate.
} rewrite H2.
assert (N - 2 - k =? one=false).
{ assert ((N - 2 - k =? one) = false <-> ((N-2)%nat - k)%nat <> one). 
  { apply (beq_nat_false_iff ((N-2)%nat - k)%nat one). } destruct H3. apply H4. 
  assert ((k <= N - 4)%nat -> (2 <=  ((N-2)%nat - k)%nat)%nat). { omega. }
  destruct H0. specialize (H5 H6).  
  destruct (N - 2 - k)%nat. discriminate. destruct n. contradict H6. omega. auto.
} rewrite H3.
assert (k =? N - 2 = false <-> (k <> (N-2)%nat)).
{ apply (beq_nat_false_iff k (N-2)%nat). } destruct H4. rewrite H5. nra. omega.
Qed.

