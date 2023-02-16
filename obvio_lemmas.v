Require Import Omega Init.Nat Arith.EqNat.
Require Import Coq.Arith.PeanoNat Coq.Structures.Equalities.



Lemma obvio_1: forall (N:nat) , (2< N) %nat -> (0 < N) %nat.
Proof.
intros. omega.
Qed.


Lemma obvio_2: forall (n m:nat) , (n < m)%nat -> (n-m)%nat = zero.
Proof.
intros. 
induction n.
induction m. reflexivity. simpl. reflexivity.
cut ( (S n- m)%nat = pred (n-m)).
+ intros. rewrite H0. rewrite IHn. simpl. reflexivity. omega.
+ omega.
Qed. 

Lemma obvio_3: forall (n:nat) , (n-n)%nat =zero.
Proof.
intros.
induction n.
auto. 
simpl. rewrite IHn. reflexivity.
Qed.

