(********* Integrating the point wise consistency into the numerical scheme ****************)

Require Import Reals Psatz.
Require Import Coquelicot.Rbar.
Require Import Top.linear_map.
Require Import Top.continuous_linear_map. 
Require Import Omega Init.Nat Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import lax_equivalence.
Require Import pointwise_consistency.

(* Instantiation begins here *)

Notation Xh:= lax_equivalence.Xh.
Notation X:= lax_equivalence.X.
Notation Y:= lax_equivalence.Y.
Notation Yh:= lax_equivalence.Yh.
Notation E:= lax_equivalence.E.
Notation F:= lax_equivalence.F.
Notation Aop:= lax_equivalence.Aop.
Notation Ah_op:= lax_equivalence.Ah_op.

Variable N:nat.
Variable x:nat ->R.

(* u is a real valued function defined in the pointwise_consistency module *)
Notation u:= pointwise_consistency.u.

(* D is a differential opertor defined in the pointwise_consistency module *)
Notation D:= pointwise_consistency.D.

(* Imposing boundary conditions *)
Hypothesis u_0 : (D 0 (x 0))= 0.
Hypothesis u_N: (D 0 (x N)) =0.
Hypothesis u_2x: forall i:nat, (D 2 (x i)) =1.


Definition equiv_f (N:nat):= (fun h:R => Rabs (( D 0 (x 0)) */ (h*h)) + sum_n_m(fun i:nat => Rabs (( D 0 (x i -h) - 2* (D 0 (x i)) + D 0 (x i +h))*/(h^2) -1)) 1%nat (pred N)
                                  + Rabs ( (D 0 (x N))*/ (h *h))).


Hypothesis norm_eq :
  forall (u:X) (f:Y) (h:R) (uh: Xh h) (rh: forall (h:R), X -> (Xh h)) (sh: forall (h:R), Y->(Yh h))
 (E: Y->X) (Eh:forall (h:R), (Yh h)->(Xh h)),
  norm (minus (Ah_op h (rh h u)) (sh h (Aop u)))= equiv_f N h.


Hypothesis interval_1: forall i:nat, Oab (x i).
Hypothesis interval_2: forall (i:nat) (h:R), Oab (x i+h).
Hypothesis interval_3: forall (i:nat)(h:R), Oab (x i-h).

(* Defining explicitly interval for x in the domain of length (ub-lb) where lb and ub are lower and upper bounds of the interval *)
Hypothesis x_limits:
    forall (i N:nat) (lb ub y:R), (0<i<N)%nat -> (lb < (x i) < ub) /\  (y= (ub-lb)/INR (N+1)).

(*** This is where we integrate pointwise consistency with the consistency statement in the Lax equivalence theorem *******)
Lemma lim_sum:
   is_lim (fun h:R => sum_n_m (fun i:nat => Rabs (( D 0 (x i -h) - 2* (D 0 (x i)) + D 0 (x i +h))*/(h^2) -1)) 1%nat (pred N)) 0 0.
Proof.
induction N.
+ simpl. 
  apply (is_lim_ext (fun h:R => 0) (fun h : R =>sum_n_m (fun i : nat => Rabs ((D 0 (x i - h) - 2 * D 0 (x i) + D 0 (x i + h)) */ (h * (h * 1)) - 1)) 1 0)).
    * intros. symmetry.
      apply (sum_n_m_zero (fun i : nat => Rabs ((D 0 (x i - y) - 2 * D 0 (x i) + D 0 (x i + y)) */ (y * (y * 1)) - 1)) 1%nat 0%nat). omega.
    * apply is_lim_const.
+ assert ( n = 0%nat \/ (0<n)%nat). { omega. } 
  destruct H. 
  - rewrite H. simpl. 
    apply (is_lim_ext (fun h:R => 0) (fun h : R =>sum_n_m (fun i : nat => Rabs ((D 0 (x i - h) - 2 * D 0 (x i) + D 0 (x i + h)) */ (h * (h * 1)) - 1)) 1 0)).
    * intros. symmetry.
      apply (sum_n_m_zero (fun i : nat => Rabs ((D 0 (x i - y) - 2 * D 0 (x i) + D 0 (x i + y)) */ (y * (y * 1)) - 1)) 1%nat 0%nat). omega.
    * apply is_lim_const.
  - simpl.
    assert ( n = S (pred n)). { omega. }
    rewrite H0.
    apply (is_lim_ext (fun h:R =>  sum_n_m (fun i : nat => Rabs ((D 0 (x i - h) - 2 * D 0 (x i) + D 0 (x i + h)) */ h ^ 2 - 1)) 1 (Init.Nat.pred n)+
                                Rabs ((D 0 (x (S (pred n))- h) - 2 * D 0 (x (S (pred n))) + D 0 (x (S (pred n))+h))*/(h^2)-1))
                          (fun h : R =>sum_n_m (fun i : nat => Rabs ((D 0 (x i - h) - 2 * D 0 (x i) + D 0 (x i + h)) */ (h * (h * 1)) - 1)) 1 (S (Init.Nat.pred n)))).
    * intros. symmetry. 
      assert (sum_n_m (fun i : nat => Rabs((D 0 (x i - y) - 2 * D 0 (x i) + D 0 (x i + y)) */ (y * (y * 1)) - 1)) (S (pred n)) (S (pred n))=
                          Rabs ((D 0 (x (S (pred n))- y) - 2 * D 0 (x (S (pred n))) + D 0 (x (S (pred n))+y))*/(y^2)-1)).
      { apply (sum_n_n (fun i : nat => Rabs((D 0 (x i - y) - 2 * D 0 (x i) + D 0 (x i + y)) */ (y * (y * 1)) - 1)) (S (pred n))). }
      rewrite <- H1. 
      apply (sum_n_m_Chasles (fun i : nat => Rabs((D 0 (x i - y) - 2 * D 0 (x i) + D 0 (x i + y)) */ (y * (y * 1)) - 1)) 1%nat (pred n) (S (pred n))). omega. omega.
    * rewrite <- H0. 
      apply (is_lim_plus (fun h : R => sum_n_m (fun i : nat =>  Rabs((D 0 (x i - h) - 2 * D 0 (x i) + D 0 (x i + h)) */ h ^ 2 - 1)) 1 (Init.Nat.pred n))
                (fun h:R => Rabs((D 0 (x n - h) - 2 * D 0 (x n) + D 0 (x n + h)) */ h ^ 2 - 1)) 0 0 0 0).
      { apply IHn. }
      { cut(Oab (x n)-> exists gamma:R, gamma >0 /\ exists G:R, G>0/\ forall dx:R, dx>0 -> Oab ((x n)+dx) -> Oab ((x n)-dx)->(dx< gamma -> Rabs( (D 0 ((x n)+dx) - 2* (D 0 (x n)) +D 0 ((x n)-dx)) * / (dx * dx) - D 2 (x n))<= G*(dx^2))).
        + intros. 
          assert ( Oab (x n)). { apply (interval_1 n). } specialize (H1 H2). destruct H1 as [L H1]. destruct H1 as [H1 H3]. destruct H3 as [p H3]. destruct H3.
          apply (is_lim_le_le_loc (fun _ => 0) (fun h:R => p * (h^2)) 
                   (fun h : R => Rabs((D 0 (x n - h) - 2 * D 0 (x n) + D 0 (x n + h)) * / h ^ 2 - 1)) 0 0).
         * unfold Rbar_locally'. unfold locally'. unfold within. unfold locally. exists (mkposreal 2 two_zero). intros. 
           split.
          { apply Rabs_pos. }
          { specialize (H4 y). 
            assert( y>0). {
              assert (y= L/ INR(S n+1)). { 
                assert (forall (i N:nat) (lb ub y:R), (0<i<N)%nat -> (lb < (x i) < ub) /\  (y= (ub-lb)/INR (N+1))).
                { apply x_limits. } 
                specialize (H7 n (S n) 0 L y).
                assert ((0 < n < S n)%nat). { omega. } specialize (H7 H8).
                destruct H7 as [H7 H9]. assert (L-0=L). { nra. } rewrite <-H10. apply H9.
                } rewrite H7.  
              assert (L / INR (S n + 1)= L * (/ INR (S n +1))). { nra. } rewrite H8. apply Rmult_gt_0_compat.
              apply H1. apply Rinv_0_lt_compat. apply lt_0_INR. omega.
            }
            specialize (H4 H7). 
            assert ( Oab (x n+ y)). { apply (interval_2 n). } specialize (H4 H8).
            assert( Oab (x n -y)). { apply (interval_3 n). } specialize (H4 H9). 
            assert ( y < L). { 
            assert (y= L/ INR(S n+1)). { 
                assert (forall (i N:nat) (lb ub y:R), (0<i<N)%nat -> (lb < (x i) < ub) /\  (y= (ub-lb)/INR (N+1))).
                { apply x_limits. } 
                specialize (H10 n (S n) 0 L y).
                assert ((0 < n < S n)%nat). { omega. } specialize (H10 H11).
                destruct H10 as [H10 H12]. assert (L-0=L). { nra. } rewrite <-H13. apply H12.
                } rewrite H10.  
                assert ( L = L* 1). { nra. } rewrite H11.
               assert (L * 1 / INR (S n + 1) = L * (/ INR (S n + 1))). { nra. } rewrite H12.
               apply Rmult_lt_compat_l. apply H1.
               assert ( INR (S n + 1) * (/ INR (S n + 1))=1). { apply Rinv_r. apply not_0_INR. omega. } rewrite <-H13.
               assert (/ INR (S n + 1) =1 * (/ INR (S n + 1))). { nra. } rewrite H14.
               assert (INR (S n + 1) * (1 * / INR (S n + 1))=INR (S n + 1) * (/ INR (S n + 1))). { nra. } rewrite H15.
               apply Rmult_lt_compat_r. apply Rinv_0_lt_compat. apply lt_0_INR. omega. 
               apply lt_1_INR. omega.
           } 
            specialize (H4 H10). 
            assert ( D 0 (x n - y) - 2* (D 0 (x n)) + D 0 (x n +y)= D 0 (x n  +y)- 2* (D 0 (x n))+ D 0 (x n - y)). { nra. }
            rewrite H11.
            assert (D 2 (x n) =1). { apply (u_2x n). }
            rewrite H12 in H4. assert ( y*y= y^2). { nra. } rewrite H13 in H4. apply H4.
           }
         * apply is_lim_const.
         * assert (Rbar_mult p 0=0). { apply (Rbar_mult_0_r p). } rewrite <-H5.
          apply (is_lim_scal_l (fun h:R => h^2) p (Rbar_mult p 0) 0). rewrite H5.
          apply (is_lim_ext (fun h:R=> h * h) (fun h:R => h^2)). 
          { intros. nra. }
          { assert ( Rbar_mult 0 0 = 0). { apply (Rbar_mult_0_l 0). } rewrite <- H6.
            apply (is_lim_mult (fun h:R => h) (fun h:R => h) (Rbar_mult 0 0) 0 0).
            + rewrite H6. apply (is_lim_id 0).
            + rewrite H6. apply (is_lim_id 0).
            + apply Rbar_mult_correct' with 0. unfold is_Rbar_mult. unfold Rbar_mult'. assert (0 * 0 =0). { nra. } rewrite H7. reflexivity.
          }
      + apply (taylor_FD (x n)).
     }
     { unfold is_Rbar_plus. unfold Rbar_plus'. assert (0+0=0). { nra. } rewrite H1. reflexivity. }
Qed.


Theorem consistency_inst:
  forall (U:X) (f:Y) (h:R) (uh: Xh h) (rh: forall (h:R), X -> (Xh h)) (sh: forall (h:R), Y->(Yh h))
 (E: Y->X) (Eh:forall (h:R), (Yh h)->(Xh h)), 
  is_lim (fun h:R => norm (minus (Ah_op h (rh h U)) (sh h (Aop U)))) 0 0.
Proof.
intros.
apply (is_lim_ext (equiv_f N) (fun h:R => norm (minus (Ah_op h (rh h U)) (sh h (Aop U))))
          0 0).
+ intros. symmetry. apply norm_eq. now auto. apply rh. auto. apply E. apply Eh.
+ unfold equiv_f.
  apply (is_lim_ext (fun h : R => Rabs (D 0 (x 0) * / (h * h)) + (sum_n_m (fun i : nat =>
                          Rabs ((D 0 (x i - h) - 2 * D 0 (x i) + D 0 (x i + h)) * / h ^ 2 - 1)) 1
                              (Init.Nat.pred N) + Rabs (D 0 (x N) * / (h * h)))) 
                    (fun h : R => Rabs (D 0 (x 0) * / (h * h)) + sum_n_m (fun i : nat =>
                          Rabs ((D 0 (x i - h) - 2 * D 0 (x i) + D 0 (x i + h)) * / h ^ 2 - 1)) 1
                              (Init.Nat.pred N) + Rabs (D 0 (x N) * / (h * h)))).
  - intros. nra.
  - apply (is_lim_plus (fun h: R => Rabs (D 0 (x 0) * / (h * h)))
                    (fun h:R => sum_n_m (fun i : nat => Rabs ((D 0 (x i - h) - 2 * D 0 (x i) +  D 0 (x i + h)) * / h ^ 2 - 1)) 1 (Init.Nat.pred N) 
                                +  Rabs (D 0 (x N) * / (h * h))) 0 0 0 0).
    * apply (is_lim_ext (fun h:R =>0) (fun h0 : R => Rabs (D 0 (x 0) * / (h0 * h0))) 0 0).
      { intros. assert (D 0 (x 0%nat) =0). { apply u_0. } rewrite H. symmetry. 
      assert(0 * / (y * y)=0). { nra. } rewrite H0. apply Rabs_R0.
      }
      { apply is_lim_const. }
    * apply (is_lim_plus (fun h:R =>sum_n_m (fun i : nat => Rabs ((D 0 (x i - h) - 2 * D 0 (x i) +  D 0 (x i + h)) * / h ^ 2 - 1)) 1 (Init.Nat.pred N))
                          (fun h:R => Rabs (D 0 (x N) * / (h * h))) 0 0 0 0).
      { apply lim_sum. }
      { apply (is_lim_ext (fun h:R => 0) (fun h0 : R => Rabs (D 0 (x N) * / (h0 * h0))) 0 0).
        + intros. symmetry.
          assert ( D 0 (x N)=0). { apply u_N. } rewrite H.
          assert ( 0 * / (y * y)=0). { nra. } rewrite H0. apply Rabs_R0.
        + apply is_lim_const.
      }
      { unfold is_Rbar_plus. unfold Rbar_plus'. 
        cut(0+0=0).
        { intros. rewrite H. reflexivity. }
        { nra. }
      }
    * unfold is_Rbar_plus. unfold Rbar_plus'. 
      cut(0+0=0).
      { intros. rewrite H. reflexivity. }
      { nra. }
Qed.

