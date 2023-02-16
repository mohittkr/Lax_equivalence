Require Import Reals Psatz.
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.Rbar.
Require Import Top.linear_map.
Require Import Top.continuous_linear_map. 
Require Import Coquelicot.Coquelicot.
Require Import Decidable.
Require Import Coquelicot.Rbar.


Open Scope R_scope.

(* Defining X, Y , Xh, Yh as Banach spaces (complete normed spaces)*)
Context {X: CompleteNormedModule R_AbsRing}.
Context {Xh: R -> CompleteNormedModule R_AbsRing}.
Context {Y: CompleteNormedModule R_AbsRing}.
Context {Yh: R -> CompleteNormedModule R_AbsRing}.


(* Defining a linear mapping on Banach space*)
Definition is_linear_mapping (E F: CompleteNormedModule R_AbsRing) (phi: E -> F) :=
  (forall (x y :E), phi (plus x y) = plus (phi x) (phi y))
     /\ (forall (x : E) (l:R_AbsRing), phi (scal l x) = scal l (phi x)).



(* Defining linear bounded restriction operator from E to F*)
Definition is_bounded_linear (E F: CompleteNormedModule R_AbsRing)(phi:E->F):=
     is_linear_mapping E F phi /\ (exists K:R, 0<=K /\ (forall x:E, norm(phi x) <= K* norm x)).


Context {E : CompleteNormedModule R_AbsRing}.
Context {F : CompleteNormedModule R_AbsRing}.

(* Defining uniformly bounded opaartor from E to F*)
Definition is_uniformly_bounded (E F: CompleteNormedModule R_AbsRing) (phi:E->F):=
 (is_bounded_linear E F phi) /\ (exists c1:Rbar ,forall h:R,(operator_norm (phi)) <= c1).


Variable Aop: X->Y.
Variable Ah_op: (forall (h:R), (Xh h)->(Yh h)).

(*** This lemma uses the property of linear operator to prove that phi(x-y)= phi(x)-phi(y) ,
      where x and Y belong to Banach spaces E and F respectively and phi: E->F ***************)

Lemma composition (E F:CompleteNormedModule R_AbsRing):
forall (x y: E) (phi: E->F), is_linear_mapping E F phi ->  phi( minus x y) = minus (phi x) (phi y).
Proof.
intros.
destruct H.
unfold minus.
specialize (H x (opp y)).
cut (opp(phi y)= phi(opp y)).
+ intros. rewrite H1. apply  H.
+ cut (scal (opp one) y= opp y).
  * intros. rewrite <- H1.
    cut (phi(scal (opp one) y)= scal (opp one) (phi y)).
    - intros. rewrite H2. 
      cut (scal (opp one) (phi y)=opp (phi y)).
      + intros. rewrite H3. reflexivity.
      + apply (scal_opp_one (phi y)).
    - apply (H0 y (opp one)).
  * apply (scal_opp_one y).
Qed.


(*Lemma as an argument for posreal*)
Lemma two_zero: 0<2.
Proof.
apply Rlt_R0_R2.
Qed.

(* Define f=Au , u=Ef and EhAh=I*)

(* Lax equivalence theorem to prove the convergence*)
Theorem is_convergent:
forall (u:X) (f:Y) (h:R) (uh: Xh h) (rh: forall (h:R), X -> (Xh h)) (sh: forall (h:R), Y->(Yh h))
 (E: Y->X) (Eh:forall (h:R), (Yh h)->(Xh h)), 
 is_linear_mapping X Y Aop -> f=Aop u-> (* Hypothesis that A is a linear mapping from X to Y*)
  (forall (h:R), is_linear_mapping (Xh h) (Yh h) (Ah_op h) )-> (* Hypothesis that Ah is a linear
   mapping from Xh to Yh for each h*)
  (forall (h:R), is_bounded_linear X (Xh h) (rh h))->(* Hypothesis that rh is a bounded linear
  operatior (restriction) from X to Xh for each h*)  
  (forall (h:R), is_bounded_linear Y (Yh h) (sh h))-> (* Hypothesis that sh is a bounded linear
  operator (restriction) from Y to Yh*) 
  is_bounded_linear Y X E -> (* Hypothesis that E is a bounded linear operator from Y to X*)
  u=E f-> (* Defining solution in continuous space (true solution)*)
  (forall (h:R), is_bounded_linear (Yh h) (Xh h) (Eh h))-> (* Hypotheis that Eh is a bounded 
  linear operator from Yh to Xh for each h*)
 (forall h:R, is_finite (operator_norm(Eh h))) -> (* Hypothesis that ||Eh|| is finite*)
   (uh= Eh h (sh h f))-> (* Defining a discrete solution uh*)
   ( Ah_op h uh = sh h f)-> (*f =fh*)
  (forall (h:R), rh h u= Eh h (Ah_op h (rh h u)))-> (*uh =Eh *Ah *uh, where Eh*Ah=I*)
  (forall h:R,  minus (Ah_op h (rh h u)) (sh h (Aop u)) <> zero )->

  (is_lim (fun h:R => 
      norm (minus (Ah_op h (rh h u)) (sh h (Aop u)))) 0 0 (*Consistency*) /\ 
  ( exists K:R , forall (h:R), operator_norm(Eh h)<=K ) (* Stability*)-> 
  is_lim (fun h:R=>
      norm (minus (rh h (E(f))) (Eh h (sh h (f))))) 0 0) (*Convergence*).

Proof.
intros.

destruct H12 as [H12 H13].
destruct H13 as [p H13]. 
apply (is_lim_ext ((fun h0 : R => norm (minus (Eh h0 (Ah_op h0 (rh h0 u))) (Eh h0 (sh h0 f))))) 
        (fun h0 : R => norm (minus (rh h0 (E0 f)) (Eh h0 (sh h0 f)))) 0 0).
+ intros.
  cut(Eh y (Ah_op y (rh y u)) = (rh y (E0 f))).
  - intros. rewrite H14. reflexivity.
  - symmetry. specialize (H10 y). rewrite <- H5. apply H10.
+ apply (is_lim_ext (fun h0 : R => norm (Eh h0 (minus (Ah_op h0 (rh h0 u)) (sh h0 (Aop u)))))
          (fun h0 : R => norm (minus (Eh h0 (Ah_op h0 (rh h0 u))) (Eh h0 (sh h0 f)))) 0 0).
  - intros. 
    cut(Eh y (minus (Ah_op y (rh y u)) (sh y (Aop u)))= minus (Eh y (Ah_op y (rh y u))) (Eh y (sh y f))).
    * intros. rewrite H14. reflexivity.
    * rewrite H0. apply (composition (Yh y) (Xh y) (Ah_op y (rh y u)) (sh y (Aop u)) (Eh y)). 
      unfold is_bounded_linear in H6. specialize (H6 y). destruct H6 as [H14 H15]. apply H14.
  -  cut (Rbar_locally' 0 (fun h0:R => 0 <=norm (Eh h0 (minus (Ah_op h0 (rh h0 u)) (sh h0 (Aop u))))
                  <= operator_norm (Eh h0) * norm (minus (Ah_op h0 (rh h0 u)) (sh h0 (Aop u))))).
     * intros. 
      (* Applying the sandwich theorem for limits
              In Coq, this is expressed as:
              Lemma is_lim_le_le_loc (f g h: R -> R) (x: Rbar) (l:Rbar):
                Rbar_locally' x (fun y=> f y<= h y <= g y) ->
                    is_lim f x l -> is_lim g x l -> is_lim h x l 


              Here, since the function g  is chosen as: 
                    ||Eh||*||Ah (rh u) - sh (A(u))|| (upper bound)
                    and the function f is a constant function O since from property of
                    norm 0<= ||.|| *)
        apply (is_lim_le_le_loc (fun _ => 0) 
                    (fun h0:R =>operator_norm (Eh h0) * norm (minus (Ah_op h0 (rh h0 u)) (sh h0 (Aop u))))
                        (fun h0:R => norm (Eh h0 (minus (Ah_op h0 (rh h0 u)) (sh h0 (Aop u))))) 0 0).
        apply H14. 
        apply (is_lim_const 0 0). (* Applying property of limits for a constant function*)
        cut(Rbar_locally' (Rbar_mult p 0) (fun h0:R => 0 <= operator_norm (Eh h0) * norm (minus (Ah_op h0 (rh h0 u)) (sh h0 (Aop u)))
                              <= p* norm (minus (Ah_op h0 (rh h0 u)) (sh h0 (Aop u))))).
        { intros. 
          cut(Rbar_mult p 0 = 0).
          + intros. rewrite <-H16.
             apply (is_lim_le_le_loc (fun _  =>0) (fun h0:R  => p* norm(minus (Ah_op h0 (rh h0 u)) (sh h0 (Aop u))))
                        (fun h0:R  => operator_norm (Eh h0) * norm (minus (Ah_op h0 (rh h0 u)) (sh h0 (Aop u)))) (Rbar_mult p 0) (Rbar_mult p 0)).
             apply H15.
             rewrite H16.
             apply (is_lim_const 0 0).
              (* Applying the property of limit:
                      lim_{x-> a} K*f(x)= K* lim_{x->a} f(x) *)
             apply (is_lim_scal_l (fun h0:R => norm (minus (Ah_op h0 (rh h0 u)) (sh h0 (Aop u))))
                         p (Rbar_mult p 0) 0).
             rewrite H16.
             apply H12.
          + apply (Rbar_mult_0_r p).
        }
        { 
             unfold Rbar_locally'.
                unfold locally'.
                unfold within.
                unfold locally.
                exists (mkposreal 2 two_zero).
                intros.
                split.
                cut(0*0=0).
                + intros. rewrite <- H17.
                  apply (Rmult_le_compat 0 (operator_norm (Eh y)) 0 (norm (minus (Ah_op y (rh y u)) (sh y (Aop u))))).
                  apply Rle_refl. apply Rle_refl. 
                 (* Applying the property that operator norm of Eh >=0*)
                  apply (operator_norm_ge_0' (Eh y)). 
                  (* Proving that ||a-b|| >=0 *)
                  cut (Rabs (norm (Ah_op y (rh y u))- norm (sh y (Aop u)))<= norm (minus (Ah_op y (rh y u)) (sh y (Aop u)))).
                  - intros. 
                    apply (Rle_trans 0 (Rabs (norm (Ah_op y (rh y u)) - norm (sh y (Aop u)))) 
                            (norm (minus (Ah_op y (rh y u)) (sh y (Aop u))))).
                    apply Rabs_pos.
                    apply H18.
                  - apply (norm_triangle_inv (Ah_op y (rh y u))(sh y (Aop u))).
                + nra.
             
            (* Proof that ||Eh||*||Ah (rh u) - sh (A u)|| <= K* ||Ah (rh u) -sh (A u)||
                when ||Eh||<=K*)
              apply (Rmult_le_compat_r (norm (minus (Ah_op y (rh y u)) (sh y (Aop u)))) 
                    (operator_norm (Eh y)) p).
              cut (Rabs (norm (Ah_op y (rh y u))- norm (sh y (Aop u)))<= norm (minus (Ah_op y (rh y u)) (sh y (Aop u)))).
              - intros. 
                apply (Rle_trans 0 (Rabs (norm (Ah_op y (rh y u)) - norm (sh y (Aop u)))) 
                        (norm (minus (Ah_op y (rh y u)) (sh y (Aop u))))).
                apply Rabs_pos.
                apply H17.
              - apply (norm_triangle_inv (Ah_op y (rh y u))(sh y (Aop u))).
              apply H13.
        }
        (* Proof that 0<=||Eh(Ah (rh u)- sh (A u)||<= ||Eh||||Ah rh u- sh A u||
              in an open neighborhood of 0*)
      *  unfold Rbar_locally'.
            unfold locally'.
            unfold within.
            unfold locally.
            exists (mkposreal 2 two_zero).
            intros.
            split.
            (* Proof that 0 <= norm (Eh h (minus (Ah h (rh h u)) (sh h (A u)))) *)
            cut(Eh y (minus (Ah_op y (rh y u)) (sh y (Aop u)))= minus (Eh y (Ah_op y (rh y u))) (Eh y (sh y f))).
            { intros. rewrite H16. 
              cut( Rabs(norm (Eh y (Ah_op y (rh y u))) - norm (Eh y (sh y (Aop u)))) <= norm (minus (Eh y (Ah_op y (rh y u))) (Eh y (sh y (Aop u))))).
              + intros. rewrite H0.
                apply (Rle_trans 0 (Rabs (norm (Eh y (Ah_op y (rh y u))) - norm (Eh y (sh y (Aop u)))))
                                    ( norm (minus (Eh y (Ah_op y (rh y u))) (Eh y (sh y (Aop u)))))).
                apply Rabs_pos.
                apply H17.
              + apply (norm_triangle_inv (Eh y (Ah_op y (rh y u))) (Eh y (sh y (Aop u)))).
            }
            { rewrite H0. apply (composition (Yh y) (Xh y) (Ah_op y (rh y u)) (sh y (Aop u)) (Eh y)). 
              unfold is_bounded_linear in H6. specialize (H6 y). destruct H6 as [H16 H17]. apply H16. 
            }
            
          
            (* Applying the lemma that ||Eh(Ah (rh u)- sh (A u)||<= ||Eh||||Ah rh u- sh A u||*)
            apply (operator_norm_helper' (Eh y)).
            specialize (H7 y). apply H7.
            specialize (H11 y). apply H11.
Qed.
