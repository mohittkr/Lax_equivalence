(****** Pointwise consistency for the central difference approximation of the 2nd derivative ********)


Require Import Reals Psatz.
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Coquelicot.
Require Import Omega Init.Nat Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import Interval.Interval_missing.
Require Import Interval.coqapprox.taylor_thm.


(*Defining a real valued function u(x)*)
Parameter u: R->R.

(*Defining an operator for derivatives. The operator D takes a natural number for the order of derivative and a real , x (point at which the derivative
is to be computed. The return type is real. *)
Variable D:nat->R->R. 

(* Checking for continuity and differentiability of u at x*)

Definition continuity u := forall x:R, continuity_pt u x.
Definition derivable u := forall x:R, derivable_pt u x.


(* [a b] is the interval in which the Taylor Lagrange is studied*)
Variables l r :R.

(* n is the order of derivative when the differentiability property is to verified and n is the order of continuity of u when its continuity property 
is considered *)


Variable n:nat.

(* Cab x means x lies in the closed interval [a b] *)
Notation Cab x:= (l<=x<=r).
(* Oab x means x lies in the open interval (a b) *)
Notation Oab x:=(l<x<r).



(* Define a hypothesis that \frac {d^k (u}{d x^k} at x is \frac{d^(k+1) (f)}{d x^(k+1)} in (a b)*)
Hypothesis derivable_pt_lim_Dp :
  forall k x n, (k <= n)%nat -> Oab x ->
  derivable_pt_lim (D k) x (D (S k) x).


(*Define a hypothesis that f is C^(k) continuous in [a b]*)
Hypothesis continuity_pt_Dp :
  forall k x n, (k <= n)%nat -> Cab x ->
  continuity_pt (D k) x.


(* Tcoeff is defined as \frac {d^(n) (u)}{d x^n} *)
Notation Tcoeff n x :=(D n x/(INR (fact n)) )(only parsing).

(* Tterm is defined as Tcoeff * (x-x0)^n *)
Notation Tterm n x0 x := (Tcoeff n x0 * ((x-x0)^n))(only parsing).

(* Tsum is the truncated Taylor polynomial of degree n*)
Notation Tsum n x0 x := (sum_f_R0 (fun i => Tterm i x0  x) n)(only parsing).


(* instantiate Taylor_Lagrange for u(x+dx) with n=2*)
(* Lemma statement: for x lies in (a b) , dx>0, (x+dx) in (a b), there exists a real c, such that u(x+dx)-u(x)-(du/dx)*(dx)- (1/2!)*(d^2 u / dx^2)*(dx^2)= (1/3!)*(d^3 u(c)/dx^3)*(dx^3)
                    where c in (x x+dx) *)

(* D 0 (x+dx) means u(x+dx)
  S 2 means (2+1) or 3 , S is a successor operator in Peano arithemtic for natural numbers *)


Lemma Inst_nat_upper (x dx:R):
Oab x-> dx>0-> Oab (x+dx) -> exists c:R, D 0 (x+dx) - Tsum 3 x (x+dx) = Tcoeff (S 3) c * (x+dx-x)^(S 3) /\ (x <> x+dx -> x < c < x+dx \/ x+dx < c < x).
Proof.
intros.
(* Cor_Taylor_Lagrange is the Taylor Lagrange remainder theorem:

  Cab x0 -> Cab x ->
  exists c,
  D 0 x - Tsum n x0 x =
  Tcoeff (S n) c * (x - x0)^(S n)
  /\ (x0 <> x -> x0 < c < x \/ x < c < x0).

Theorem statement: 
for x0 in [a b], x in [a b], there exists c in R, such that u(x)- u(x0)-(du(x0)/dx)*(dx)- .... - (1/n!)*(d^n u(x0)/ dx^n)*(dx^n)= (1/(n+1)!)*(d^(n+1) u(c)/dx^(n+1)
where c in (x0 x) or (x x0).

Here x0 is the point of expansion.

The theorem takes as argument, x (x+dx) and the order of expansion which in this case is 2. 
*)
apply (Cor_Taylor_Lagrange x (x+dx) 3).
intros.
apply (derivable_pt_lim_Dp k x0 3). apply H2.  
nra. nra. nra.
Qed.


(* instantiate Taylor_Lagrange for u(x-dx) with n=3*)
Lemma Inst_nat_lower(x dx: R):
Oab x->dx>0-> Oab (x-dx) -> exists c:R, D 0 (x-dx) - Tsum 3 x (x-dx) = Tcoeff (S 3) c * (x-dx-x)^(S 3)/\ (x <> x-dx -> x < c < x-dx \/ x-dx < c < x). 
Proof.
intros.
apply (Cor_Taylor_Lagrange (x-dx) x 3).
intros.
apply (derivable_pt_lim_Dp k x0 3). apply H2.  
nra. nra. nra.
Qed.

(* Proof of Taylor Lagrange for u(x+dx)*)
(* Lemma statement:

for x in (a b),
there exists eta >0 in R, M>0 in R , such that forall dx in R, dx>0,
(x+dx) in (a b) and dx < eta, 

| u(x+dx) - u(x)- (du/dx)*(dx)- (1/2!)*(d^2 u/ dx^2)*(dx^2)- (1/3!) * (d^3 u/dx^3)* (dx ^3)| <= M* (dx^4).
i.e. The truncation error is big O (dx^4)

*) 
Lemma taylor_uupper (x:R):
Oab x-> exists eta: R, eta>0 /\ exists M :R, M>0  /\forall dx:R, dx>0 ->Oab (x+dx)->  (dx<eta ->  Rabs(D 0 (x+dx) - Tsum 3 x (x+dx)) <=M*(dx^4)).
Proof.
intros.

(* here we provide an evidence for eta, i.e. existential quantification for eta.

Here i have chosen eta to be (b-x) . Reason for chosing so will be explained later *)
exists (r-x).

(* whenever there is an "and" operator in the goal, the "split" tactic splits the goal into two subgoals *)
split.
- nra. (* since x in (a b), b-x >0, nra does this mathematical reasoning to prove the subgoal *)
- 
  (* We have to provide an evidence for M to continue the proof. We chose M to be max (d^4 u /dx) in the interval [x b] since
    we are studying for u(x+dx) in (x b). 
    Thus, we use a lemma in COQ, which establishes the existence of a maximum in a compact interval for a continuous function. 
    Lemma statement: there exists a point F in R, F in [p1 p2] such that for all y in R , y in [p1 p2], f y <= f F.
                     where f is a real valued function. The maximum is f F. 
    Thus, we use this lemma for d^4 u/dx^4 to get an evidence for M.
  *)
  cut( exists F:R , (forall y:R, x<=y<=x+(r-x) ->(D 4 y) <= (D 4 F)) /\ x<=F<=x+(r-x)).
  { intros.  destruct H0 as [F H0]. (* In a hypothesis, destruct breaks it into two sub hypothesis. Since this is an 
                                        existential hypotheis, an evidence F is provided. This introduces F in the environment
                                        which will later be used. *)
    (* here, we used a lemma in COQ, which establishes the existence of a minimum in a compact interval for a continuous function.
      Lemma statement: there exists a point G in R, G in [p1 p2] such that for all y in R, y in [p1 p2], f G <= f y,
                       where f is a real valued function. The minimum is f G.
      Thus, we have introduced two lemmas so far to establish the existence of a maximum and a minimum in the interval [x b].
      These bounds will later be used to prove that the lagrange remainder d^4 u(c)/dx^4 <= M.
     *)
    cut( exists G:R , (forall y:R, x<=y<=x+(r-x) ->(D 4 G) <= (D 4 y)) /\ x<=G<=x+(r-x)).
    - intros. destruct H1 as [G H1]. (* G (the point at which d^4 u/dx^4 attains a minimum value) is introduced into the environment*)  
      
      (* We instantiate M with maximum of |d^4 u(G)/dx^4| and |d^4 u(F)/dx^4| *)
      exists (Rmax 1 (Rmax (Rabs( D 4 G/ INR (fact 4))) (Rabs(D 4 F/ INR (fact 4))))).
      split. 
       + (* Rlt_le_trans: fforall r1 r2 r3, r1 < r2 -> r2 <= r3 -> r1 < r3. 
            This lemma is used to establish that M instantiated as before is greater than 0 *)

        apply (Rlt_le_trans 0 1 (Rmax 1 (Rmax (Rabs( D 4 G/ INR (fact 4))) (Rabs(D 4 F/ INR (fact 4)))))).
          * lra. (*apply Rlt_0_1.*)
          * (*Rmax_l:  forall x y:R, x <= Rmax x y.*)
            apply Rmax_l.
       + intros. (*introduces dx and its properties into the environment*) 
      cut(Oab x-> dx>0-> Oab (x+dx) -> exists c:R, D 0 (x+dx) - Tsum 3 x (x+dx) = Tcoeff (S 3) c * (x+dx-x)^(S 3)/\ (x <> x+dx -> x < c < x+dx \/ x+dx < c < x)).
      (* We introduce the lemma defined earlier, Inst_nat_upper into the proof context. The idea is to get information on "c" which
         to be used in taylor lagrange for u(x+dx) and instantiate the order of truncation as well *)
      { intros.
        specialize (H5 H H2 H3).
        destruct H5 as [c H5]. (* destruct introduces c in the environment *)
        destruct H5 as [H5 H6]. (* destruct breaks the hypothesis H5 into two separate hypothesis which were connected by the "and" operator*)
        destruct H0 as [H0 H7]. specialize (H0 c). (* instantiate y with c *)
        assert (H8: x<=c<=x+(r-x)). {  nra. }  (* assert: This tactic introduces new hypothesis in the context. 
        Purpose of doing so is to break the hypotheis H0, which is done using "specialize" tactic in the next step.
        Since this hypotheis is a reasoning on interval, "nra" is used to prove it *)
        specialize (H0 H8). 
        destruct H1 as [H1 H9]. specialize (H1 c). specialize (H1 H8). (* Similarly, we break the hypothesis H1*)
        (* Now we have the information that (d^4 u(c)/dx^4) is bounded below by (d^4 u(G)/dx^4) and bounded above by 
           (d^4 u(F)/dx^4). This information will be used later to prove that |d^4 u(c)/dx^4| <= M *)
        
        (* Now we are in a position to prove the lemma for taylor_lagrange of u(x+dx) *)
        (* Here, we write the truncated taylor series in terms of lagrange remainder. 
          This will lead us to prove that |(d^4 u(c)/dx^4)* (dx^4)| <= M * (dx^4) i.e. the lagrange remainder is big O (dx^4) *)        
        cut ( D 0 (x+dx) - Tsum 3 x (x+dx) =  Tcoeff (S 3) c * ((x+dx) -x)^(S 3)).
        * intros. rewrite H10. 
          cut( (x+dx)-x = dx). intros. rewrite H11. 
          cut (Rabs (D 4 c / INR (fact 4) * dx ^ 4) = Rabs (D 4 c / INR (fact 4)) * dx ^ 4).
          - intros. rewrite H12.
            (*Lemma Rmult_le_compat_r :forall r r1 r2, 0 <= r -> r1 <= r2 -> r1 * r <= r2 * r.
              Purpose of introducing this lemma is to get rid of dx^4 on both sides. This is equivalent to dividing dx^4 on both sides
              since dx >0 (hypothesis H2)*)
            apply Rmult_le_compat_r. (* Applying this tactic introduces the premise that dx^3>=0 *)
            apply Rlt_le. (*Lemma Rlt_le : forall r1 r2, r1 < r2 -> r1 <= r2. 
            Purpose of doing this is to reduce the goal to dx^3>0 which can be proved by applying the hypotheis H2: dx>0*)
             apply pow_lt. apply H2.
          
          -  (* Start of proof that |d^u(c)/dx^3| <= M *)
             apply Rle_trans with  (Rmax (Rabs (D 4 G / INR (fact 4))) (Rabs (D 4 F / INR (fact 4)))). 
             apply RmaxAbs.
             (*Lemma RmaxAbs :
                forall (p q:R) r, p <= q -> q <= r -> Rabs q <= Rmax (Rabs p) (Rabs r).
                
              Purpose of using this lemma is to reduce the goal into following 2 subgoals:
              D 4 G / INR (fact 4) <= D 4 c / INR (fact 4)
              ______________________________________(2/6)
              D 4 c / INR (fact 4) <= D 4 F / INR (fact 4)

              This reduction will further help in application of the hypothesis H0 and H1 (these hypothesis gives information on the
              bounds for the lagrange remainder *)

             cut(D 4 G / INR (fact 4)= (D 4 G)*(/ INR (fact 4))).
             (* Here, we follow the process for reduction of 
                D 4 G / INR (fact 4) <= D 4 c / INR (fact 4) to D 4 G <= D 4 c.
                In the following steps,we perform a relatively long process for a basic operation of eliminating 1/4! on boh sides *)
             { intros.  rewrite H13. 
               cut(D 4 c / INR (fact 4)= (D 4 c)*(/ INR (fact 4))).
               + intros. rewrite H14. apply Rmult_le_compat_r. apply Rlt_le. 
                 apply Rinv_0_lt_compat. (*Lemma Rinv_0_lt_compat : forall r, 0 < r -> 0 < / r. *)
                 apply lt_0_INR. (*Lemma lt_0_INR : forall n:nat, (0 < n)%nat -> 0 < INR n.*)
                 simpl. (*simpl: This tactic performs mathematical simplification, i.e. it simplifies 4! to 24. *)
                 omega. (*The tactic omega, due to Pierre Crégut, is an automatic decision procedure for Presburger arithmetic.
                 It solves quantifier-free formulas built with ~, /, /`, `-> on top of equalities, inequalities and disequalities 
                 on both the type nat of natural numbers and Z of binary integers. *)
                 apply H1.
               + trivial.
              }
              { trivial. }
             (* Similarly, we carry the same process for reducing  D 4 c / INR (fact 4) <= D 4 F / INR (fact 4) to D 4 c <= D 4 F and proving it*)
             cut(D 4 c / INR (fact 4) = (D 4 c)*(/ INR(fact 4))).
             { intros. rewrite H13.
               cut(D 4 F / INR(fact 4)= (D 4 F)*(/INR (fact 4))).
               + intros. rewrite H14. apply Rmult_le_compat_r. apply Rlt_le. apply Rinv_0_lt_compat. apply lt_0_INR.  simpl. omega. apply H0.
               + trivial.
            } 
            { trivial. }
            apply Rmax_r. (*Lemma Rmax_r : forall x y:R, y <= Rmax x y.*)
             
        * rewrite Rabs_mult. (*Lemma Rabs_mult : forall x y:R, Rabs (x * y) = Rabs x * Rabs y.*)
          cut (dx^4 = (Rabs (dx^4))).  
          { intros. rewrite <- H12. reflexivity. (* reflexivity is used to prove goals of type A=B *) }
          { cut (Rabs(dx ^ 4) = dx ^ 4).
            - intros. rewrite H12. reflexivity. 
            - apply Rabs_right. (*Lemma Rabs_right : forall r, r >= 0 -> Rabs r = r. This is applicable since dx>0*)
              apply Rgt_ge. (*Lemma Rgt_ge : forall r1 r2, r1 > r2 -> r1 >= r2.
              Purpose is to reduce the goal, dx^4>=0 to dx^4>0 so that we can apply H2.*)
              apply pow_lt. apply H2. 
         } 
      + lra. apply H5.
    }
    { apply (Inst_nat_upper x dx). } (* Here we apply the lemma Inst_nat_upper since the goal statement matche with the lemma statement*)
  - (* Here we apply the lemma on the lower bound for the 3rd derivative in the interval [x b], and prove the non-dependent premises*)
    apply (continuity_ab_min (D 4) x (x+(r-x))). nra. intros. apply (continuity_pt_Dp 4 c 4). omega. nra.
  }
  {
   (* Here we apply the lemma on the upper bound for the 4th derivative in the interval [x b], and prove the non-dependent premises*)
  apply (continuity_ab_maj (D 4) x (x+(r-x))). nra. intros. apply (continuity_pt_Dp 4 c 4). omega. nra.
  } 
Qed. (* The lemma on the taylor lagrange for u(x+dx) is proved and defined*)
   

(*Proof of Taylor Lagrange for u(x-dx)*)
Lemma taylor_ulower (x:R):
Oab x -> exists delta: R, delta>0 /\ exists K :R, K>0 /\ forall dx:R, dx>0 ->Oab (x-dx)-> (dx<delta -> Rabs(D 0 (x-dx) - Tsum 3 x (x-dx)) <=K*(dx^4)).
Proof.
(* instantiate eta with (x-a)*)
exists (x-l).
split.
- nra.
- (* Introduce lemma to establish maximum of (d^4 u(y)/dx^4) in the interval [a x].*)
  cut( exists F:R , (forall y:R, x-(x-l)<=y<=x ->(D 4 y) <= (D 4 F)) /\ x-(x-l)<=F<=x).
  { intros. destruct H0 as [F H0]. (* destruct introduces F in the environment *)
    (* Introduce lemma to establish minimum of (d^4 u(y)/dx^4) in the inteval [a x]*)
    cut( exists G:R , (forall y:R, x-(x-l)<=y<=x ->(D 4 G) <= (D 4 y)) /\ x-(x-l)<=G<=x).
    - intros. destruct H1 as [G H1]. (*destruct introduces G in the environment *)

      (*instantiate K*) 
      exists (Rmax 1 (Rmax (Rabs( D 4 G/ INR (fact 4))) (Rabs(D 4 F/ INR (fact 4))))).
      split.
      + apply (Rlt_le_trans 0 1 (Rmax 1 (Rmax (Rabs( D 4 G/ INR (fact 4))) (Rabs(D 4 F/ INR (fact 4)))))).
          * lra. (*apply Rlt_0_1.*)
          *  apply Rmax_l.
      + intros.
        (* Introduce the lemma Inst_nat_lower to extract information about "c" and also to instantiate the order of approximation 
        in taylor lagrange for u(x-dx) to 2*)
        cut(Oab x-> dx>0-> Oab (x-dx) -> exists c:R, D 0 (x-dx) - Tsum 3 x (x-dx) = Tcoeff (S 3) c * (x-dx-x)^(S 3)/\ (x <> x-dx -> x < c < x-dx \/ x-dx < c < x)).
        { intros. specialize (H5 H H2 H3). (*break the hypothesis by using the information about dx already present in the environment
                                            in form of hypothesis *)
          destruct H5 as [c H5]. (* introduce "c" in the environment*)
          destruct H5 as [H5 H6]. (* Break the hypothesis into separate hypothesis connected by the "and" operator *)
          destruct H0 as [H0 H7]. specialize (H0 c). 
          assert (H8: x-(x-l)<=c<=x). {  nra. } (* Introduce a new hypothesis establishing that c lies in [a x]*)
          specialize (H0 H8). (* reduce hypothesis H0 into inequality D 4 c <= D 4 F *)
          destruct H1 as [H1 H9]. specialize (H1 c). specialize (H1 H8). (* reduce hypothesis H1 into inequality D 4 G<= D 4 c*)
        (* Now we have the information that (d^4 u(c)/dx^4) is bounded below by (d^4 u(G)/dx^4) and bounded above by 
           (d^4 u(F)/dx^4). This information will be used later to prove that |d^4 u(c)/dx^4| <= M *)
        
        (* Now we are in a position to prove the lemma for taylor_lagrange of u(x-dx) *)
        (* Here, we write the truncated taylor series in terms of lagrange remainder. 
          This will lead us to prove that |(d^4 u(c)/dx^4)* (dx^3)| <= K * (dx^4) i.e. the lagrange remainder is big O (dx^4) *) 
          cut ( D 0 (x-dx) - Tsum 3 x (x-dx) =  Tcoeff (S 3) c * ((x-dx) - x)^(S 3)).
          { intros. rewrite H10. 
            cut((x-dx)-x = -dx). 
            + intros. rewrite H11. 
              cut (Rabs (D 4 c / INR (fact 4) * (- dx) ^ 4)= (Rabs ( D 4 c / INR (fact 4))) * dx ^ 4).
              - intros. rewrite  H12.
                apply  Rmult_le_compat_r. 
                apply Rlt_le. apply pow_lt. apply H2. 
                   
             (* Start of proof that |d^4u(c)/dx^4| <= K *)
                   apply Rle_trans with  (Rmax (Rabs (D 4 G / INR (fact 4))) (Rabs (D 4 F / INR (fact 4)))).
                   apply RmaxAbs.
                  (*Lemma RmaxAbs :
                    forall (p q:R) r, p <= q -> q <= r -> Rabs q <= Rmax (Rabs p) (Rabs r).
                    
                  Purpose of using this lemma is to reduce the goal into following 2 subgoals:
                  D 4 G / INR (fact 4) <= D 4 c / INR (fact 4)
                  ______________________________________(2/6)
                  D 4 c / INR (fact 4) <= D 4 F / INR (fact 4)

                  This reduction will further help in application of the hypothesis H0 and H1 (these hypothesis gives information 
                  on the bounds for the lagrange remainder *)

                   cut(D 4 G / INR (fact 4)= (D 4 G)*(/ INR (fact 4))).
                (* Here, we follow the process for reduction of 
                D 4 G / INR (fact 4) <= D 4 c / INR (fact 4) to D 4 G <= D 4 c.
                In the following steps,we perform a relatively long process for a basic operation of eliminating 1/4! on boh sides *)
                    { intros.  rewrite H13. 
                     cut(D 4 c / INR (fact 4)= (D 4 c)*(/ INR (fact 4))).
                     + intros. rewrite H14. apply Rmult_le_compat_r. apply Rlt_le. apply Rinv_0_lt_compat. apply lt_0_INR. simpl. omega. apply H1.
                     + trivial.
                    }
                    { trivial. }
                    (* Similarly, we carry the same process for reducing  D 4 c / INR (fact 4) <= D 4 F / INR (fact 4) to D 4 c <= D 4 F and proving it*)
                   cut(D 4 c / INR (fact 4) = (D 4 c)*(/ INR(fact 4))).
                   { intros. rewrite H13.
                     cut(D 4 F / INR(fact 4)= (D 4 F)*(/INR (fact 4))).
                     + intros. rewrite H14. apply Rmult_le_compat_r. apply Rlt_le. apply Rinv_0_lt_compat. apply lt_0_INR.  simpl. omega. apply H0.
                     + trivial.
                   } 
                   { trivial. }
                  apply Rmax_r.
                 - assert ( (-dx)^4= dx ^4).
                   assert ( -dx = -1 * dx). { nra. }
                   rewrite H12. assert (dx ^4= (-1)^4 * (dx^4)). { nra. } rewrite H13. apply Rpow_mult_distr.
                   rewrite H12.  assert (Rabs (D 4 c / INR (fact 4) * dx ^ 4)= Rabs (D 4 c / INR (fact 4))* Rabs(dx^4)). { apply Rabs_mult. }
                   rewrite H13. apply Rmult_eq_compat_l. apply Rabs_right. nra. 
                + nra.
              }
            apply H5.
         }
         { apply (Inst_nat_lower x dx). } (* Here we apply the lemma Inst_nat_lower since the goal statement matches with the lemma statement *)
      - (* Here we apply the lemma on the lower bound for the 4th derivative in the interval [a x], and prove the non-dependent premises*)
        apply (continuity_ab_min (D 4) (x-(x-l)) x). nra. intros. apply (continuity_pt_Dp 4 c 4). omega. nra.
    }
    { (* Here we apply the lemma on the upper bound for the 4th derivative in the interval [a x], and prove the non-dependent premises*) 
      apply (continuity_ab_maj (D 4) (x-(x-l)) x). nra. intros. apply (continuity_pt_Dp 4 c 4). omega. nra. }         
   
Qed. (* Lemma on taylor_lagrange for u(x-dx) is proved and defined*)

(*Proof for 2nd order FD scheme, | (u(x+dx) -2* u(x) +u(x-dx))/(dx^2) - (d^2u/dx^2)| <= G*(dx^2)
  The strategy here is to rewrite the scheme into taylor lagrange for u(x+dx) and u(x-dx) and use the already
  proven lemmas to complete the proof *)


(* Theorem statement:
    for x in (a b), there exists gamma>0 in R and G >0 in R, such that forall dx >0 in R and dx<gamma, 
   | (u(x+dx) -2* u(x) +u(x-dx))/(dx^2) - (d^2u/dx^2)| <= G*(dx^2), i.e. the scheme is 2nd order accurate *)

Theorem taylor_FD (x:R):
Oab x -> exists gamma:R, gamma >0 /\ exists G:R, G>0/\ forall dx:R, dx>0 -> Oab (x+dx) -> Oab (x-dx)->(dx< gamma -> Rabs( (D 0 (x+dx) - 2* (D 0 x) +D 0 (x-dx)) * / (dx * dx) - D 2 x)<= G*(dx^2)).
Proof.
intros.

(* We would like to instantiate gamma with min (eta, delta) and G with (M+K), but so far,we have no information 
on M and K in the environment, thus we introduce the lemmas  on taylor lagrange for u(x+dx) and u(x-dx) and 
extract the informations on eta, delta, M and K *)

(* Lemma on taylor lagrange for u(x+dx)*)
cut(Oab x->  exists eta: R, eta>0 /\ exists M :R, M>0 /\forall dx:R, dx>0 ->Oab (x+dx)->(dx<eta -> Rabs(D 0 (x+dx) - Tsum 3 x (x+dx)) <=M*(dx^4))).
- intros. destruct H0 as [eta H1]. (*destruct introduces eta in the environment *)
  apply H. (* proves x in (a b)*) 
  destruct H1 as [H2 H3]. (* Breaks the hypothesis H3 into separate hypothesis connected by the "and" operator*)
  (* Lemma on taylor lagrange for u(x-dx)*)  
  cut(Oab x ->  exists delta: R, delta>0 /\exists K :R, K>0 /\ forall dx:R, dx>0 ->Oab (x-dx)-> (dx<delta -> Rabs(D 0 (x-dx) - Tsum 3 x (x-dx)) <=K*(dx^4))).
  + intros. destruct H0 as [delta H4]. (* destruct introduces delta in the environment *)
    apply H. destruct H4 as [H5 H6].
    exists (Rmin eta delta).
    split.
    { (* Proof for min(eta, delta) >0 *) 
     apply Rmin_pos. (*Lemma Rmin_pos : forall x y:R, 0 < x -> 0 < y -> 0 < Rmin x y.
     Applying this lemma, produces two subgoals, eta>0, delta>0, since we already have these information in the
     environment in form of hypothesis H2 and H5 , we just apply them in the following steps. *)
     apply H2. apply H5. }
    
     (* we now have to instantiate G , hence we revisit the lemmas on taylor lagrange for u(x+dx) and u(x-dx) 
    which are already present in the environment as hypothesis H3 and H4 respectively *)
    { destruct H3 as [M H4]. (* introduces M in the environment *)
      destruct H4 as [H7 H8]. destruct H6 as [K H6]. (* destruct introduces K in the environment*)
      destruct H6 as [H9 H10].
      exists (M+K). (* Since we now have information about M and K , we can instantiate G with (M+K) *)
      split.
      * nra. (* in the environment, we already have M>0, K>0 , hence nra uses these facts to prove (M+K)>0 *)
      * intros. (* introduces information on "dx" in the environment*)
        (* We introduce additional hypothesis dx<eta and dx< delta, these will be used to break the lemmas on 
          u(x+dx) and u(x-dx) further . We will prove these hypothesis later *)
       cut(dx<eta). 
       + cut(dx< delta).
         - intros. specialize(H8 dx H0 H1 H11). (* Use the information on dx to further break the hypothesis 
          and get the desired form of taylor lagrange for (u(x+dx)) after getting rid of the quantifiers *)
          specialize( H10 dx H0 H3 H6). 
          (* Use the information on dx to further break the hypothesis 
          and get the desired form of taylor lagrange for (u(x-dx)) after getting rid of the quantifiers *)

          (* Next , we will decompose the scheme into the lemmas on taylor lagrange for u(x+dx) and u(x-dx) and apply those lemmas separately
            to complete the proof *)
          apply Rmult_le_reg_r with (dx^2).
          * nra.
          * assert((M + K) * dx ^ 2 * dx ^ 2= (M+K) * (dx ^4)). { nra. }
            rewrite H12. 
            cut( Rabs(dx^2)= dx^2).
            { intros. rewrite <- H13.
              assert (Rabs (((D 0 (x + dx) - 2 * D 0 x + D 0 (x - dx)) * / (dx * dx) - D 2 x) * (dx ^2))=
                         Rabs ((D 0 (x + dx) - 2 * D 0 x + D 0 (x - dx)) * / (dx * dx) - D 2 x) * Rabs (dx ^ 2)).
              { apply Rabs_mult. }
              rewrite <- H14.
              assert(((D 0 (x + dx) - 2 * D 0 x + D 0 (x - dx)) * / (dx * dx) - D 2 x) * dx ^ 2=
                      ((D 0 (x + dx) - 2 * D 0 x + D 0 (x - dx)) - (D 2 x) * (dx^2))).
              { assert ( dx*dx = dx^2). { nra. } rewrite H15. 
                assert (((D 0 (x + dx) - 2 * D 0 x + D 0 (x - dx)) * / dx ^ 2 - D 2 x) * dx ^ 2=
                        ((D 0 (x + dx) - 2 * D 0 x + D 0 (x - dx)) * / dx ^ 2) * (dx ^2) -D 2 x * dx ^ 2). { nra. }
                rewrite H16. 
                assert ((D 0 (x + dx) - 2 * D 0 x + D 0 (x - dx)) * / dx ^ 2 * dx ^ 2= (D 0 (x + dx) - 2 * D 0 x + D 0 (x - dx))).
                { assert(((D 0 (x + dx) - 2 * D 0 x + D 0 (x - dx)) * / dx ^ 2 )* dx ^ 2 = (D 0 (x + dx) - 2 * D 0 x + D 0 (x - dx)) * (dx^2) */ (dx^2)). { nra. }
                  rewrite H17. apply Rinv_r_simpl_l. nra.
                }
                rewrite H17. reflexivity.
              }
              rewrite H15.
              assert (( D 2 x) * (dx^2)= ((D 2 x)/(INR (fact 2)))*(dx ^2) +  ((D 2 x)/(INR (fact 2)))*(dx ^2)). 
              { assert (INR (fact 2) = 2). { assert ( fact 2= 2%nat). { unfold fact. omega. } rewrite H16. trivial. }
                rewrite H16. nra.
              }
              rewrite H16. 
              assert ( (D 0 (x + dx) - 2 * D 0 x + D 0 (x - dx) - (D 2 x / INR (fact 2) * dx ^ 2 + D 2 x / INR (fact 2) * dx ^ 2))=
                        (D 0 (x+dx) - (D 0 x + D 1 x * dx + D 2 x / INR (fact 2) * dx ^ 2 + (D 3 x / INR (fact 3)) * dx ^3)) + ( D 0 (x-dx) - (D 0 x - D 1 x * dx + D 2 x / INR (fact 2) * dx ^ 2- (D 3 x/ INR (fact 3))* (dx ^3)))). { nra. }
              rewrite H17. 
              cut( (D 0 x + D 1 x * dx + D 2 x / INR (fact 2) * dx ^ 2 + (D 3 x/ INR (fact 3))* (dx ^3))= Tsum 3 x (x+dx)).
              + intros. rewrite H18. 
                cut((D 0 x - D 1 x * dx + D 2 x / INR (fact 2) * dx ^ 2 - D 3 x / INR (fact 3) * dx ^ 3)= Tsum 3 x (x-dx)).
                - intros. rewrite H19.
                  apply Rle_trans with (Rabs(D 0 (x + dx) - sum_f_R0 (fun i : nat => D i x / INR (fact i) * (x + dx - x) ^ i) 3)+
                                        Rabs ((D 0 (x - dx) - sum_f_R0 (fun i : nat => D i x / INR (fact i) * (x - dx - x) ^ i) 3))).
                  * apply Rabs_triang.
                  * assert ((M + K) * dx ^ 4= M * (dx ^4) + K * (dx ^4)). { nra. }
                    rewrite H20. apply Rplus_le_compat. 
                    apply H8. 
                    apply H10.
                - unfold sum_f_R0. assert (x-dx-x= -dx). { nra. } rewrite H19.
                  assert (fact 0 =1%nat). { simpl. reflexivity. } rewrite H20.
                  assert (fact 1= 1%nat). { simpl. reflexivity. } rewrite H21. 
                  assert (INR 1= 1). { reflexivity. } rewrite H22. 
                  assert (D 0 x / 1 * (- dx) ^ 0= D 0 x). { nra. } rewrite H23.
                  assert ( D 1 x / 1 * (- dx) ^ 1 = - D 1 x * dx). { nra. } rewrite H24.
                  assert (D 3 x / INR (fact 3) * (- dx) ^ 3= - D 3 x / INR (fact 3) * dx ^ 3).  { nra. } rewrite H25.
                  assert ( (-dx)^2 = dx ^2). { nra. } rewrite H26. nra. 
              + unfold sum_f_R0. assert (x+dx -x = dx). { nra. } rewrite H18. 
                assert (fact 0 =1%nat). { simpl. reflexivity. } rewrite H19.
                assert (fact 1= 1%nat). { simpl. reflexivity. } rewrite H20. 
                assert (D 0 x / INR 1 * dx ^ 0 = D 0 x). { assert (dx^0=1). { nra. } rewrite H21. assert (INR 1=1). { reflexivity. } rewrite H22. nra. }
                rewrite H21.
                assert (D 1 x / INR 1 * dx ^ 1 = D 1 x * dx). { assert (INR 1 =1). { reflexivity. } rewrite H22. nra. }
                rewrite H22. reflexivity.
              }
              { apply Rabs_right. nra. }
           -  (* Proof for dx< delta*)
               apply (Rmin_Rgt eta) in H4. destruct H4 as [H11 H12]. (*We have dx < Rmin eta delta as our hypothesis H4. 
                Rmin_Rgt tactic breaks H4 into dx < eta and dx < delta. we will use the later in this proof*)
               apply H12.
        + (*Proof for dx < eta*)
           apply (Rmin_Rgt eta) in H4. (*Lemma Rmin_Rgt : forall r1 r2 r, Rmin r1 r2 > r <-> r1 > r /\ r2 > r.
           We have dx < Rmin eta delta as our hypothesis H4. Rmin_Rgt tactic breaks H4 into dx < eta and dx < delta. we will use the former in this proof*)
           destruct H4 as [H11 H12]. (* breaks the modified hypothesis H4 into two separate hypotheis dx<eta and dx<delta so that these can be ready to 
           be applied *) 
           apply H11.
      }
   + apply (taylor_ulower x). 
- apply (taylor_uupper x).
Qed.
    