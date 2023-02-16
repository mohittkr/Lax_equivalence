Require Import Reals Psatz.
Require Import Coquelicot.Rbar.
Require Import Top.linear_map.
Require Import Top.continuous_linear_map. 
Require Import Omega Init.Nat Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Export lax_equivalence.
Require Export stability.
Require Import scheme_consistency.


Notation Xh:= lax_equivalence.Xh.
Notation X:= lax_equivalence.X.
Notation Y:= lax_equivalence.Y.
Notation Yh:= lax_equivalence.Yh.
Notation E:= lax_equivalence.E.
Notation F:= lax_equivalence.F.
Notation Aop:= lax_equivalence.Aop.
Notation Ah_op:= lax_equivalence.Ah_op.

Theorem scheme_convergence:
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
  (forall h:R,  minus (Ah_op h (rh h u)) (sh h (Aop u)) <> Hierarchy.zero )->

   is_lim (fun h:R=>norm (minus (rh h (E(f))) (Eh h (sh h (f))))) 0 0 .
Proof.
intros.
apply (is_convergent u f h uh).
+ auto.
+ auto.
+ auto.
+ auto.
+ auto.
+ auto.
+ auto.
+ auto.
+ auto.
+ auto.
+ auto.
+ auto.
+ auto.
+ split.
  - apply (consistency_inst u f h uh). auto. auto. auto.
  - apply (stability u f h uh).
    apply rh. apply sh. auto.
Qed.