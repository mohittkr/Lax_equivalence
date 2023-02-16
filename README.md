The Coq files are grouped as follows:
1. Ah_properties.v : We define the tri-diagonal matrix Ah and define properties on it. These properties are lemmas on extraction of zero entries row   wise and column wise. These lemmas are then used to prove the lemmas on the spectrum of Ah and the invertibility of Ah.

2. linear_algebra.v : This file contains some linear algebra tools we developed for our formalization. 

3. combinatorics.v : This file contains formalization of some properties on combinatorics that we need to define the explicit matrix inverse of Ah.

4. Ah_inverse.v : We define an explicit inverse of Ah and verify that this is indeed the inverse of Ah using the definition: Ah Ah^{-1}= I /\ Ah^{-1} Ah = I. We also prove that the determinant of Ah, defined as Mk in this file is non-zero, for the inverse to exist.

5. Eigen_system.v : we define the eigenvalue-eigenvector pair of Ah and verify that this pair belongs to the spectrum of Ah.

6. Ah_diagonalization.v : We prove that Ah is diagonalizable. We also verify that the eigensystem is complete by verifying that the eigenvectors are independent due to its orthogonality.

7. inverse_eigen.v : In this file, we verify that the eigenvalues of Ah^{-1} are just inverse of the eigenvalues of Ah.

8. inverse_is_normal.v : In this file, we verify that Ah^{-1} is a normal matrix. 

9. stability.v : In this file, we prove stability of the scheme by integrating all of the above lemmas. [ scheme specific]

10. pointwise_consistency.v : In this file, we apply the Taylor--Lagrange theorem from the Coq.Interval library to prove pointwise consistency of the scheme.

11. scheme_consistency.v : In this file, we use the pointwise consistency from pointwise_consistency.v to prove consistency of the scheme in the domain [0, 1] and thereby relating it to the consistency statement of the Lax equivalence theorem.
[scheme specific ]

12. lax_equivalence.v : In this file, we prove the Lax equivalence theorem.

13. scheme_convergence.v : In this file, we prove convergence of the scheme in the domain [0,1] by applying the Lax equivalence theorem. When applying Lax equivalence theorem, we apply stability lemma from stability.v and consistency from scheme_consistency.v files.
[ scheme specific]

14. obvio_lemmas.v : This file contains some trivial lemmas that were required throughout the formalization.

15. scheme_determinant.v: Proof that the determinant of Ah (1/h^2, -2/h^2, 1/h^2) is non-zero. [scheme specific]

To run the .v files, following dependencies are needed (make sure to use the exact versions specified here):

* Coq 8.9.1 (https://github.com/coq/coq/releases/tag/V8.9.1)
* mathcomp 1.9.0 (https://github.com/math-comp/math-comp/releases/tag/mathcomp-1.9.0)
  Can be installed with Opam by executing:
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam install coq-mathcomp-ssreflect.1.9.0
  opam install coq-mathcomp-fingroup.1.9.0
  opam install coq-mathcomp-algebra.1.9.0
* Flocq 3.2.0 (http://flocq.gforge.inria.fr/)
* Coquelicot 3.0.3 (http://coquelicot.saclay.inria.fr/)
* coq-interval 3.4.1. (http://coq-interval.gforge.inria.fr/)
* BigNums 8.9.0 ( https://github.com/coq/bignums/releases )


Also, to run the files, you need to install "CoqLM" library which is available through:
https://www.lri.fr/~faissole/these_coq.html
(Florian Faissole is a PhD student working with Slyvie Boldo - INRIA Saclay)
This library will be installed in "user-contrib" folder and can be imported into "lax_equivalence.v" using "Require Import" command.
Note that appropriate path needs to be specified.
For instance, in our case the library was installed in "user-contrib/Top" folder.
Thus, we imported the library using:
    Require Import Top.linear_map.
where "linear_map" is a compiled .vo file from CoqLM library.
To run the file, standard Reals library and Coquelicot.Coquelicot library need to be imported. Besides, "Interval.coqapprox.taylor_thm" library
also needs to be imported. This library contains the proof of "Taylor-Lagrange theorem" which is used to prove the consistency of a
finite difference scheme.


To compile all the files, just run make. 