
# Formal Baby Snark

This repository implements a formal verification of the [babySNARK](https://github.com/initc3/babySNARK) proof system, using the [Lean Theorem Prover](https://leanprover.github.io/). This is a work in progress.

As of 1/29/2020 the knowledge soundness proof for babySNARK is sorry free. The full proof of the theorem can be found at the end of knowledge_soundness.lean.

## Summary of the BabySNARK code

The knowledge_soundness.lean file has several parameter statements that match the parameters of the babySNARK instantiation. These are:
  
* $F$ The field over which the polynomials are defined.
* $m$, $n_{stmt}$, $n_{wit}$, corresponding to $m$, $l$ and $n-l$ from the paper.
* $r$, the indexed collection of roots of the polynomial $t$
* $u_{stmt}, u_{wit}$, indexed collections of single variable polynomials corresponding to the $u_i$ from the paper.
* The various coefficients of the adversary polynomials given by the algebraic group model.
  
This file also defines various values from these parameters, including:

* $t$, the monic polynomial over which the modulo is taken.
* A multivariable analogue of $t$
* The multivariable polynomial forms of the CRS.
* $B_{wit}, V_{wit}, H$, multivariable polynomials of the AGM representation.
* `satisfying_wit` a proposition-valued function of a collection of field elements indicating whether they satisfy the square span program.

There are a total of ~50 lemmas across the lean files in the project. These include:

* Several lemmas that are rather general that can be found in the `/general_lemmas` directory. These lemmas seem useful enough to potentially include in mathlib itself, so I plan to submit them as pull requests to [their repo](https://github.com/leanprover-community/mathlib), barring the possibility that they already exist there. They are:
  * A lemma that shows casting a single variable polynomial to a multivariable polynomial and back leaves it unchanged.
  * A few lemmas about the divisibility properties of multivariable polynomials, in particular the fact that if a multivariable polynomial is a multiple of X then all coefficients of terms not including X are zero.
* Several lemmas specific to the soundness proof of babySNARK
  * A lemma that says (essentially) that the set of pairs of polynomials whose product is Z^2 consists of {(Z^2, 1) (Z, Z) (1, Z^2)}
  * Several lemmas of the form "The coefficient of {particular term} in such-and-such polynomial is zero"

## In the works

As of January 2021, we are in the process of refining and expanding on this project to apply the techniques to other pairing-based SNARKs

Some folks from CMU asked if we could expand the net to SNARKs like Marlin and Aurora. After looking at these papers, I have concluded that these constructions are too different than the ones I am dealing with to include. Some code from this repository could be useful in formalizing a soundness proof for these SNARKs, but for now, this is future work.

### Planning timeline

Here is a list of goals and dates for this project

* [x] Implement type class for proof systems/ SNARKs and formalize the correctness and knowledge-soundness (and perhaps ZK)
* [x] Implement a `ring`-like/`library-search`-like tactic to automate simplification of statements about the coefficients of polynomials
* [x] Implement an alternation or decidability based way of resolving statements
* Implement SNARKs
  * BabySNARK
    * [x] Implementation
    * [x] Proof
  * Type III Groth '16 (as presented [here](https://eprint.iacr.org/2020/811.pdf))
    * [x] Implementation
    * [x] Proof
  * Groth '16
    * [x] Implementation
    * [ ] Proof
  * Pinocchio
    * [x] Implementation
    * [ ] Proof
