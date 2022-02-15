
# Formalization of SNARKs

This repository implements a formal verification of a variety of SNARK proof systems, using the [Lean Theorem Prover](https://leanprover.github.io/), in the Algebraic Group Model. This is a work in progress.

As of 10/14/2020 the knowledge soundness proofs for [babySNARK](https://github.com/initc3/babySNARK) and the Type III Groth '16 are complete. The full proofs of these theorems can be found at the end of `knowledge_soundness.lean` in their respective directories.

## Summary of the BabySNARK code

The knowledge_soundness.lean file has several parameter statements that correspond to the parameters of the BabySNARK instantiation. These are:
  
* `F` The field over which the polynomials are defined.
* `m`, `n_stmt`, `n_wit`, corresponding to `m`, `l` and `n-l` from the paper.
* `r`, the indexed collection of roots of the polynomial `t`
* `u_stmt, u_wit`, indexed collections of single variable polynomials corresponding to the `u_i` from the paper.
* The various coefficients of the adversary polynomials given by the algebraic group model.
  
This file also defines various values from these parameters, including:

* `t`, the monic polynomial over which the modulo is taken.
* A multivariable analogue of `t`
* The multivariable polynomial forms of the CRS.
* `B_wit, V_wit, H`, multivariable polynomials of the AGM representation.
* `satisfying_wit` a proposition-valued function of a collection of field elements indicating whether they satisfy the square span program.

There are a total of ~50 lemmas across the lean files in the project. These include:

* Several lemmas that are rather general that can be found in the `/general_lemmas` directory. These lemmas seem useful enough to potentially include in mathlib itself, so I plan to submit them as pull requests to [their repo](https://github.com/leanprover-community/mathlib), barring the possibility that they already exist there. They are:
  * A lemma that shows casting a single variable polynomial to a multivariable polynomial and back leaves it unchanged.
  * A few lemmas about the divisibility properties of multivariable polynomials, in particular the fact that if a multivariable polynomial is a multiple of X then all coefficients of terms not including X are zero.
* Several lemmas specific to the soundness proof of babySNARK
  * A lemma that says (essentially) that the set of pairs of polynomials whose product is Z^2 consists of {(Z^2, 1) (Z, Z) (1, Z^2)}
  * Several lemmas of the form "The coefficient of {particular term} in such-and-such polynomial is zero"

## In the works

We are in the process of refining and expanding on this project to apply the techniques to other pairing-based SNARKs.

Some folks from CMU asked if we could expand the net to SNARKs like Marlin and Aurora. After looking at these papers, I have concluded that these constructions are too different than the ones I am dealing with to include. Some code from this repository could be useful in formalizing a soundness proof for these SNARKs, but for now, this is future work.

### Planning timeline

Here is a list of goals and dates for this project

* [x] Implement type class for proof systems/ SNARKs and formalize the correctness and knowledge-soundness (and perhaps ZK)
* [x] Implement a `ring`-like/`library-search`-like tactic to automate simplification of statements about the coefficients of polynomials
* [x] Implement a procedure to solve systems of equations of polynomials
* Implement SNARKs
  * BabySNARK
    * [x] Implementation
    * [x] Proof
  * Type III Groth '16 (as presented [here](https://eprint.iacr.org/2020/811.pdf))
    * [x] Implementation
    * [x] Proof
  * Groth '16
    * [x] Implementation
    * [x] Proof
  * Pinocchio
    * [x] Implementation
    * [x] Proof
  * GGPR
    * [x] Implementation
    * [x] Proof
  * Lipmaa
    * [ ] Implementation
    * [ ] Proof

### SNARK Table

Here is a table of the main properties of the SNARKs we formalized.

| Name                              | # Toxic Samples | # Proof elements | # CRS Element Sets | # checks | # Equations (nontrivial) | # Equations (necessary) | Compile Time |
| --------------------------------- | --------------- | ---------------- | ------------------ | -------- | ------------------------ | ----------------------- | ------------ |
| GGPR                              | 5               | 7 (only need 6)  | 19                 | 5 (4)    |                          | 17                      | 140.61 s     |
| Pinocchio (Requiring Strong QAP)  | TODO            | TODO             | TODO               | TODO     | TODO                     | TODO                    | TODO         |
| Pinocchio                         | 8               | 8                | 21                 | 5        | TODO                     | 46                      | 342.89s      |
| Groth '16                         | 5               | 3                | 8                  | 1        | TODO                     | 38 (need all? 2x check) | 13741.86s    |
| Baghery et al. (Groth Type III )) | 5               | 3                | 7 and 4            | 1        | TODO                     | 14                      | 552.67s      |
| BabySNARK                         | 3               | 3                | 4                  | 2        | TODO                     | ?                       | 74.98s       |
| Lipmaa                            | 2               | 3                | 7 and 4 and 1      | 1        | 21                       | TODO                    | TODO         |
| Lipmaa SE                         | 3               | 4                | 10 and 4 and 1     | 2        | TODO                     | TODO                    | TODO         |
