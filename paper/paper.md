9'

# Formalizing SNARKs

## Abstract

We formalize proofs of the cryptographic soundness of several linear (todo: linear right adjective? bilnear?) SNARKs in the Lean Theorem Prover. These formalizations assume the Algebraic Group Model.

## Introduction

Over the past decade, cryptographic research has produced Succinct Non-interactive Arguments of Knowledge which allow a prover to demonstrate knowledge of a witness for any witness of any statement in NP. The most succinct of these constructions \cite{groth16} allow a proof with a single constant sized message. These constructions promise to have many applications in TODO, TODO and TODO \cite{}.

Since this new technology has applications so many tasks where security is a main concern, it is important to use SNARK constructions for which we can be confident in their cryptographic properties. To this end, SNARKs published in the academic literature come with mathematical proofs of security properties. But in despite this, it is still possible for errors to slip through the cracks. TODO discuss the past soundness errors.

To prevent errors like these from happening in the future, we look to apply more unimpeachable guarantees on the correctness of these proofs. In this project, we take several SNARKs, both from the literature and from open source SNARK libraries, and check soundness proofs for them in the Lean theorem prover. TODO, include table of SNARKs for which I have proofs. We base our proofs on the mathlib project \cite{TODO}, which provides useful built-in lemmas about multivariable polynomials. In the course of our work, we make several automated tools for assisting our proofs, including a variety of simplification attributes for dealing with statements about these polynomials and coefficients thereof, as well as a tactic to resolve certain subgoals consisting of systems of equations over a field.

### Related Work

TODO

## Overview of linear SNARKS and the AGM

TODO Overview what a SNARK is cryptographically speaking (particularly important if I'm targeting a PL conference)

TODO overview of elliptic curve pairings and the AGM

TODO Venn diagram of SNARK types

To summarize, formally proving the soundness of a TODOlinear? SNARK in the AGM model consists of

* Identifying the toxic waste elements.
* Formalizing the CRS elements as polynomials over the toxic waste elements
* Formalizing the proof elements as parametrized linear combinations of CRS elements
* Formalizing the verification equations as equations over the proof elements and CRS elements
* Formalizing the satisfaction condition.
* Formally proving that the verification equations imply the satisfaction conditions for some extraction

## Formal Techniques for the soundness proof

In this section, we discuss the specific techniques we used to create a system which is capable of formalizing linear SNARKs.

### Stage 0: Multivariate Polynomial Formalization

One consideration in formalizing linear SNARKs is the data type used to represent the multivariable polynomials in the toxic waste elements which appear throughout the proof. This turns out to be of critical importance. We discuss a few options and their benefits and drawbacks

#### Laurent Polynomials

Many SNARK constructions, including Groth '16 (TODO which others), actually do not formalize their work in terms of  polynomials, but in terms of the more general notion of Laurent polynomials. Laurent polynomials are permitted to have terms with negative exponents. Here, we encounter the problem that `mathlib` does not currently possess an implementation of multivariable laurent polynomials. To get around this, we note (as others have TODO see PLONK reference) that it is generally not necessary for Groth 16 and these other constructions to formalize using Laurent polynomials. One can simply multiply all the CRS elements in the construction by the minimum order of every toxic waste element to get a SNARK which is functionally equivalent, and which can be formalized in terms of (nonnegative-exponent-term) multivariable polynomials. Indeed, it can be easily formalized in Lean that the soundness property of the Laurent version follows from the soundness of the non-Laurent version, which we do. (TODO it is even the case that schemes for/about updatable/universal CRS are not affected by this transformation).

#### High-Degree Variables

Groth 16 and many other SNARKs have the property that there is actually only a single toxic waste element for which the maximum degree of the element depends on the circuit. This leads to an idea that proves crucial in later stages of the formalization: Instead of formalizing these polynomials using the mathlib type `mv_polynomial \sigma F` where `\sigma` is an inductively defined finite type an elements corresponding to each toxic waste element, we formalize them as `mv_polynomial \sigma (polynomial F)` where `\sigma` has elements corresponding to the bounded degree elements, and the `polynomial F` type is taken to represent polynomials in the element of arbitrary degree.

### Stage 1: Coefficients of the equations

To prove a Linear SNARK sound in the AGM is to prove that, under the assumption that the AGM representations of the proof elements satisfy the equations that the protocol specifies they should satisfy, the encoding of the QAP is satisfied. Thus, to formalize this proof in lean, we must take a collection of `mv_polynomial` equality expressions, which include various free variables in `F` (as well as parameterized collections of variables in `F`), and prove that these equations imply another equation.

A pair of multivariable polynomials are equal if and only if their coefficients are equal. Thus, we can convert our assumptions into a collection of assumptions about the equalities of coefficients of our `mv_polynomial`s. Here is where it becomes important that we have formalized these multivariable polynomials using the type `mv_polynomial \sigma (polynomial F)`, and ensured that all the orders of variables in the outer polynomial have bounded degree. Because of this, we can extract equalities of coefficients of the finitely many terms for which all the degrees are below this bound. 

For example, in the case of Groth 16, there are 4 bounded toxic waste elements, $\alpha, \beta, \gamma, \delta$. The maximum degrees of these variables in the CRS elements are (after conversion from Laurent polynomials) 1, 1, 2 and 2, respectively, and since the single equality tested in the protocol only uses pairings of linear combinations of these elements, the terms in the output can take on:

* One of 3 arities in $\alpha$, ($1, \alpha, \alpha^2$)
* One of 3 arities in $\beta$, ($1, \beta, \beta^2$)
* One of 5 arities in $\gamma$, ($1, \gamma, \gamma^2, \gamma^3, \gamma^4$)
* One of 5 arities in $\delta$, ($1, \delta, \delta^2, \delta^3, \delta^4$)

So there are at most $3 \times 3 \times 5 \times 5 = 75$ terms with nonzero coefficient. Inspection shows that only 51 of these are actually nonzero.

To isolate these equations automatically, we created three Lean simplification attributes (cite?). 

TODO rename the attributes?

* `polynomial_nf_2`, puts the polynomial equations into a normal form, with TODO
* TODO
* TODO

### Stage 2: Mutual simplification




## Specific Details SNARK

Effiency of the evaluation approach, vs automatability of the more hardcore method

TODO can the priority of lemmas in a simp set be different for each simp set? can I set it myself?

## FUture Work

One of the properties required of the extractor is that is be a polynomial time computable function in the AGM coefficients. In the case of all the SNARKs covered in this paper, this extractor is simply the projection function of one of these coefficient values, so on paper the proof of this is trivial. Still, since mathlib does not, at the time of writing, have a module for computational complexity we have been unable to verify this fact formally. Future work could extend mathlib to formalize common notions in computational complexity (and there has been some interest in doing this, see the mathlib zulipchat forum for more details), which would allow for more complete cryptographic proofs to be carried out in Lean.