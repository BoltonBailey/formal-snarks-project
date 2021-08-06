

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

## Formal Techniques

In this section, we discuss the 


Polynomials over all vars vs mv_polynomial of polynomial.

## Specific Details SNARK

Effiency of the evaluation approach, vs automatability of the more hardcore method

TODO can the priority of lemmas in a simp set be different for each simp set? can I set it myself?

## FUture Work

One of the properties required of the extractor is that is be a polynomial time computable function in the AGM coefficients. In the case of all the SNARKs covered in this paper, this extractor is simply the projection function of one of these coefficient values, so on paper the proof of this is trivial. Still, since mathlib does not, at the time of writing, have a module for computational complexity we have been unable to verify this fact formally. Future work could extend mathlib to formalize common notions in computational complexity (and there has been some interest in doing this, see the mathlib zulipchat forum for more details), which would allow for more complete cryptographic proofs to be carried out in Lean.