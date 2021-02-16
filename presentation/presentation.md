
# Formal SNARKs

--------

## What Is This Project?

We are formalizing soundness proofs of pairing-based SNARKs

<!-- There are a wide array of such SNARKs (they have benefits such as constant proof size). A newcomer to SNARKs should just know that these are a nice, general class of SNARKs. -->

This formalization is done in the Lean Theorem Prover

* Lean seems to be an active language right now
* The mathlib library has support for multivariable polynomials which is critical
* The mathlib community is open to accepting pull requests, which has been convenient
* ... and I'm sure many other reasons!

--------

## The Current State of the Project

We have implemented a proof of the Knowledge-soundness of the BabySNARK protocol in the Algebraic Group model

We are in the process of formalizing statements of other pairing-based SNARKs in the AGM:

* Groth16 
* The GGPR version from the Pinocchio paper.

--------

## What We Would Like To Do

Build up a small library of SNARKs with formal proofs.

Build a framework to make it convenient to formalize new SNARK proofs

* Write tactics for facilitating proofs about polynomials and their coefficients.
* Write a general framework for pairing based SNARK schemes.

--------

## Primer on Baby SNARK - Square Span Program

Baby SNARK works on a Square Span Program. Suppose we have a circuit with $n_{stmt}$ statement inputs, $n_{wit}$ witness inputs and $m$ wires.

We have a monic polynomial $t(\cdot)$
and collections of degree $m$ polynomials
$\{u_{stmt, i}(\cdot)\}_{i \in [n_{stmt}]}$, and $\{u_{wit,i}(\cdot)\}_{i \in [n_{wit}]}$,

and we say a pair of vectors $\{a_{stmt, i}\}_{i \in [n_{stmt}]}$, and $\{a_{wit,i}\}_{i \in [n_{wit}]}$ satisfy the Square Span Program if

$$ \left( \sum a_i u_i(X) \right)^2 - 1 \equiv 0 \pmod{t(X)} $$

We can reduce any circuit as described above to this framework in a similar way to how this would be done with a QAP or R1CS.

--------

## Primer on Baby SNARK - Prover

$$ \tau, \beta, \gamma \xleftarrow{\$}  \mathbb{F} $$
The CRS for a Baby SNARK instance consists of $m + n_{wit} + 2$ elements:
$$ \mathsf{CRS} := 1, \tau, \dots, \tau^m, \gamma, \gamma\beta, \beta u_{0, wit}(\tau), \dots, \beta u_{n_{wit}, wit}(\tau)  $$

The prover computes (in the exponent) the following as the proof:

$$ H := \left( \left(\sum_{i \in [n_{stmt}] \cup [n_{wit}]} a_i u_i(\tau) \right)^2 -1 \right)/t(\tau) $$
$$ V_{wit} := \sum_{i \in [n_{wit}]} a_i u_i(\tau) $$
$$ B_{wit} := \sum_{i \in [n_{wit}]} a_i \beta u_i(\tau) $$

--------

## Primer on Baby SNARK - Verifier

The Verifier computes

$$ V := V_{wit} + \sum_{i \in [n_{stmt}]} a_i u_i(\tau) $$

And then verifies, via pairing function $e$

$$ e(H, t(\tau)) + e(1, 1) = e(V, V) $$
$$ e(B_{wit}, \gamma) = e(\gamma \beta, V_{wit} ) $$

--------

## What are the givens in the main theorem, and what is the goal?

In the AGM model we assume the proof elements are some linear combination of the CRS elements, and that the prover knows the coefficients of this linear combination. To prove knowledge soundness, we must extract from these coefficients a satisfying witness assignment.
 <!-- the proof elements in terms of a linear combination of the CRS elements (represented as `mv_polynomial vars F` in Lean, with coefficients in `F`).
 -->
<!-- We assume the equations that the verifier checks hold. -->

To do this, we assume the equations that the verifier checks hold. We then prove a series of facts about the coefficients, culminating in the fact that a particular set of the coefficients satisfy the Square Span Program.

From this, it follows that any algebraic adversary cannot produce a valid proof without knowing a satisfying witness.

<!-- A critical point - the proof of the main theorem is designed so that you can read the paper side-by-side with the code -->

--------

## How you can contribute?

* We have a big spreadsheet of SNARKs that this framework could cover - come help us implement them!

* Help us develop tactics and structures to make the formalization process easier.

* Use the framework to systematically explore the space of possible SNARKs.

<!-- Compile from project home directory with `pandoc presentation/presentation.md -t beamer -o presentation/presentation.pdf` -->