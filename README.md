
# Linear PCP SNARKs in Lean

This is an old repository associated with [this paper](https://www.usenix.org/system/files/usenixsecurity24-bailey.pdf).

This project didn't fully make the transition to Lean 4 at the time the rest of the ecosystem did. 
With Claude Fable available again, I've used it to restore the project to a building state.

Here are some next steps that I'd like to accomplish if I have time:

- [x] Reengineer all polynomials to use the computable polynomial framework. (All definitions — models, SNARKs, transformations — are stated over CompPoly's `CPolynomial`/`COrdMvPolynomial`, the sparse multivariate representation over ordered variable types; the soundness proofs transport to mathlib polynomials internally where mathlib-side lemmas are needed.)
- [x] Reformulate the core soundness proving tactic into a computable non-meta function that analyzes a straightforward Linear PCP SNARK scheme and decides boolean true/false if it is sound, (and/or at least outputs the core ideal membership test problem(s)). (The problems are output by `SymbolicAGMScheme.soundnessProblem` and the per-SNARK `Symbolic.lean` files; `IdealMembershipProblem.decideMembership` decides them by a fuelled grevlex Buchberger certificate search whose `true` answers are re-checked by a *verified* certificate checker — see `Models/IdealMembershipDecision.lean` and its demo. `false` only means "no certificate found within the fuel".)
- [ ] Hook up [Lean-SMT](https://github.com/ufmg-smite/lean-smt) or another tactic to resolve these membership tests. 
  - [ ] This will require bumping Lean-SMT to a new toolchain. (Update seems like this happened!)
  - [ ] Formulate the Grobner basis problem instances for all of the SNARKs into a standard SMT format for benchmarking purposes.
- [ ] Introduce different models for Type I and Type III groups (Type II as well?) and duplicate SNARKs to prove sound in each model where soundness holds.
- [ ] Add VCVio/ArkLib to deps. Express the SNARKs in the AGM model from those libraries (partial work in `arklib-models`).