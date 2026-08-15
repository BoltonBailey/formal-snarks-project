
# Linear PCP SNARKs in Lean

This is an old repository associated with [this paper](https://www.usenix.org/system/files/usenixsecurity24-bailey.pdf).

This project didn't fully make the transition to Lean 4 at the time the rest of the ecosystem did. 
With Claude Fable available again, I've used it to restore the project to a building state.

Here are some next steps that I'd like to accomplish if I have time:

- [ ] Hook up [Lean-SMT](https://github.com/ufmg-smite/lean-smt) or another tactic to resolve these membership tests. 
  - [x] This will require bumping Lean-SMT to a new toolchain. (Update seems like this happened!)
  - [x] Formulate the Grobner basis problem instances for all of the SNARKs into a standard SMT format for benchmarking purposes.
- [ ] Introduce different models for Type I and Type III groups (Type II as well?) and duplicate SNARKs to prove sound in each model where soundness holds.
- [ ] Add VCVio/ArkLib to deps. Express the SNARKs in the AGM model from those libraries (partial work in `arklib-models`).