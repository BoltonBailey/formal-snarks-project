
# inear PCP SNARKs in Lean

This is an old repository associated with [this paper](https://www.usenix.org/system/files/usenixsecurity24-bailey.pdf).

This project didn't fully make the transistion to Lean 4 at the time the rest of the ecosystem did. 
With Claude Fable available again, I've used it to restore the project to a building state.

Here are some next steps that I'd like to accomplish if I have time

- [ ] Reengineer all polynomials to use the computable polynomial framework (partially done).
- [ ] Reformulate the core soundness proving tactic into a computable non-meta function that analyses a straightforward Linear PCP SNARK scheme and decides if it is sound, (or at least outputs the core ideal membership test problem(s)).
- [ ] Hook up Lean SMT or another tactic to resolve these membership tests. 
  - [ ] Formulate the Grobner basis problem instances for all of the SNARKs into a standard SMT format for benchmarking purposes.