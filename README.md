
This is an old repository associated with [this paper](https://www.usenix.org/system/files/usenixsecurity24-bailey.pdf).

Unfortunately, in the Lean3->Lean4 upgrade and changes to the grobner basis tactic, this project never was fully upgraded. 

Here are some next steps that I'd like to accomplish if I have time

- Reengineer all polynomials to use the computable polynomial framework.
- [ ] Reformulate the core soundness proving tactic into a computable non-meta function that analyses a strightforward Linear PCP SNARK and decides if it is sound, or at least outputs the core grobner basis problem(s).
- [ ] Hook up Lean SMT or another tactic to resolve the 
  - [ ] Formulate the Grobner basis problem instances for all of the SNARKs into standard SMT benchmark format.