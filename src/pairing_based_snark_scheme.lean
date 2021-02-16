
import data.mv_polynomial.basic

section

/-!

This file should contain a general scheme for pairing based SNARKs in the sense of 

What are the toxic waste elements?
What are the CRS elements?
What are the proof elements?
What equalities does the verification/the crs process enforce?

Does all this express in full generality the possibilities for a Pairing Based SNARK?

Should the scheme include the QAP as arguments, or should there be a separate function?

-/

--  TODO is a structure correct here, or a dependent tuple?

structure pairing_based_snark_scheme (F : Type) [field F] (toxic : Type) (crs_size : ℕ) (crs : fin crs_size -> mv_polynomial toxic F) (prove : sorry)