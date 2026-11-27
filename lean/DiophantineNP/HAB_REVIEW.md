# Verifying Corollary 6.3 and its use in the draft

The published Corollary 6.3 puts division and iterated multiplication in first-order logic with majority. The closed theorem `DiophantineNP.HAB.corollary63` in `DiophantineNP/HABCorollary63.lean` expresses both conclusions in the project’s finite logic. The application to bounded Diophantine languages appears in `DiophantineNP/HABVerified.lean`. [Hesse, Allender and Barrington, *Uniform Constant-Depth Threshold Circuits for Division and Iterated Multiplication*, Corollary 6.3](https://people.cs.rutgers.edu/~allender/papers/division.pdf)

## Check the finite-logic theorem on its own

From the directory containing `lakefile.toml`, build the theorem and inspect its statement and axiom dependencies.

```sh
lake build DiophantineNP.HABCorollary63
lake env lean --stdin <<'LEAN'
import DiophantineNP.HABCorollary63

#print DiophantineNP.HAB.Corollary63
#print DiophantineNP.HAB.DivisionInFOM
#print DiophantineNP.HAB.ImultInFOM
#print axioms DiophantineNP.HAB.corollary63
LEAN
```

## Compare the statements

| Question for a verifier | What to inspect |
| --- | --- |
| Does the finite logic match the paper? | `HAB.Form` and `Form.Holds` in `HABTranslation.lean` give equality, linear order, position-first BIT, an input relation, and ordinary quantification plus strict unary majority. The same finite syntax tree works for every universe. `HAB.toSource_correct` eliminates the auxiliary bounded arithmetic atoms. |
| Are the inputs and all possible output bits represented? | A relation on $[U]^2$ encodes $U$ words of $U$ bits each, least significant bit first. The pair $(h,l)$ queries position $hU+l$ for every $h,l<U$. For division the first two rows encode the dividend and divisor. Every $U\ge2$ is covered. The division formula also returns zero on a zero divisor, following Lean’s natural-number division convention. |
| Could a change of universe alter majority or the product? | `HABPairInterpretation.compile_correct` proves preservation of BIT and majority over pairs, including ties and odd sizes. `HABWideOutput.source_correct` interprets the polynomially larger workspace within the base universe and gives each added row the multiplicative identity. The draft’s low-bit interface handles sizes zero and one in `HAB.productTemplate_of_imult`. |
| Does the draft use precisely this result? | `HAB.corollary63_iff_productTemplate` proves both directions. `classEquality_of_hab` supplies the connection to the verifier and both complexity inclusions. `HAB.imultInFOM` in `HABCorollary63.lean` supplies its product formula. |

## Follow the proof without assuming the answer

1. **Start with the short primes and independent addition.** `HABIndependentSum.formula_correct` computes the low $U$ bits of a sum of $U$ arbitrary input words, including the carry between blocks. `HABProductBlocks.binaryProduct_spec` computes the residue of the full product using packed short modular powers. `HABPolylogRange.block_covered` supplies a sufficiently large family of such primes for the smaller calculations.
2. **Recover a binary answer on that smaller scale.** The modules `HABCRTExtend`, `HABCRTQuotient`, `HABCRTNumerator`, `HABCRTEstimate` and `HABCRTBitDecision` implement basis extension, division by an auxiliary product of primes, and the corrected bit decision. `HABPolylogProduct.formula_correct` proves that for every fixed $d$ one formula computes the bits of the product whenever its value is below $2^{(\lfloor\log_2 U\rfloor)^d}$, for sufficiently large $U$.
3. **Derive modular powering at the larger scale.** Local bounds for geometric-series division and step 2 supply the actual term `HABModularArithmetic.shortProducts`. The group-power argument in `HABPowerReduction` then yields a single majority formula for $a^r\equiv b\pmod p$ at every represented prime. The theorem here is in the logic with majority required by Corollary 6.3. The paper also proves a stronger auxiliary result about powering in ordinary first-order logic. [HAB, §6](https://people.cs.rutgers.edu/~allender/papers/division.pdf)
4. **Run the unrestricted readout.** `HABLargePrimeProduct.source_correct` computes the product of all raw rows at an arbitrary represented prime. `HABWideBitDecision.localSpec` computes the binary digit from these residues. `HABWideOutput.imult_of_local` proves the concrete prime, precision and address bounds needed at every original width.
5. **Produce the quotient bits.** `HABGeometricDivision.division_in_FOM_of_imult` constructs the finite division formula using a geometric-series approximation, an exact right shift and one correction. `HABDivisionGraph.formula_correct` independently validates a supplied quotient using a widened product and comparison.

A concrete obstruction explains why the proof uses two scales. `HABProductBlocks.padded_short_prime_collision` gives distinct positive $U$-bit values agreeing at every prime admitted by the original packed-power condition, even after any fixed polynomial enlargement for sufficiently large $U$. Computing the smaller binary products first supplies the stronger modular-power operation needed to separate the larger inputs.

For a manuscript review, also compare `Classes.D`, `Classes.NP` and `NativeVerifier` with the statements intended in the draft. These specify binary inputs, natural or signed witnesses as appropriate, and the distinctions between unrestricted and bounded soundness. `CoordinateClass.lean` proves that the total-bit bound, the per-coordinate bit bound, and the inclusive numerical bound give the same class. The last convention is Pollett’s on positive inputs. The project includes input zero and assigns it length one. [Pollett, introduction](https://www.cs.sjsu.edu/faculty/pollett/papers/hilbert10.pdf)

## An alternative modulus for the draft’s readout

`BinomialModulus.native_readout` constructs a valid alternative CRT modulus from a power of a central binomial coefficient. `modulus_closed` expresses that modulus using integer powers, division and remainder, and `modulus_bound` bounds its bit length. The corresponding multiplier and scale must still be produced uniformly to replace the general product theorem. This is a separate potential route. The closed theorem `classEquality` uses the original width construction.
