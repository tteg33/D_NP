# Review notes, 26 November 2026

> Historical review of the incoming archive. The evaluator, curve rank and two machine compilers have since been proved, built and audited. See `README.md`, `HAB_REVIEW.md` and `DiophantineNP/HABCriterion.lean` for the current status.

## Scope and method

The request was to improve the Lean code. The review environment had no Lean toolchain and no network access, so **nothing in this archive was compiled during the review**. For that reason the 77 library modules were not edited: they are byte-identical to the archive that was reviewed, and the README's statement that the pinned build passes could not be confirmed or refuted here.

What was done instead:

- every check that needs only the source text (results below);
- a hardened `verify.py`, tested without Lean;
- two new Lean files kept outside the build, because they are unchecked;
- a plan for the open construction `PackedScalarPrograms`, with an executable model that tests its mathematics against brute-force expansions.

## What changed

| Path | Status |
| --- | --- |
| `DiophantineNP/*.lean` (77 files), `DiophantineNP.lean`, `Audit.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `manuscript/` | Unchanged. `python verify.py --static-only` prints the source digest `a7a4c1a8b706d3d1` for the modules. |
| `verify.py` | Rewritten. The default run executes the same three Lake commands as before, after a preflight. New options: `--static-only`, `--strict`, `--extras`. |
| `Premises.lean` | New, not compiled, outside the build. Bundles the external inputs, states the final dependency with the two curve hypotheses included, and prints every premise. |
| `blueprint/EVALUATOR_PLAN.md` | New. The plan for `PackedScalarPrograms`. |
| `blueprint/reference_evaluator.py` | New. Tests of that plan. All pass. |
| `blueprint/Evaluator.lean` | New, not compiled, outside the build. The plan as Lean definitions and 28 statements ending in `sorry`. |
| `README.md` | One section added at the end. |

## Findings

### Checks on the source text

- The root file imports all 77 modules. This matters because `lake build` and `Audit.lean` see only imported modules; a forgotten module would be silently unchecked. The new preflight enforces it.
- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by` or `extern` outside comments. Three proofs use `decide +kernel`, which is checked by the kernel.
- Four option overrides: `maxRecDepth 3000` (`ConcreteGrid.lean`), `maxHeartbeats 600000` (`FormulaCompiler.lean`), `maxHeartbeats 1600000` on the structure `Observed` (`Observation.lean`), `exponentiation.threshold 1024` (`IntegerPower.lean`).
- `lakefile.toml` sets no `leanOptions`, so `autoImplicit` has Lean's default. A heuristic scan of all declaration signatures found no identifier that looks auto-bound. `python verify.py --strict` settles it with the compiler.
- The toolchain file, the lakefile and the manifest agree on Lean 4.24.0 and mathlib `f897ebcf72cd`.

### The statement layer

1. **The premise list of the final theorem will grow by two.** `classEquality_of_packedScalarSystems` has four premises. The first, `PackedScalarSystems`, can only be discharged with the power operation `signedPower`, which takes `Cyclic` and `Quadratic`. The complete list is one internal obligation and five external inputs. `Premises.lean` states it that way.
2. **The open obligation is the step the manuscript asserts in §3.5**: one fixed evaluator and a polynomial bound on all its intermediate values. Given that evaluator and the three literature formulas, the library states a derivation of Theorem 1.1 (`nativeVerifier_of_packedScalarSystems`). I read the statements along that chain, not every proof, and could not compile them.
3. **`rational q` stores fractions in lowest terms.** An evaluator that reproduces `packedExpr` literally needs gcds of very large numbers. The plan avoids this with an equivalence on expressions (`ScalarEquiv`).
4. **`precision` and `halfDegree` contain `(size U).log2`.** No existing scalar operation computes it. One new operation is needed, built like `signedPower`.
5. **`ScalarProgram.Term` is a tree without sharing.** The fixed program for the smallest sample formula has about 2,500 distinct operations and about 10^17 tree nodes. The statement is unaffected. The number of witness slots of the final polynomial is.
6. **The size clause is easier than it looks.** It follows from which operations the terms use, not from estimates of the computed numbers. See observation 1 of the plan.
7. **The evaluator's toolkit is not used by anything yet.** Eight modules are imported only by the root file. Four of them are the ingredients of the missing evaluator: `ScalarSignedPower`, `ScalarDivision`, `ScalarProjection` and `TailRadix`. `Corollary.lean` does not depend on Appendix A at all, which is the same gap seen from the import graph.

### The literature inputs against the supplied sources

I compared the Lean hypotheses with the pinpoints in the reference bundle.

| Lean hypothesis | Source checked | Result |
| --- | --- | --- |
| `LiteratureFormulas.nativeBit` | Libkin, Theorem 6.12 and Corollary 6.15 | The source states that BIT is definable from addition and multiplication. Matches the atoms `eqv`, `leq`, `add`, `mul`. |
| `LiteratureFormulas.product` | Hesse, Allender and Barrington, §2.3 and Corollary 6.3 | The logic matches: universe `0..n-1`, a majority quantifier over one variable that is true for more than half the values, and a binary relation for the `n` input numbers. The Lean template asks only for the low `U` output bits, which is a special case. |
| `LiteratureFormulas.sum` | Same paper | Iterated addition is mentioned there as known and is not one of its numbered results. A direct citation would be better. |
| `JonesMatiyasevichDirection` | Lipmaa, page 11 | Lipmaa reports the criterion in the form the Lean hypothesis uses. The 1984 paper itself is not in the bundle, so the model of computation and the witness bound in the original were not compared. |
| `Quadratic` | Silverman, Theorem VIII.9.3(b) | Matches. The project's height differs from Silverman's by a constant factor, which does not affect the statement. |
| `Cyclic` | Cremona, Table 2; LMFDB 37.a1 | Rank 1, trivial torsion and the generator `(0,0)` are as tabulated. |

Pollett's PDF has no usable text layer and was not checked. `PolynomialEvaluationInP` is a standard fact about Turing machines. I know of no formal proof of it, in mathlib or elsewhere, so it needs one or a precise citation.

Each Lean hypothesis also quantifies over every universe size, including very small ones. The sources work with arbitrary `n`, and a fixed formula can treat finitely many sizes separately, but none of that is written down in the project.

### Suggestions that need a compiler

- Add `[leanOptions] autoImplicit = false` to `lakefile.toml` once `--strict` passes.
- Once `Premises.lean` compiles, move it to `DiophantineNP/Premises.lean`, importing `DiophantineNP.Corollary` and `DiophantineNP.PowerTests`, add it to the root file, and let `Audit.lean` print the axioms of `classEquality_of_evaluator`.
- Merge duplicated private helpers into one small module: `bits_mono` (`NaturalBridge`, `PowerPolynomial`), the three versions of "`x ≤ 2^k` gives `bits x ≤ k+1`" (`PowerPolynomial.bits_of_mag`, `RadixGrowth.bits_of_bound`, `ModularVerifier.bits_le`), `table_eval` and `table_mass` (`TailRadix`, `ScalarProjection`), and `single_cost` / `bit_le_cost` (`ScalarCertified`, `ScalarSystems`).
- 124 lines are longer than 100 characters, and roughly two in five public declarations have a docstring.

## How to check this archive

```sh
python verify.py --static-only      # no Lean needed
python blueprint/reference_evaluator.py
python verify.py                    # preflight, mathlib cache, build, axiom audit
python verify.py --strict --extras  # autoImplicit off; Premises.lean; the blueprint
```

If `--extras` reports errors in `Premises.lean` or `blueprint/Evaluator.lean`, the verified library is unaffected: those two files were written without a compiler.
