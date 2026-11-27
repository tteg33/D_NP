# Native bitwise inclusion and Diophantine complexity

This Lean 4 project formalizes the draft *A fixed Diophantine verifier for native binary bitwise inclusion*. Start with `DiophantineNP/HABVerified.lean` for the closed native polynomial and class-equality theorems. Its iterated-multiplication input is proved in `DiophantineNP/HABCorollary63.lean`, which also proves both parts of Hesse–Allender–Barrington Corollary 6.3. The project pins Lean 4.24.0 and mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The `manuscript/` directory contains the submitted TeX and the revised manuscript in TeX and PDF.

To rebuild the revised PDF with pdfLaTeX, run the following inside `manuscript/`. The environment values reproduce the release metadata with the pdfTeX version recorded in the [PDF build log](verification/logs/pdf-build.log).

```sh
export TZ=UTC SOURCE_DATE_EPOCH=1795737600 FORCE_SOURCE_DATE=1
for pass in 1 2 3; do
  pdflatex -halt-on-error -interaction=nonstopmode Native_Bitwise_Inclusion_Revised.tex || exit 1
done
```

## What Lean proves about the main claim

For natural numbers $a,b$, `BitIncl a b` means that every set bit of $a$ is a set bit of $b$. `NativeVerifier` is the exact target of Theorem 1.1. One polynomial and one finite number of signed witnesses must work for **every** input width. Each true input has a short root. Every root, regardless of its length, must give a true input.

1. **With the three correct width values supplied**, Lean constructs a specific integer polynomial with five input slots and 17 natural witness slots. Its inputs are $(a,b,D_n,J_n,2^{n+2})$. A zero of any size implies bitwise inclusion. Every true pair of width $n$ has a witness of total length at most $17(40(n+2)^3+7)$ bits. There is also a signed version with 68 witness slots. `ModularVerifier.lean` proves these statements for the actual prime powers of the paper.
2. **To remove the three extra inputs**, `Assembly.lean` builds a single polynomial for the width checks and the modular check, using disjoint auxiliary variables. If the width checks have short, globally sound graphs, it proves `NativeVerifier`. It counts every auxiliary coordinate. The guessed width can be larger than the actual width on a dishonest assignment.
3. **The route from finite arithmetic to those width graphs is explicit.** Lean constructs the formulas for the odd primes, their powers, the products with one factor omitted, the bit shifts, and the final sum. Lean constructs BIT and iterated sum from the available finite arithmetic, using a uniform iterated-product template constructed by the finite-model proof. The BIT construction uses only the elementary arithmetic atoms and unary majority. An independent construction in `HABIndependentSum.lean` also proves iterated addition directly from majority, with no product premise. `WidthFormulaSubstitution.lean` verifies substitution under quantifiers. `PackingBridge.lean` and `ScaleFormula.lean` prove how the paper's packing theorem turns those formulas into exact polynomial graphs for all three width values.
4. **The complexity corollary** uses a signed-to-natural polynomial substitution. The positive and negative parts together have exactly the bit cost charged to their signed input. `Classes.lean` defines numerical languages, fixed-polynomial bounded membership, and a finite-alphabet Turing-machine verifier for NP. The current proof compiles bounded register traces directly into one polynomial using a fixed number of bit masks. A complete finite-stack evaluator decides equality of every fixed signed polynomial on the framed TM2 encoding.

### Size of the explicit construction

For the width-one case, the first Wallis extraction forms an integer of approximately $3.94\times 10^{2446}$ bits. The explicit HAB formula uses 1,992,018 padding iterations. Expanding the resulting formula and using the displayed unreduced threshold evaluator gives an exponent larger than $10^{599000}$ for that method. The theorem quantifies over a fixed polynomial and a fixed bound valid at every width. The estimates describe one construction. In the smaller five-input system above, the supplied width-one values are $D=4{,}782{,}969$, $J=597{,}871$ and $m=8$. The 17-coordinate root for $a=b=1$ has total cost 185 bits. [Checked example](review/WidthOne.lean)

## The verified evaluator

For every fixed counting formula, `Blueprint.packedScalarPrograms` produces two integer programs before the universe size or parameters are supplied. Their quotient equals the manuscript’s rational readout at every positive universe size. Both programs have polynomial peak bit length in the numerical universe size. Its original interface takes two curve hypotheses. The current proof supplies height quadraticity unconditionally and proves generation by the proposed point via explicit cubic-field descent.

`EvaluatorSemantics.lean` proves `clearedNum_spec` by structural induction at every positive integral evaluation point, including the replacement of one coordinate by a larger radix during cyclic projection. `EvaluatorNodes.lean` builds fixed terms for all nine expression constructors. `EvaluatorParameters.lean`, `EvaluatorFormula.lean` and `EvaluatorPacked.lean` assemble those terms for the actual formula and Fourier kernel. Equivalent rational leaves can use unreduced fractions. The existing strict one-quarter rounding theorem then determines the packed word. `HeightGenerator.lean` proves that the proposed elliptic generator has infinite order. `CurveHeightBridge.lean` identifies the height normalizations.

| Manuscript step | Verified result and where to read it |
| --- | --- |
| §2, correctness and size of the CRT readout | The actual odd primes are in the prescribed search range. The modulus fits the explicit cubic logarithmic bound. The CRT selects exactly the native bits and the ceiling reads the empty selection as zero. Start with `WidthData.lean`, `WidthFrame.lean` and `ModularVerifier.lean`. |
| §3.1–3.3, logic on a roots-of-unity grid | The Wallis constants, binomial threshold error, label and window estimates, and the guarded induction for existential and strict-majority quantifiers are checked. The truth predicate of any fixed formula has an actual rational Laurent expression. Its coefficient, denominator and exponent bounds are uniform over the numerical parameters. See `Wallis.lean`, `GridLogic.lean`, `FormulaOutput.lean` and `FormulaGrowth.lean`. |
| §3.4, recovering binary weights | The two frequency signs give the exact factor $8J$ in the ideal sum. The actual fourfold sum is within one quarter of the packed word. The four successive cyclic means of the rational Laurent expression have exactly this value. See `FourGridKernel.lean`, `FourGridReadout.lean`, `KernelEvaluation.lean` and `FormulaRounding.lean`. |
| §3.5, evaluating a cyclic mean | Signed radix extraction handles negative coefficients. The formalization gives the exact cyclic filter, signed threshold evaluation, denominator clearing and bounds on the radix at successive scalar calls. For the packed formula, the recursive integer program and its bit bound are both checked. See `ScalarProjection.lean`, `TailRadix.lean` and `RadixGrowth.lean`. |
| §4, compiling finite constraints | The polynomial compiler handles signs, inequalities, divisibility, finite conjunctions and disjunctions. For each fixed system the additional honest witnesses have total bit length at most a constant times the maximum input bit length plus a constant. `ScalarProgram.lean` also turns a fixed tree of integer operations into a single polynomial and proves that a polynomial bound on peak intermediate bit length suffices for a short full witness. See `Compiler.lean`, `ConstraintCost.lean` and `ScalarSignedPower.lean`. |
| Appendix A, powering | The development includes Pell descent, index selection, computations in the rational-point group of curve 37a1, duplication bounds, the canonical-height limit and the appendix's fixed power polynomial. With the rank of this curve now proved in Lean, it has 192 signed witness slots, unrestricted soundness, and a quartic bound on total witness bits. See `Curve37.lean`, `IntegerPower.lean` and `PowerPolynomial.lean`. |

### A concrete difficulty with exponentiation

The proof in mathlib that exponentiation is Diophantine uses a different Pell graph. Our theorem `MathlibPower.exponential_witness` proves a lower bound for **every** witness in its positive branch. On the family $g=2^N$, $e=1$, $y=g$, one auxiliary integer already requires at least $N2^N+1$ magnitude bits. The base, exponent and output together use only $O(N+1)$ bits. This explains why simply importing `Dioph.pow_dioph` cannot discharge the manuscript's short-witness requirement. The draft builds a different power polynomial using the elliptic-curve index bound in Appendix A.

For $E: y^2+y=x^3-x$, Lean proves the canonical-height parallelogram identity, quadratic scaling at every rational point, and that $P=(0,0)$ generates the rational point group. The proof identifies doubling with taking a square in a cubic field. It checks the ideal class number, prime-by-prime descent of rational points, and unit signatures under all three real embeddings. `Curve37.rank_one` gives the exact rank on mathlib’s rational-point type. See `CubicDescent.lean`, `CubicIntegralReduction.lean` and `RANK_REVIEW.md`.

## Run the checks

Install Git and Lean using the official Lean setup guide. The project selects its compiler version automatically. Python 3 is used only by the convenience script. [Install Lean](https://lean-lang.org/install/)

Extract the archive, open the folder that contains `lakefile.toml`, and run the following command. The first run downloads mathlib and its compiled dependencies.

```sh
python verify.py
```

On Windows, `py verify.py` also works with the Python launcher. With Lean and Lake set up, the equivalent manual checks are

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Open `DiophantineNP/HABVerified.lean` for the final statements. To read the two machine compilers independently, open `DiophantineNP/VerifiedCompilers.lean`. For the full check use the command below. It re-elaborates each module with automatic variable declaration disabled, audits transitive dependencies, tests the numerical examples and checks the standalone entry points.

```sh
python3 verify.py --strict --extras -j 3
```

The default project build sets `autoImplicit=false`. The following commands run the preflight tests and replay the safe, total project declarations against the pinned external imports. The checker verifies that none of the selected project declarations was already present when replay began. The full transcript and source digest for the packaged revision are in [VERIFICATION.txt](VERIFICATION.txt).

```sh
python3 tests/test_preflight.py
bash verification/replay.sh project
lake env lean -DautoImplicit=false review/CertificateTransducer.lean
```

For a replay starting from an empty kernel environment, run `bash verification/replay.sh fresh`. This also checks the imported dependency closure. The release logs identify which checks completed locally. GitHub Actions includes both modes, with transitive replay available on manual dispatch.

The two independently buildable review packages each contain just the required project proof sources, the exact toolchain and manifest, and a checked statement. [HAB63.zip](review/standalone/HAB63.zip) · [Rank37.zip](review/standalone/Rank37.zip)

To regenerate them, choose two new output paths and run

```sh
python3 review/export.py hab HAB63.zip
python3 review/export.py rank Rank37.zip
```

## Current theorem statements

| Declaration | Conclusion | Inputs |
| --- | --- | --- |
| `HAB.corollary63` | Fixed source formulas compute every requested bit of division and iterated multiplication. | None |
| `nativeVerifier` | One integer polynomial verifies native bitwise inclusion with short honest witnesses and unrestricted soundness. | None |
| `classEquality` | The bounded Diophantine and NP classes coincide for binary numerical languages. | None |
| `Classes.Clocked.languages_eq_NP` | The class defined by running an explicit time-bounded TM2 on framed tapes equals the verifier class. | None |
| `Classes.Clocked.binary_certificate_iff` | One binary word of length at most $2q(\ell(x))+r$ suffices for the original $r$-field witness, with exact preservation of the cutoff. | None |
| `Classes.d_subset_np` | Every bounded Diophantine language has a polynomial-time verifier on the framed binary tape. | None |
| `Classes.np_subset_d_of_native` | Every language in the project’s NP class has a bounded Diophantine representation. | A globally sound native bit-inclusion verifier with short honest roots |
| `classEquality_of_native` | The two numerical complexity classes are equal. | The same native verifier |
| `Curve37.rank_one` | The rational Mordell–Weil group of the curve has rank one. | None |
| `nativeVerifier_of_product` | The specific native bit-inclusion polynomial exists. | One uniform iterated-product formula |
| `classEquality_of_product` | The two numerical complexity classes are equal. | The same iterated-product formula |
| `classEquality_of_hab` | The two numerical complexity classes are equal. | The published iterated-multiplication result stated in the source logic, `HAB.ImultInFOM` |

`CoordinateClass.lean` proves that bounding total witness length, bounding each coordinate’s bit length, and imposing an inclusive numerical bound on each coordinate give the same class. A change in the numerical cutoff alone could admit a long root on a false input. The proof encodes the original cutoff inside the new polynomial equation. `classEquality_powerCutoff` gives the final equality using the inclusive convention. Pollett states that convention on positive inputs. This project also defines the language at zero, whose input length is taken to be one. [Pollett, introduction](https://www.cs.sjsu.edu/faculty/pollett/papers/hilbert10.pdf)

The clocked-machine comparison includes every raw tape. It proves a polynomial deadline in instance bit length alone on admissible certificates, including rejection. `BinaryCertificates.decode` rejects malformed witnesses. In `Clocked.acceptsWord`, decoding precedes the timed TM2 run. The separately checked transducer consumes the raw certificate, rejects malformed words, and supplies the exact framed witness tape. Its run takes at most one scanner transition per input bit plus one. The theorem `BinaryCertificates.combined_clock` bounds scanner transitions plus verifier fuel by a polynomial in the instance length on admissible words. Compiling those stages into one conventional machine and comparing with a separately defined nondeterministic Turing machine on arbitrary binary strings remain open. [Transducer and combined clock](review/CertificateTransducer.lean)

The declarations are in namespace `DiophantineNP`. The class `D` here concerns short Diophantine certificates for yes instances.

## The finite-model proof

`HAB.ImultInFOM` requires one formula for all universe sizes, all input matrices and all legal output positions. A matrix has $U$ rows of $U$ little-endian bits. A query $(h,l)$ selects bit $hU+l$ of their ordinary product. The proof constructs this formula and derives a quotient-bit formula for two full-width inputs. The grammar has order, BIT, a binary input relation, first-order quantification and strict unary majority. `HAB_REVIEW.md` traces the two stages of CRT recovery, the elimination of the modular-power assumption, and the connection to the draft. [Hesse–Allender–Barrington, §§2–6](https://people.cs.rutgers.edu/~allender/papers/division.pdf)

## Independent verification

1. Compare §2, §2.3 and Corollary 6.3 of Hesse–Allender–Barrington with `HAB.ImultInFOM` using `HAB_REVIEW.md`. Then read `Statement.lean`, `Classes.lean` and `CoordinateClass.lean` to check input types, bit costs and the quantifiers in the two numerical classes. A root of the native polynomial is required to be sound at every length.
2. For NP into D, follow `NativeComplexity.lean`, `RegisterNativeTrace.lean` and `TraceChecker.lean`. The proof keeps the original certificate cutoff, enforces endpoints and adjacent steps, and pays for every auxiliary word. It uses one polynomial for a fixed machine for every input. [1984 source of the related normal-form route](https://doi.org/10.2307/2274135)
3. For D into NP, follow `MachineCircuitAllocation.lean`, `MachineStackMultiply.lean` and `MachineFrameAdapter.lean`. The time bound is for actual TM2 transitions. The verifier halts on malformed inputs as well.
4. For the curve, compare `CurveKummer.lean`, `CubicIdeals.lean`, `CubicIntegralReduction.lean`, `CubicUnitSigns.lean` and `CubicDescent.lean`. The PARI and eclib calculations in `RANK_REVIEW.md` give independent checks of the value. The Lean theorem depends on neither computation.

`JONES_REVIEW.md` records the local correction to equation (49) in the 1984 paper. `REVIEW.md` and the files in `blueprint/` retain the earlier review and evaluator history.
