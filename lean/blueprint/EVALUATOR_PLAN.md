# A plan for the remaining construction, `PackedScalarPrograms`

> Historical review of the incoming archive. The evaluator has since been proved, built and audited. See the current project README and `DiophantineNP/EvaluatorPremises.lean`.

This note is about the one obligation that is internal to the manuscript: the fixed evaluator of §3.5. It is a plan with tested mathematics. It is not a proof, and no Lean in this folder has been compiled.

| File | What it is |
| --- | --- |
| `EVALUATOR_PLAN.md` | This plan. |
| `reference_evaluator.py` | An executable model of the plan. It mirrors the Lean definitions and compares the proposed evaluator with brute-force Laurent expansions. Run it with `python blueprint/reference_evaluator.py`. |
| `Evaluator.lean` | The same plan as Lean definitions and statements. 28 statements end in `sorry`. Never compiled. |

## The target

`Corollary.lean` asks, for every formula `φ`, for two fixed integer terms `num` and `den` over the inputs `U, t₁, …, t_k` such that

1. `den` is positive on every valid input,
2. the largest bit length of any intermediate value is at most `(1+U)^c`,
3. `num / den = packedScalar φ t`, where `packedScalar φ t = scalarAtOne (packedExpr φ t)`.

A term is a tree of binary operations. The project certifies three kinds of operation: any fixed bivariate integer polynomial (`ofPolynomial`), floor division by a positive integer (`divisionOperation`), and a power `a ^ b` (`signedPower`). The last one takes the two curve hypotheses `Cyclic` and `Quadratic`, so a proof of the target has the shape `Cyclic → Quadratic → PackedScalarPrograms`.

## Three observations

### 1. The size bound is syntactic

Clause 2 looks like it needs an estimate for every number the evaluator produces. It does not. Split terms into two classes by the operations they use.

- **Small** terms are built from inputs and literals with `+`, `-`, `*`, positive division and `log2`. Their *values* stay polynomial in the inputs.
- **Tame** terms are Small terms, or `+`, `-`, `*`, positive division applied to Tame terms, or a power whose base is Tame and whose exponent is Small. Their *bit lengths* stay polynomial in the inputs.

Both claims are short structural inductions (`SmallTerm.bound`, `TameTerm.peak_le`). The second uses that `a ^ n` has at most `n · bits(a) + 1` bits and that `n` is a Small value.

Every exponent in the evaluator below is Small: threshold degrees, strides, the period, the radius bound, the shift `b`, and `size^4` in the Wallis constant. So the evaluator is Tame by construction and clause 2 follows from one generic lemma. `reference_evaluator.py` builds the actual program for three sample formulas and confirms that it is Tame.

### 2. One integer per node

For an expression `e` in `d` coordinates and a point `x` with positive integer coordinates, write `X = ∏ xᵢ`, and let `(D, H̃, G̃) = evalBounds e`. `D` is the denominator of `Expr.bounds`. `H̃` and `G̃` are over-estimates of its height and radius, chosen so that they need no `max` and no absolute value (for example `p² + 1` instead of `max 1 |p|`, and `G̃_f + G̃_g` instead of `max G_f G_g`). The evaluator computes the integer

    clearedNum e x = X^G̃ · rawValue e.expand x,     so that     exprValue e x = clearedNum e x / (X^G̃ · D).

| Node | `clearedNum` at `x` |
| --- | --- |
| `scalar p q` | `p` |
| `monomial v` | `∏ xᵢ^(G̃ + vᵢ)` with `G̃ = ∑ |vᵢ|` |
| `geometric j s J` | `∏_{i≠j} xᵢ^(J·s) · geomSum(x_j^s, J)`, where `geomSum(y, J) = ∑_{i<J} 2^i y^(J-i)` |
| `neg f` | `-N_f` |
| `add f g` | `D_g · X^G̃_g · N_f + D_f · X^G̃_f · N_g` |
| `mul f g` | `N_f · N_g` |
| `pow f n` | `N_f ^ n` |
| `threshold f n k` | `tailNumerator (A + N_f) (A - N_f) n k` with `A = X^G̃_f · D_f` |
| `project f j m` | `extractCoefficient (v · (z^(m·n) - 1)/(z^m - 1)) z (2b)` with `b = shiftBound G̃ m`, `z = radix x 1 H̃ G̃ b`, `n = 2b/m + 1` and `v = x_j^G̃ · z^(b-G̃) · N_f(x[j := z])` |

`N_f` is `clearedNum f x`. The projection row is `scalarRecipe` with `p = x`, `q = 1`. It makes one recursive call, at the radix `z`. At the point `(1, …, 1)` the clearing factor disappears and `scalarAtOne e = clearedNum e 1 / D`.

No clause branches. `positiveDiv t t` is the indicator of `0 < t`, which gives `|a| = a·(2·[a>0] - 1)` for the radix inside `tailNumerator`, `max G 1 - 1 = G - [G>0]` for `shiftBound`, and the case `y = 2` of the geometric sum.

The correctness statement is `clearedNum_spec`. Its proof is an induction on `e` for all `x`, and each case is a lemma the project already has:

| Case | Existing result |
| --- | --- |
| `add`, `neg` | `Raw.evaluate_plus`, `Raw.evaluate_scale` |
| `mul`, `pow` | `Raw.evaluate_mul`, `Raw.evaluate_pow` |
| `threshold` | `Raw.evaluate_tail`, `TailRadix.tailNumerator_eq` (needs `k ≤ n+1`, true for every threshold of `packedExpr`) |
| `project` | `ScalarProjection.scalarRecipe_raw` with `Raw.Safe` at the over-estimates, and the induction hypothesis at `Function.update x j z` |

### 3. Leaves in lowest terms would need gcds

`FormulaLeaves.rational q` stores `q.num` and `q.den`. A leaf such as `-(size U) / (2 · piRational (size U ^ 4))` is in lowest terms in `packedExpr`, and its denominator enters `Expr.bounds`. An evaluator that reproduces `packedExpr` node for node would have to compute gcds of numbers like `16^(size^4)`.

It does not have to. Replacing a scalar leaf by an equal fraction changes `Expr.bounds` and leaves every value unchanged, including through cyclic projections. `ScalarEquiv` states this, and its proof is an induction with `Expr.evaluate_add`, `Expr.evaluate_mul`, `Expr.evaluate_pow`, `Expr.evaluate_threshold` and `gridChar_project`. The evaluator then works on an expression `e'` with unreduced leaves, and `scalarAtOne e' = scalarAtOne (packedExpr φ t)`.

## Work packages

Sizes are estimates for Lean 4 with mathlib.

| | Package | Depends on | Lines |
| --- | --- | --- | --- |
| R1 | Growth classes for the three existing operations; a `log2` operation built with `Operation.ofShortFormula` on the model of `signedPower` | — | 250 |
| R2 | `SmallTerm`, `TameTerm`, `TameTerm.peak_le`, `peak_poly_of_tame` | R1 | 200 |
| R3 | `evalBounds`, `clearedNum`, `geomSum_closed`, `clearedNum_spec` | — | 450 |
| R4 | `ScalarEquiv` and `scalarAtOne_eq` | — | 120 |
| R5 | `Evaluated` and its nine closure operations (terms, `run` lemmas, Tame proofs) | R1–R3 | 600 |
| R6 | Parameter terms and the assembly along `packedExpr` | R4, R5 | 500 |

R3 is the mathematical core and is independent of terms, so it can be done first. R2 is independent of everything about Laurent expressions.

Parameter terms for R6, valid for `U ≥ 1` (all checked against the Lean definitions for 43 values of `U`):

- `radius U = max 2 U = U + positiveDiv 1 U`
- `J U = 2·radius + 1`, `stride U = 4·(2·radius + 2)^30`, `size U = J · stride`
- `precision U` and `halfDegree U` need `(size U).log2`, hence the new operation in R1
- `Nat.choose (2n) n = ((1+R)^(2n) / R^n) mod R` with `R = 2^(2n+1)` (`TailRadix.choose_from_power`), and `piRational n = 16^n / (n · choose²)` as an unreduced pair
- the majority threshold `U/2` is `positiveDiv U 2`

## What the reference model checks

`python blueprint/reference_evaluator.py` takes about 80 seconds (`--quick`: 8 seconds). Last run:

| Check | Result |
| --- | --- |
| `evalBounds` has the denominator of `Expr.bounds` and larger height and radius | 3000 random expressions |
| Lean's `scalarRecipe`, transcribed with rationals and floor, equals the cyclic projection, with `Expr.bounds` and with the over-estimates | 300 random cases at rational points, up to 360 Laurent terms |
| `clearedNum e x = X^G̃ · rawValue e.expand x`, and `|clearedNum e x| ≤ H̃ · X^(2G̃)` | 1500 random expressions over all nine constructors. 922 contain projections, 238 of them nested, and in 593 a projection removes some terms and keeps others. Up to 86 nodes, sub-expansions up to 353 terms, intermediate values up to 825,710 bits |
| Unreduced scalar leaves leave `exprValue` unchanged | 600 random expressions, 471 with different bounds |
| Parameter terms equal the Lean definitions | 43 values of `U` up to 10⁶ |
| One fixed program evaluates a toy family with `U`-dependent scalars, exponents, threshold degrees and two nested projections | every `(U, t)` with `U ≤ 6`, plus `U = 8, 10`; brute force for `U ≤ 4` |
| Peak bit length of that program | grows like `(1+U)^4.3` between `U = 5` and `U = 10` |
| The program for the real `packedExpr` is Tame | three formulas, about 2,500 to 3,500 operations each |

The random expressions are small: the median has 17 nodes, and the median widest sub-expansion has 4 Laurent terms. They exercise every recurrence and its degenerate cases (degree 0, empty threshold, empty geometric sum, period 1, coordinate 1, the case `y = 2`). They are not a substitute for the proof.

The model cannot run the real program. `piRational (size U ^ 4)` contains `16^(size^4)`, and `size 1` is already about `4.4 · 10^24`. The bound is polynomial in `U` with constants of that kind.

## Things to know before starting

- **Terms are trees.** `ScalarProgram.Term` has no sharing. The program for `MAJ x (x < j)` has about 2,500 distinct operations and about `10^17` nodes as a tree, because every nested projection copies its radix. That is a fixed number, so the statement is unaffected, but the final polynomial has that many witness slots. A `let` constructor for `Term` would bring it back to thousands.
- **The curve hypotheses spread.** Every closure operation that raises to a power takes `Cyclic` and `Quadratic`. The final theorem then lists them next to the three literature inputs. `Premises.lean` states the dependency in that form.
- **`tailNumerator_eq` has a side condition** `k ≤ d+1`. The plan carries it as `WellFormed`.
- **`scalarRecipe` fixes its shift** to `shiftBound G m`. An evaluator must use exactly that `b`, or re-prove the recipe for another multiple of `m`.
- **Divisors are positive wherever the program divides**: `2·z^k`, `z - 1`, `z^m - 1` with `z ≥ 5`. `positiveDiv` then agrees with Lean's integer division.

## What this plan does not change

A complete `PackedScalarPrograms` would remove one of the premises of `classEquality_of_packedScalarSystems` and replace it by the two curve facts. The class equality would still rest on `LiteratureFormulas`, `JonesMatiyasevichDirection` and `PolynomialEvaluationInP`, which are stated in this project and proved elsewhere or not at all. Because the conclusion is D = NP, each of them should be checked against its source by someone other than the author of the formalization.
