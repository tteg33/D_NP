# Checking the Jones–Matiyasevich step

Jones and Matiyasevich give the relevant NP characterization in §5, equation (53), p. 827. The fact to transfer to this project is the direction from an accepting polynomial-time computation to a particular bounded numerical representation. The paper's introductory theorem about enumerable sets has a different computational bound. [Published article, pp. 818–829](https://doi.org/10.2307/2274135)

The current end-to-end proof in `NativeComplexity.lean` compiles as many bit masks as the fixed verifier needs into one polynomial. It preserves the original NP certificate cutoff. The older route through the exact one-mask syntax of (53) is documented here to make the source comparison and local correction reviewable.

## The bound in (53)

The input and witnesses are naturals. The source's length is the least integer at least $\log_2(x+1)$, which is `Nat.size x` and gives zero at zero. A fixed integer polynomial $P$ bounds the length of **each** guessed integer separately and inclusively. The other conditions are bitwise inclusion between the first two guesses and the vanishing of one integer polynomial $Q$. Compare the printed equation directly with `Classes.Jones.NormalForm` in `JonesInterface.lean`.

The project's bounded class counts total witness length using at least one bit per natural, including zero. These two budget conventions need an argument. `Classes.Jones.mem_D_of_normalForm` introduces the exact source lengths and natural slack for each original bound, and combines the equations. Every root must satisfy the individual comparisons. The completeness proof pays the total bit cost of the original witnesses, lengths, slack and all auxiliary polynomial witnesses. `Classes.Jones.lengthGraph_of_curve` supplies an exact length graph, including the value at zero. The native verifier used in this argument has soundness for roots of any length.

## A correction to (49) on p. 827

Write $a\preceq b$ if every set bit of $a$ is also set in $b$. The printed halving step ends its third mask with $+I$. Two radix-64 time positions give the following check, with the first position inactive and the second active.

| Quantity | Value |
| --- | --- |
| Radix $Q$ | 64 |
| Word of time markers $I$ | $1+64=65$ |
| Active time $L$ | 64 |
| Packed register $R$ | $0+2\cdot64=128$ |
| Proposed quotient contribution $J$ | 0 |

The first two masks hold because their left sides are zero. The right side of the printed third mask is $63(65-64)+0+65=128$, so that mask also holds. Equation (50) requires $J=64$ in the active position. The carry from the inactive position makes the wrong $J$ pass. `JMTableau.printed_half_mask_wrong_quotient` checks this example. `JMTableau.printed_half_mask_counterexample` gives a separate example where the printed mask rejects every proposed quotient and the honest execution satisfies the paper's radix-size bound.

Keeping the first two masks and changing the third to $R\preceq(Q-1)(I-L)+2J+L$ repairs the step. `JMTableau.halfConditions_iff` proves for every finite trace and every admissible power-of-two radix that this forces exactly the floor-half contribution on active positions and zero on inactive positions. The machine in (42) subtracts this contribution, producing the ceiling half. This is a local correction to the derivation. The language characterization in (53) still has to be connected to the project's machine encoding.

## The two routes through the compiler

The direct route now proves `Classes.np_subset_d_of_native`. It verifies a bounded affine register trace with a fixed number of bit masks, compiles their native polynomial witnesses together, and charges the sizes of all auxiliary coordinates. This route proves the needed language inclusion. Producing the literal single external bit mask of (53) is a different syntactic target and is no longer a premise of the class theorem.

For the other inclusion, `Classes.polynomialEvaluationInP` constructs a total finite-alphabet TM2 verifier for any fixed signed polynomial, including the running-time bound. Both implications are assembled in `VerifiedCompilers.lean`.
