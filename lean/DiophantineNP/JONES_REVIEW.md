# Checking the Jones–Matiyasevich step

Jones and Matiyasevich give a bounded numerical characterization of NP in §5, equation (53), p. 827. Section 5 restricts the length of an accepting register computation to a polynomial in the input length. The introductory theorem treats enumerable sets. [Published article, pp. 818–829](https://doi.org/10.2307/2274135)

The current end-to-end proof in `NativeComplexity.lean` compiles as many bit masks as the fixed verifier needs into one polynomial. It preserves the original NP certificate cutoff. The older route through the exact one-mask syntax of (53) is documented here to make the source comparison and local correction reviewable.

## The bound in (53)

The input and witnesses are naturals. The source's length is the least integer at least $\log_2(x+1)$, which is `Nat.size x` and gives zero at zero. A fixed integer polynomial $P$ bounds the length of **each** guessed integer separately and inclusively. The other conditions are bitwise inclusion between the first two guesses and the vanishing of one integer polynomial $Q$. Compare the printed equation directly with `Classes.Jones.NormalForm` in `JonesInterface.lean`.

The project's bounded class counts total witness length using at least one bit per natural, including zero. These two budget conventions need an argument. `Classes.Jones.mem_D_of_normalForm` introduces the exact source lengths and natural slack for each original bound, and combines the equations. Every root must satisfy the individual comparisons. The completeness proof pays the total bit cost of the original witnesses, lengths, slack and all auxiliary polynomial witnesses. `Classes.Jones.lengthGraph_of_curve` supplies an exact length graph, including the value at zero. The native verifier used in this argument has soundness for roots of any length.

## A correction to (49) on p. 827

On journal p. 827 (page 10 of the Cambridge PDF), equation (49) gives three masks for the contribution of a halving instruction. Here $a\preceq b$ means that every set bit of $a$ is set in $b$. With the paper’s indices, the printed conditions are

$$
2J_{j,p}\preceq R_j,\qquad J_{j,p}\preceq (Q/2-1)L_p,\qquad
R_j\preceq (Q-1)(I-L_p)+2J_{j,p}+I.
$$

The sentence following (49) asserts that these conditions imply (50), which gives the packed floor-half contribution at active time positions. In the scan the third mask ends in $+I$. [Original article, p. 827, equations (49)–(50)](https://doi.org/10.2307/2274135)

For two radix-64 time positions, take the first position inactive and the second active. The table abbreviates $(L_p,R_j,J_{j,p})$ as $(L,R,J)$.

| Quantity | Value |
| --- | --- |
| Radix $Q$ | 64 |
| Word of time markers $I$ | $1+64=65$ |
| Active time $L$ | 64 |
| Packed register $R$ | $0+2\cdot64=128$ |
| Proposed quotient contribution $J$ | 0 |

The first two masks hold because their left sides are zero. The right side of the printed third mask is $63(65-64)+0+65=128$, so that mask also holds. Equation (50) requires $J=64$ in the active position. The carry from the inactive position makes the wrong $J$ pass. `JMTableau.printed_half_mask_wrong_quotient` checks this example. `JMTableau.printed_half_mask_counterexample` checks the opposite failure. For $I=1+Q+Q^2+Q^3$, $L=Q$, and $R=1+Q+Q^2$, the low bit of $R$ is one. The right side of the printed third mask is even for every $J$, and the honest execution meets the radix bound (46).

Keeping the first two masks and changing the third to $R\preceq(Q-1)(I-L)+2J+L$ repairs the step. `JMTableau.halfConditions_iff` proves for every finite trace and every admissible power-of-two radix that this forces exactly the floor-half contribution on active positions and zero on inactive positions. The machine in (42) subtracts this contribution, producing the ceiling half. The first counterexample falsifies the implication from printed (49) to (50). Equation (53) is a further characterization of languages. Its literal one-mask form for every verifier in this project's encoding is the proposition `JonesSourceDirection` in `JonesReduction.lean`, an input to an alternative conditional theorem.

## The two routes through the compiler

The direct route proves `Classes.np_subset_d_of_native`. It verifies a bounded affine register trace with a fixed number of bit masks, compiles their native polynomial witnesses together, and charges the sizes of all auxiliary coordinates. `classEquality_of_native` uses this inclusion. Inspect `Classes.np_subset_d_of_native` and `Classes.Jones.mem_D_of_normalForm` to compare the direct compiler with the conditional one-mask route.

For the other inclusion, `Classes.polynomialEvaluationInP` constructs a total finite-alphabet TM2 verifier for any fixed signed polynomial, including the running-time bound. Both implications are assembled in `VerifiedCompilers.lean`.
