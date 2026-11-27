import DiophantineNP.KernelGrowth
import DiophantineNP.NaturalBridge

/-! # Bit length of the rational Fourier readout

At the all-ones assignment the integral numerator is the sum of the expanded
coefficients. The coefficient mass and common denominator give an explicit
short fraction independently of any constraint system for computing it.
-/

namespace DiophantineNP.FormulaLaurent
open Counting LaurentBounds
open scoped BigOperators

noncomputable section

/-- The signed numerator before reducing the fraction. -/
def numeratorAtOne {d : ℕ} (e : Expr d) : ℤ := ∑ t, e.expand.coeff t

theorem scalarAtOne_eq_fraction {d : ℕ} (e : Expr d) :
    scalarAtOne e = (numeratorAtOne e : ℚ) / e.bounds.denominator := by
  simp [scalarAtOne, Expr.evaluate, Raw.evaluate, coordinateCharacter, numeratorAtOne]

theorem numeratorAtOne_le_height {d : ℕ} (e : Expr d) :
    (numeratorAtOne e).natAbs ≤ e.bounds.height := by
  apply le_trans _ e.bounds_sound.1
  have h : |∑ t, e.expand.coeff t| ≤ ∑ t, |e.expand.coeff t| :=
    Finset.abs_sum_le_sum_abs ..
  exact_mod_cast (show ((numeratorAtOne e).natAbs : ℤ) ≤ (e.expand.mass : ℤ) by
    simpa [numeratorAtOne, Raw.mass] using h)

private theorem short_fraction_of_bounds {d U c : ℕ} (e : Expr d) (hU : 0 < U)
    (budget : e.bounds.radius + bits e.bounds.denominator + bits e.bounds.height ≤ (U+1)^c) :
    ∃ p q : ℤ, 0 < q ∧ (p : ℚ) / (q : ℚ) = scalarAtOne e ∧
      (bits p.natAbs + 1) + (bits q.natAbs + 1) ≤ (1+U)^(c+2) := by
  refine ⟨numeratorAtOne e, e.bounds.denominator, by exact_mod_cast e.denominator_pos, ?_, ?_⟩
  · exact_mod_cast (scalarAtOne_eq_fraction e).symm
  · have hnum := FourSquare.bits_mono (numeratorAtOne_le_height e)
    have hfactor : 4 ≤ (U+1)^2 := by nlinarith
    have hpos : 0 < (U+1)^c := pow_pos (by omega) _
    have hg := Nat.mul_le_mul_left ((U+1)^c) hfactor
    simp only [Int.natAbs_natCast, Nat.add_comm 1 U, pow_add]
    omega

/-- For each fixed formula, the two signed output registers together need only
polynomially many bits, uniformly in the numerical parameters. -/
theorem packedScalar_short_fraction {k : ℕ} (φ : Formula (k+1)) :
    ∃ C : ℕ, ∀ U, 0 < U → ∀ t : Fin k → Fin U, ∃ p q : ℤ,
      0 < q ∧ (p : ℚ) / (q : ℚ) = packedScalar φ t ∧
      (bits p.natAbs + 1) + (bits q.natAbs + 1) ≤ (1+U)^C := by
  obtain ⟨c, hc⟩ := packedExpr_uniform_size φ
  exact ⟨c+2, fun U hU t => short_fraction_of_bounds (packedExpr φ t) hU (hc U hU t)⟩

end
end DiophantineNP.FormulaLaurent
