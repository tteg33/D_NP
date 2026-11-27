import DiophantineNP.PowerTests

/-! # Conversion to the canonical height in the literature -/

namespace DiophantineNP.Curve37
open Filter

/-- Silverman's limit for the even function x of degree two, using the natural logarithm. -/
theorem silverman_limit (Q : E.Point) :
    Tendsto (fun n : ℕ => Real.log (height ((2^n : ℕ) • Q)) / (2 * 4^n))
      atTop (nhds ((Real.log 2 / 2) * canonicalHeight Q)) := by
  convert (canonical_limit Q).const_mul (Real.log 2 / 2) using 1
  funext n
  dsimp [logHeight,Real.logb]
  have hlog := Real.log_pos (by norm_num : (1:ℝ) < 2)
  field_simp

/-- Formal conversion of the two Néron–Tate normalizations by uniqueness of limits. -/
theorem quadratic_of_silverman (H : E.Point → ℝ)
    (hdef : ∀ Q, Tendsto (fun n : ℕ => Real.log (height ((2^n : ℕ) • Q)) / (2*4^n))
      atTop (nhds (H Q)))
    (hquad : ∀ j : ℤ, H (j • P) = H P * (j : ℝ)^2) : PowerTests.Quadratic := by
  have heq (Q : E.Point) : H Q = Real.log 2 / 2 * canonicalHeight Q :=
    tendsto_nhds_unique (hdef Q) (silverman_limit Q)
  intro j
  have h := hquad j
  rw [heq,heq] at h
  rw [mul_assoc] at h
  exact mul_left_cancel₀ (by positivity : (Real.log 2 / 2) ≠ 0) h

/-- The bounded error in the naive multiplication-by-j formula (Silverman VIII.6.4(b))
suffices even when known just on the doubling orbit of the generator. -/
theorem quadratic_of_naive_error
    (error : ∀ j : ℤ, ∃ C : ℝ, ∀ n : ℕ,
      |logHeight (j • ((2^n : ℕ) • P)) - logHeight ((2^n : ℕ) • P) * (j : ℝ)^2| ≤ C) :
    PowerTests.Quadratic := by
  intro j
  obtain ⟨C,hC⟩ := error j
  have hd := ((canonical_limit (j • P)).sub ((canonical_limit P).mul_const ((j : ℝ)^2))).abs
  have hlim : Tendsto (fun n : ℕ => C / 4^n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hbound : |canonicalHeight (j • P)-canonicalHeight P*(j:ℝ)^2| ≤ 0 := by
    apply le_of_tendsto_of_tendsto' hd hlim
    intro n
    change |logHeight ((2^n : ℕ) • (j • P)) / 4^n -
      logHeight ((2^n : ℕ) • P) / 4^n * (j : ℝ)^2| ≤ C/4^n
    rw [smul_comm (2^n : ℕ) j,div_mul_eq_mul_div,←sub_div,abs_div,abs_of_pos (by positivity : (0:ℝ)<4^n)]
    exact div_le_div_of_nonneg_right (hC n) (by positivity)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _)))

end DiophantineNP.Curve37
