import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The explicit rational approximation to π in Section 3.1 -/

namespace DiophantineNP.Wallis

/-- The draft's rational parameter, embedded into the reals for the estimate. -/
noncomputable def approxPi (n : ℕ) : ℝ :=
  16^n / ((n:ℝ) * ((2*n).choose n : ℝ)^2)

private theorem wallis_central (n : ℕ) :
    Real.Wallis.W n = (16:ℝ)^n / (((2*n).choose n : ℝ)^2 * (2*n+1)) := by
  have hnat : (2*n).choose n * n.factorial * n.factorial = (2*n).factorial := by
    simpa only [two_mul] using Nat.add_choose_mul_factorial_mul_factorial n n
  have hfac : (((2*n).choose n : ℝ) * (n.factorial:ℝ) * (n.factorial:ℝ)) =
      ((2*n).factorial : ℝ) := by exact_mod_cast hnat
  have hcoef : (0:ℝ) < (2*n).choose n := by
    exact_mod_cast Nat.choose_pos (by omega : n ≤ 2*n)
  have hf : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hpow : (2:ℝ)^(4*n) = 16^n := by rw [pow_mul]; norm_num
  rw [Real.Wallis.W_eq_factorial_ratio, hpow, ← hfac]
  field_simp

private theorem wallis_strict_upper (n : ℕ) : Real.Wallis.W n < Real.pi/2 := by
  apply lt_of_lt_of_le _ (Real.Wallis.W_le (n+1))
  rw [Real.Wallis.W_succ]
  have hfac : (1:ℝ) < (2*n+2)/(2*n+1)*((2*n+2)/(2*n+3)) := by
    rw [div_mul_div_comm]
    apply (lt_div_iff₀ (by positivity)).2
    ring_nf
    linarith
  simpa using mul_lt_mul_of_pos_left hfac (Real.Wallis.W_pos n)

/-- The explicit strict two-sided Wallis estimate from the manuscript.
All constants are valid even at n = 1. -/
theorem approxPi_ratio (n : ℕ) (hn : 0 < n) :
    1 < approxPi n / Real.pi ∧ approxPi n / Real.pi < 1 + 1/(2*(n:ℝ)) := by
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have hcoef : (0:ℝ) < (2*n).choose n := by
    exact_mod_cast Nat.choose_pos (by omega : n ≤ 2*n)
  have hp := Real.pi_pos
  have hlink : (n:ℝ) * approxPi n = (2*(n:ℝ)+1)*Real.Wallis.W n := by
    rw [approxPi, wallis_central]
    field_simp
  have hlow := Real.Wallis.le_W n
  have hhigh := wallis_strict_upper n
  have hp0 : 0 < 2*(n:ℝ)+2 := by positivity
  have hlow' : (2*(n:ℝ)+1)*Real.pi ≤ (Real.Wallis.W n)*(2*(2*n+2)) := by
    field_simp at hlow
    linarith
  constructor
  · apply (lt_div_iff₀ hp).2
    by_contra! hnpi
    have htest := mul_le_mul_of_nonneg_left hnpi hN.le
    have htest' := mul_le_mul_of_nonneg_left htest (show 0 ≤ 2*(2*(n:ℝ)+2) by positivity)
    have hpo := mul_le_mul_of_nonneg_left hlow' (show 0 ≤ 2*(n:ℝ)+1 by positivity)
    rw [hlink] at htest'
    nlinarith
  · apply (div_lt_iff₀ hp).2
    have h := mul_lt_mul_of_pos_left hhigh (show 0 < 2*(n:ℝ)+1 by positivity)
    rw [← hlink] at h
    field_simp
    linarith

end DiophantineNP.Wallis
