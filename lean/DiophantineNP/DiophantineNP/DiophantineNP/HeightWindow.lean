import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Consecutive heights and the second iteration

This is the real-variable argument in Appendix A. The assumption on `h` is
the uniform comparison of naive and canonical heights along the cyclic group.
The curve-specific construction of such an `h` remains a separate obligation.
-/

namespace DiophantineNP.HeightWindow

/-- The naive heights along the multiples of a generator differ from
`α j²` by at most four, in the base-two normalization of the draft. -/
def QuadraticEstimate (h : ℤ → ℝ) (α : ℝ) : Prop :=
  ∀ j : ℤ, |h j - α * (j : ℝ)^2| ≤ 4

/-- Accumulated error from repeatedly doubling a point with bounded
one-step discrepancy. -/
theorem doubling_error {s : ℕ → ℝ} (hs : ∀ n, |s (n+1) - 4*s n| ≤ 12) (n : ℕ) :
    |s n - 4^n*s 0| ≤ 4*(4^n-1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h := abs_le.mp (hs n)
    have h' := abs_le.mp ih
    rw [pow_succ]
    apply abs_le.mpr
    constructor <;> linarith [h.1, h.2, h'.1, h'.2]

/-- The normalized doubling sequence converges by geometric control of
successive differences. -/
theorem canonical_exists {s : ℕ → ℝ} (hs : ∀ n, |s (n+1)-4*s n| ≤ 12) :
    ∃ b : ℝ, Filter.Tendsto (fun n : ℕ => s n/4^n) Filter.atTop (nhds b) := by
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_le_geometric (1/4 : ℝ) 3 (by norm_num)
  intro n
  have hp : 0 < (4 : ℝ)^n := by positivity
  have heq : s n/4^n - s (n+1)/4^(n+1) =
      -(s (n+1)-4*s n)/(4^n*4) := by rw [pow_succ]; field_simp; ring
  calc dist (s n/4^n) (s (n+1)/4^(n+1)) =
        |s (n+1)-4*s n|/(4^n*4) := by
          rw [Real.dist_eq,heq,abs_div,abs_neg,abs_of_pos (show (0 : ℝ) < 4^n*4 by positivity)]
       _ ≤ 12/(4^n*4) := div_le_div_of_nonneg_right (hs n) (by positivity)
       _ = 3*(1/4)^n := by rw [div_pow,one_pow]; field_simp; ring

/-- The naive log height differs by at most four from any canonical
height obtained by the normalized doubling limit. -/
theorem canonical_error {s : ℕ → ℝ} {b : ℝ}
    (hs : ∀ n, |s (n+1) - 4*s n| ≤ 12)
    (hb : Filter.Tendsto (fun n : ℕ => s n / 4^n) Filter.atTop (nhds b)) :
    |s 0 - b| ≤ 4 := by
  have he (n : ℕ) : s 0 - 4 ≤ s n/4^n ∧ s n/4^n ≤ s 0 + 4 := by
    obtain ⟨hl, hu⟩ := abs_le.mp (doubling_error hs n)
    have hp : 0 < (4 : ℝ)^n := by positivity
    constructor
    · apply (le_div_iff₀ hp).mpr
      linarith
    · apply (div_le_iff₀ hp).mpr
      linarith
  have hlo := ge_of_tendsto' hb (fun n => (he n).1)
  have hhi := le_of_tendsto' hb (fun n => (he n).2)
  apply abs_le.mpr
  constructor <;> linarith

/-- The one explicit multiple 16P bounds the generator's quadratic coefficient. -/
theorem generator_bounds {h : ℤ → ℝ} {α : ℝ}
    (hh : QuadraticEstimate h α) (hl : 18 < h 16) (hu : h 16 < 19) :
    1/20 < α ∧ α < 1/10 := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp (hh 16)
  norm_num at h₁ h₂
  constructor <;> linarith

private theorem difference_estimate {h : ℤ → ℝ} {α : ℝ}
    (hh : QuadraticEstimate h α) (j : ℤ) :
    |(h (j+1) - h j) - α * (2*(j : ℝ)+1)| ≤ 8 := by
  obtain ⟨hl, hu⟩ := abs_le.mp (hh j)
  obtain ⟨hl', hu'⟩ := abs_le.mp (hh (j+1))
  push_cast at hl' hu'
  apply abs_le.mpr
  constructor <;> linarith

/-- Some consecutive pair of heights has a difference between `L` and
`2 L`, so the multiplicative window has an honest witness. -/
theorem exists_adjacent {h : ℤ → ℝ} {α L : ℝ}
    (hα : 1/20 < α) (hα' : α < 1/10)
    (hL : 1024 ≤ L) (hh : QuadraticEstimate h α) :
    ∃ j : ℤ, L ≤ h (j+1) - h j ∧ h (j+1) - h j ≤ 2*L := by
  let j : ℤ := ⌊3*L/(4*α)⌋
  have hpos : 0 < 4*α := by linarith
  have hlo : (j : ℝ) ≤ 3*L/(4*α) := Int.floor_le _
  have hhi : 3*L/(4*α) < (j : ℝ)+1 := Int.lt_floor_add_one _
  have hj₁ := (le_div_iff₀ hpos).mp hlo
  have hj₂ := (div_lt_iff₀ hpos).mp hhi
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp (difference_estimate hh j)
  refine ⟨j, ?_, ?_⟩ <;> linarith

/-- Every consecutive pair in this window has a quadratically bounded
starting height, independently of how the pair was chosen. -/
theorem bounds_of_adjacent {h : ℤ → ℝ} {α L : ℝ}
    (hα : 1/20 < α) (hα' : α < 1/10) (hL : 1024 ≤ L)
    (hh : QuadraticEstimate h α) {j : ℤ}
    (hlo : L ≤ h (j+1)-h j) (hhi : h (j+1)-h j ≤ 2*L) :
    L^2 / 2 ≤ h j ∧ h j ≤ 45 * L^2 := by
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp (difference_estimate hh j)
  obtain ⟨hl, hu⟩ := abs_le.mp (hh j)
  have hpos : 0 ≤ α := by linarith
  have ha : L/4 ≤ α * (j : ℝ) := by linarith
  have hb : α * (j : ℝ) ≤ 5*L/4 := by linarith
  have hc : 0 ≤ α * (j : ℝ)^2 := mul_nonneg hpos (sq_nonneg _)
  have hsq : 1024^2 ≤ L^2 := by
    simpa only [sq] using mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1024) hL
  constructor
  · have hs := mul_self_le_mul_self (show 0 ≤ L/4 by linarith) ha
    have hp := mul_nonneg hc (show 0 ≤ 1/10-α by linarith)
    nlinarith only [hl, hs, hp, hsq]
  · have hs := mul_self_le_mul_self (show 0 ≤ α * (j : ℝ) by linarith) hb
    have hp := mul_nonneg hc (show 0 ≤ α-1/20 by linarith)
    nlinarith only [hu, hs, hp, hsq]

/-- Two successful height windows give the quartic bounds used for the cap.
All variables here are already logarithms. -/
theorem twice {L L₁ L₂ : ℝ}
    (hl₁ : L^2/2 ≤ L₁) (hu₁ : L₁ ≤ 45*L^2)
    (hl₂ : L₁^2/2 ≤ L₂) (hu₂ : L₂ ≤ 45*L₁^2) :
    L^4/8 ≤ L₂ ∧ L₂ ≤ 45^3*L^4 := by
  have hs : 0 ≤ L^2/2 := by positivity
  have ha := mul_self_le_mul_self hs hl₁
  have hb := mul_self_le_mul_self (hs.trans hl₁) hu₁
  constructor <;> nlinarith only [ha, hb, hl₂, hu₂]

end DiophantineNP.HeightWindow
