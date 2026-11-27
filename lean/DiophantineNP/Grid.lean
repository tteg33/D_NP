import DiophantineNP.Wallis
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The analytic label and window estimates on the cyclic grid

The coordinate of a selected arc is described by its signed displacement
from a quarter-period center. For the window, `h` is the unsigned integer
distance to the nearer center. -/

namespace DiophantineNP.Grid

open Real

/-- Geometry estimates used below. The draft's actual parameters instantiate
them in `paperGeometry`. -/
structure Geometry where
  B : ℝ
  M : ℝ
  P : ℝ
  hB : 2 ≤ B
  large : 512*(B+1)^3 ≤ M
  lower : π ≤ P
  upper : P ≤ π * (1 + 1/(2*M^4))

def period (B : ℕ) : ℕ := 4*(2*B+1)*(2*B+2)^30

theorem period_large (B : ℕ) : 512*(B+1)^3 ≤ period B := by
  have hb : 1 ≤ B+1 := by omega
  have h₁ := pow_le_pow_right₀ hb (by decide : 3 ≤ 30)
  have he : 2*B+2 = 2*(B+1) := by omega
  unfold period
  rw [he, mul_pow]
  nlinarith [Nat.zero_le ((B+1)^30), Nat.zero_le (B*(B+1)^30)]

/-- Includes the rational Wallis parameter and the actual polynomial-sized
period. -/
noncomputable def paperGeometry (B : ℕ) (hB : 2 ≤ B) : Geometry := by
  let M := period B
  have hm : 0 < M := by dsimp [M, period]; positivity
  have h := Wallis.approxPi_ratio (M^4) (pow_pos hm _)
  refine ⟨B, M, Wallis.approxPi (M^4), by exact_mod_cast hB, ?_, ?_, ?_⟩
  · exact_mod_cast period_large B
  · have hlow := (lt_div_iff₀ pi_pos).mp h.1
    linarith
  · have hhi := (div_lt_iff₀ pi_pos).mp h.2
    push_cast at hhi
    linarith

private theorem small_sine {x : ℝ} (hx : |x| ≤ 1) :
    |sin x-x| ≤ |x|^3/4 := by
  have hpos {t : ℝ} (ht : 0 ≤ t) (hu : t ≤ 1) : |sin t-t| ≤ t^3/4 := by
    rcases ht.eq_or_lt with rfl | ht
    · simp
    rw [abs_of_nonpos (sub_nonpos.mpr (sin_le ht.le))]
    linarith [sin_gt_sub_cube ht hu]
  rcases le_total 0 x with h | h
  · simpa [abs_of_nonneg h] using hpos h (by simpa [abs_of_nonneg h] using hx)
  · have hn := hpos (neg_nonneg.mpr h) (by simpa [abs_of_nonpos h] using hx)
    rw [sin_neg, neg_sub_neg] at hn
    simpa [abs_of_nonpos h, abs_sub_comm] using hn

namespace Geometry

variable (g : Geometry)

private theorem basic : 32*(g.B+1) ≤ g.M ∧ 1 ≤ g.M := by
  have h := pow_le_pow_right₀ (by linarith [g.hB] : 1 ≤ g.B+1) (by decide : 1 ≤ 3)
  rw [pow_one] at h
  constructor <;> linarith [g.large, g.hB]

private theorem mpos : 0 < g.M := by linarith [g.basic.2]

private theorem ppos : 0 < g.P := lt_of_lt_of_le pi_pos g.lower

/-- Angular displacement from the center by `j` grid steps. -/
noncomputable def angle (j : ℝ) : ℝ := 2*π*j/g.M

private theorem angle_bound {K j : ℝ} (hj : |j| ≤ K) :
    |g.angle j| ≤ 2*π*K/g.M := by
  rw [angle, abs_div, abs_mul, abs_of_pos g.mpos, abs_of_pos (by positivity : 0 < 2*π)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hj (by positivity)) g.mpos.le

private theorem scaled_sine {K j : ℝ} (hK : 0 ≤ K) (hj : |j| ≤ K) (hk : K ≤ g.B+1) :
    |g.M*sin (g.angle j)-2*π*j| ≤ 128*K^3/g.M^2 := by
  have hm := g.mpos
  have harg := g.angle_bound hj
  have hsmall : |g.angle j| ≤ 1 := by
    apply harg.trans
    apply (div_le_one hm).2
    have hp := mul_le_mul_of_nonneg_right (by linarith [pi_lt_four] : 2*π ≤ 8) hK
    linarith [g.basic.1]
  have hpow := pow_le_pow_left₀ (abs_nonneg _) harg 3
  have hpi : (2*π)^3 ≤ 512 := by
    have := pow_le_pow_left₀ (by positivity : 0 ≤ 2*π)
      (by linarith [pi_lt_four] : 2*π ≤ 8) 3
    norm_num at this
    exact this
  calc
    _ = g.M * |sin (g.angle j) - g.angle j| := by
      rw [← abs_of_pos hm, ← abs_mul]
      congr 1
      unfold angle
      field_simp
      rw [abs_of_pos hm]
    _ ≤ g.M * (|g.angle j|^3/4) :=
      mul_le_mul_of_nonneg_left (small_sine hsmall) hm.le
    _ ≤ g.M * ((2*π*K/g.M)^3/4) := by gcongr
    _ = ((2*π)^3*K^3/4)/g.M^2 := by field_simp
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have h := mul_le_mul_of_nonneg_right hpi (pow_nonneg hK 3)
      linarith

/-- The cosine observable agrees on the two copies of a selected label. -/
theorem selected_cos (j : ℝ) (reflected : Bool) :
    cos (if reflected then -(π/2+g.angle j) else π/2+g.angle j) = -sin (g.angle j) := by
  cases reflected <;> simp only [Bool.false_eq_true, ↓reduceIte, cos_neg, add_comm (π/2), cos_add_pi_div_two]

/-- Selected label error, at the constants of the manuscript. -/
theorem label_error {j : ℝ} (hj : |j| ≤ g.B) :
    |(g.B+g.M*sin (g.angle j)/(2*g.P)) - (g.B+j)| ≤
      32*g.B^3/g.M^2 + g.B/g.M^4 := by
  have hB := g.hB
  have hpi := pi_gt_three
  have hP := g.ppos
  have hM := g.mpos
  have hs := g.scaled_sine (by linarith) hj (by linarith)
  have hden : 0 < 2*g.P := by positivity
  have ha : |(g.M*sin (g.angle j)-2*π*j)/(2*g.P)| ≤ 32*g.B^3/g.M^2 := by
    rw [abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    apply hs.trans
    have hb3 : 0 ≤ g.B^3/g.M^2 := by positivity
    have he := mul_le_mul_of_nonneg_right
      (by linarith [g.lower] : 128 ≤ 32*(2*g.P)) hb3
    convert he using 1 <;> ring
  have hpnear : (g.P-π)/g.P ≤ 1/g.M^4 := by
    apply (div_le_iff₀ hP).2
    have hu := g.upper
    have hM4 : 0 < g.M^4 := by positivity
    field_simp at hu ⊢
    nlinarith [g.lower]
  have hw := mul_le_mul hpnear hj (abs_nonneg _) (by positivity)
  calc
    _ = |(g.M*sin (g.angle j)-2*π*j)/(2*g.P) + (π-g.P)/g.P*j| := by
      congr 1
      field_simp
      ring
    _ ≤ |(g.M*sin (g.angle j)-2*π*j)/(2*g.P)| + |(π-g.P)/g.P*j| := abs_add_le _ _
    _ ≤ _ := by
      apply add_le_add ha
      rw [abs_mul, abs_div, abs_of_nonpos (by linarith [g.lower]), abs_of_pos hP]
      convert hw using 1 <;> ring

/-- The observable has a uniform bound on every grid point. -/
theorem observable_bound {c : ℝ} (hc : |c| ≤ 1) :
    |g.B - g.M*c/(2*g.P)| < g.M := by
  have hp := g.ppos
  have hm := g.mpos
  have hb := g.hB
  calc
    _ ≤ |g.B| + |g.M*c/(2*g.P)| := abs_sub _ _
    _ ≤ g.B + g.M/(2*g.P) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ g.B), abs_div, abs_mul,
        abs_of_pos hm, abs_of_pos (by positivity : 0 < 2*g.P)]
      gcongr
      simpa using mul_le_mul_of_nonneg_left hc hm.le
    _ < _ := by
      have he : g.M/(2*g.P) ≤ g.M/2 := by
        apply div_le_div_of_nonneg_left hm.le (by norm_num)
        linarith [g.lower, pi_gt_three]
      linarith [g.basic.1]

/-- Multiplying by `M` puts the two window cutoffs on the same scale. -/
private theorem cutoff_bounds :
    π*(2*g.B+1) ≤ g.P*(2*g.B+1) ∧
    g.P*(2*g.B+1) ≤ π*(2*g.B+1)+1/2 := by
  have hB := g.hB
  have hM := g.mpos
  have hJ : 0 ≤ 2*g.B+1 := by linarith
  have hM4 : g.M ≤ g.M^4 := by
    simpa using (pow_le_pow_right₀ g.basic.2 (by decide : 1 ≤ 4))
  have hp := mul_le_mul_of_nonneg_right pi_lt_four.le hJ
  have hw : π*(2*g.B+1) ≤ g.M^4 := by linarith [g.basic.1]
  constructor
  · exact mul_le_mul_of_nonneg_right g.lower hJ
  · apply (mul_le_mul_of_nonneg_right g.upper hJ).trans
    have hd : 0 < g.M^4 := by positivity
    field_simp
    linarith

/-- The window in terms of the distance in grid steps to the nearer center. -/
noncomputable def window (h : ℝ) : ℝ :=
  ((g.P*(2*g.B+1)/g.M)^2 - sin (g.angle h)^2)/4

private theorem scaled_window (h : ℝ) :
    4*g.M^2*g.window h = (g.P*(2*g.B+1))^2 - (g.M*sin (g.angle h))^2 := by
  have := g.mpos
  unfold window
  field_simp

private theorem square_gap {x y : ℝ} (hx : 0 ≤ x) (h : x+2 ≤ y) :
    x^2+4 ≤ y^2 := by
  have hs := (sq_le_sq₀ (by linarith : 0 ≤ x+2) (by linarith : 0 ≤ y)).2 h
  linarith

private theorem angle_in_first_quadrant {h : ℝ} (h₀ : 0 ≤ h) (h₁ : 4*h ≤ g.M) :
    0 ≤ g.angle h ∧ g.angle h ≤ π/2 := by
  have hm := g.mpos
  unfold angle
  refine ⟨by positivity, (div_le_iff₀ hm).2 ?_⟩
  linarith [mul_le_mul_of_nonneg_left h₁ pi_pos.le]

private theorem inside_gap {h : ℝ} (h₀ : 0 ≤ h) (h₁ : 4*h ≤ g.M) (hin : h ≤ g.B) :
    1/g.M^2 ≤ g.window h := by
  have ⟨ha,hb⟩ := g.angle_in_first_quadrant h₀ h₁
  have hs := sin_le ha
  change sin (g.angle h) ≤ 2*π*h/g.M at hs
  have hs' := (le_div_iff₀ g.mpos).mp hs
  have hsinpos := sin_nonneg_of_nonneg_of_le_pi ha (by linarith [pi_pos])
  have hdiff : g.M*sin (g.angle h)+2 ≤ g.P*(2*g.B+1) := by
    linarith [g.cutoff_bounds.1, mul_le_mul_of_nonneg_left hin (show 0≤2*π by positivity),
      pi_gt_three]
  have hsquare := square_gap (mul_nonneg g.mpos.le hsinpos) hdiff
  apply (div_le_iff₀ (sq_pos_of_pos g.mpos)).2
  linarith only [hsquare, g.scaled_window h]

private theorem outside_gap {h : ℝ} (h₀ : 0 ≤ h) (h₁ : 4*h ≤ g.M) (hout : g.B+1 ≤ h) :
    g.window h ≤ -(1/g.M^2) := by
  have hm := g.mpos
  have hB := g.hB
  have hb : 0 ≤ g.B+1 := by linarith
  have ha₀ : 0 ≤ g.angle (g.B+1) := by unfold angle; positivity
  have ⟨_,ha₁⟩ := g.angle_in_first_quadrant h₀ h₁
  have hmon : g.angle (g.B+1) ≤ g.angle h := by
    unfold angle
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hout (by positivity)) hm.le
  have hsin := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos] : -(π/2) ≤ g.angle (g.B+1))
    ha₁ hmon
  have hs := g.scaled_sine hb (le_of_eq (abs_of_nonneg hb)) le_rfl
  have hhalf : 128*(g.B+1)^3/g.M^2 ≤ 1/2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hm)).2
    have hm2 : g.M ≤ g.M^2 := by
      simpa using pow_le_pow_right₀ g.basic.2 (by decide : 1 ≤ 2)
    linarith [g.large]
  have hdiff : g.P*(2*g.B+1)+2 ≤ g.M*sin (g.angle h) := by
    linarith [neg_le_of_abs_le (hs.trans hhalf),
      g.cutoff_bounds.2, mul_le_mul_of_nonneg_left hsin hm.le, pi_gt_three]
  have hsquare := square_gap (mul_nonneg g.ppos.le (show 0 ≤ 2*g.B+1 by linarith)) hdiff
  have hneg : 1/g.M^2 ≤ -g.window h := by
    apply (div_le_iff₀ (sq_pos_of_pos hm)).2
    linarith only [hsquare, g.scaled_window h]
  linarith only [hneg]

/-- The window is positive exactly on the selected arcs, with the stated
inverse-square margin in both directions. The disjunction records that
the distance and the radius are in integer grid steps. -/
theorem window_bounds {h : ℝ} (h₀ : 0 ≤ h) (h₁ : 4*h ≤ g.M)
    (integerGap : h ≤ g.B ∨ g.B+1 ≤ h) :
    (0 < g.window h ↔ h ≤ g.B) ∧ 1/g.M^2 ≤ |g.window h| ∧ |g.window h| ≤ 1 := by
  have hm := g.mpos
  have hb := g.hB
  have hcut : 0 ≤ g.P*(2*g.B+1) := mul_nonneg g.ppos.le (by linarith)
  have hratio : 0 ≤ g.P*(2*g.B+1)/g.M := div_nonneg hcut hm.le
  have hw : g.P*(2*g.B+1)/g.M ≤ 1 := by
    apply (div_le_one hm).2
    have hr := mul_le_mul_of_nonneg_right pi_lt_four.le (show 0≤2*g.B+1 by linarith)
    linarith [g.cutoff_bounds.2, g.basic.1]
  have hw2 := (sq_le_sq₀ hratio zero_le_one).2 hw
  have hs2 := (sq_le_sq₀ (abs_nonneg (sin (g.angle h))) zero_le_one).2
    (abs_le.mpr ⟨neg_one_le_sin _, sin_le_one _⟩)
  rw [sq_abs] at hs2
  have hu : |g.window h| ≤ 1 := by
    rw [abs_le]
    unfold window
    constructor <;> nlinarith [sq_nonneg (g.P*(2*g.B+1)/g.M), sq_nonneg (sin (g.angle h))]
  have hpos : 0 < 1/g.M^2 := by positivity
  rcases integerGap with hin | hout
  · have he := g.inside_gap h₀ h₁ hin
    exact ⟨iff_of_true (hpos.trans_le he) hin, (he.trans (le_abs_self _)), hu⟩
  · have he := g.outside_gap h₀ h₁ hout
    refine ⟨iff_of_false (by linarith) (by linarith), ?_, hu⟩
    rw [abs_of_nonpos (by linarith : g.window h ≤ 0)]
    linarith

/-- For the actual natural period and integral grid distance, no assumption
about a gap at the cutoff is needed. -/
theorem paper_window (B d : ℕ) (hB : 2 ≤ B) (hd : 4*d ≤ period B) :
    let g := paperGeometry B hB
    (0 < g.window d ↔ d ≤ B) ∧ 1/g.M^2 ≤ |g.window d| ∧ |g.window d| ≤ 1 := by
  let g := paperGeometry B hB
  have h : (d:ℝ) ≤ g.B ∨ g.B+1 ≤ d := by
    change (d:ℝ) ≤ B ∨ (B:ℝ)+1 ≤ d
    rcases le_or_gt d B with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  have hh := g.window_bounds (Nat.cast_nonneg d)
    (show 4*(d:ℝ) ≤ g.M by change 4*(d:ℝ) ≤ (period B:ℝ); exact_mod_cast hd) h
  exact ⟨hh.1.trans (by change (d:ℝ) ≤ B ↔ d ≤ B; exact_mod_cast Iff.rfl), hh.2⟩

end Geometry
/-- On the roots indexed by `0 ≤ l < 4Q`, reflect the second semicircle
onto the first, then subtract the quarter-period center. -/
def fold (Q l : ℤ) : ℤ := min l (4*Q-l)-Q

theorem fold_bounds {Q l : ℤ} (h₀ : 0 ≤ l) (h₁ : l < 4*Q) :
    |fold Q l| ≤ Q := by
  rw [fold, abs_le, min_def]
  split_ifs <;> omega

/-- A label strictly between the two endpoints of the semicircle occurs on
exactly the two indicated, distinct root indices. -/
theorem fold_fiber {Q j : ℤ} (hj : |j| < Q) :
    let a := Q+j
    let b := 4*Q-a
    0 ≤ a ∧ a < b ∧ b < 4*Q ∧
      ∀ l : ℤ, (0 ≤ l ∧ l < 4*Q ∧ fold Q l = j) ↔ l = a ∨ l = b := by
  have hh := abs_lt.mp hj
  dsimp only
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro l
  rw [fold, min_def]
  split_ifs <;> omega

/-- The cosine on an arbitrary root index equals the signed sine at the
folded index. This identifies the analytic distance used in `window_bounds`
with the actual distance in grid steps for both semicircles. -/
theorem cos_fold {Q : ℤ} (hQ : 0 < Q) (l : ℤ) :
    cos (2*π*(l:ℝ)/(4*Q)) = -sin (2*π*(fold Q l:ℝ)/(4*Q)) := by
  have hQr : (0:ℝ) < Q := by exact_mod_cast hQ
  have hangle (a : ℤ) : 2*π*(a:ℝ)/(4*Q) = 2*π*((a:ℝ)-Q)/(4*Q) + π/2 := by
    field_simp
    ring
  unfold fold
  rw [min_def]
  split_ifs with hl
  · push_cast
    conv_lhs => rw [hangle l, cos_add_pi_div_two]
  · have hflip : 2*π*(l:ℝ)/(4*Q) = 2*π - 2*π*((4*Q-l:ℤ):ℝ)/(4*Q) := by
      push_cast
      field_simp
      ring
    rw [hflip, cos_two_pi_sub, hangle (4*Q-l), cos_add_pi_div_two]
    push_cast
    rfl

/-- Explicitly re-index the original squared-cosine window by a nonnegative
integer distance. -/
theorem cos_sq_eq_sin_sq_distance {Q : ℤ} (hQ : 0 < Q) (l : ℤ) :
    cos (2*π*(l:ℝ)/(4*Q))^2 =
      sin (2*π*((fold Q l).natAbs:ℝ)/(4*Q))^2 := by
  rw [cos_fold hQ, neg_sq]
  rcases le_or_gt 0 (fold Q l) with h | h
  · have hh : (((fold Q l).natAbs : ℕ):ℝ) = (fold Q l:ℝ) := by
      rw [Nat.cast_natAbs, abs_of_nonneg h]
    rw [hh]
  · have hh : (((fold Q l).natAbs : ℕ):ℝ) = -(fold Q l:ℝ) := by
      rw [Nat.cast_natAbs, abs_of_nonpos h.le, Int.cast_neg]
    rw [hh, mul_neg, neg_div, sin_neg, neg_sq]

end DiophantineNP.Grid
