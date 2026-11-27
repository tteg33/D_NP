import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import DiophantineNP.HeightWindow
import DiophantineNP.Pell

/-! # Explicit height calculations on the curve 37a1 -/

namespace DiophantineNP.Curve37

open WeierstrassCurve

/-- The affine model `y² + y = x³ - x`. -/
def E : WeierstrassCurve.Affine ℚ := ⟨0, 0, 1, -1, 0⟩

theorem discriminant : E.Δ = 37 := by
  norm_num [E, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

local macro "curve_point" : tactic =>
  `(tactic| norm_num [Affine.nonsingular_iff, Affine.equation_iff, E])

def P : E.Point := .some (x := 0) (y := 0) (by curve_point)
private def P₂ : E.Point := .some (x := 1) (y := 0) (by curve_point)
private def P₄ : E.Point := .some (x := 2) (y := -3) (by curve_point)
private def P₈ : E.Point := .some (x := 21/25) (y := -69/125) (by curve_point)
private def P₁₆ : E.Point :=
  .some (x := 480106/4225) (y := 332513754/274625) (by curve_point)

local macro "double_point" : tactic =>
  `(tactic| (
    rw [Affine.Point.add_self_of_Y_ne (by norm_num [E, Affine.negY]), Affine.Point.some.injEq]
    norm_num [E, Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, Affine.slope]))

private theorem mul_two : (2 : ℕ) • P = P₂ := by
  rw [two_nsmul, P, P₂]
  double_point

private theorem mul_four : (4 : ℕ) • P = P₄ := by
  rw [show (4 : ℕ) = 2+2 by decide, add_nsmul, mul_two, P₂, P₄]
  double_point

private theorem mul_eight : (8 : ℕ) • P = P₈ := by
  rw [show (8 : ℕ) = 4+4 by decide, add_nsmul, mul_four, P₄, P₈]
  double_point

private theorem mul_sixteen : (16 : ℕ) • P = P₁₆ := by
  rw [show (16 : ℕ) = 8+8 by decide, add_nsmul, mul_eight, P₈, P₁₆]
  double_point

def xCoord : E.Point → Option ℚ
  | .zero => none
  | .some (x := x) _ => some x

/-- The rational-root obstruction to a point of order two on this model.
An integral primitive solution of the homogenized cubic would have even
denominator and then even numerator. -/
theorem cubic_ne_zero (x : ℚ) : 4*x^3-4*x+1 ≠ 0 := by
  intro hx
  let u := x.num
  let v : ℤ := x.den
  have hv : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  rw [← x.num_div_den] at hx
  field_simp [hv] at hx
  have hq : 4*(u : ℚ)^3-4*(u : ℚ)*(v : ℚ)^2+(v : ℚ)^3=0 := by
    dsimp [u,v]
    push_cast
    linarith only [hx]
  have hi : 4*u^3-4*u*v^2+v^3=0 := by exact_mod_cast hq
  have huv : IsCoprime u v := Int.isCoprime_iff_nat_coprime.mpr x.reduced
  have h₂ : Prime (2 : ℤ) := Int.prime_two
  have hev : (2 : ℤ) ∣ v := h₂.dvd_of_dvd_pow
    (show (2 : ℤ) ∣ v^3 from ⟨2*u*v^2-2*u^3, by linarith only [hi]⟩)
  obtain ⟨w, hw⟩ := hev
  have heu : (2 : ℤ) ∣ u := h₂.dvd_of_dvd_pow
    (show (2 : ℤ) ∣ u^3 from ⟨2*u*w^2-w^3, by rw [hw] at hi; linarith only [hi]⟩)
  have := huv.isUnit_of_dvd' heu (show (2 : ℤ) ∣ v from ⟨w,hw⟩)
  exact h₂.not_unit this

/-- The multiplication-by-two map from mathlib's group law agrees with
the one-variable rational function used in the height calculation. -/
theorem double_x {x y : ℚ} (h : E.Nonsingular x y) :
    xCoord ((Affine.Point.some h) + (Affine.Point.some h)) =
      some ((x^4+2*x^2-2*x+1)/(4*x^3-4*x+1)) := by
  have heq : y^2 + y = x^3-x := by
    have he := (Affine.equation_iff x y).mp ((Affine.nonsingular_iff x y).mp h).1
    dsimp [E] at he
    linarith only [he]
  have hs : (2*y+1)^2 = 4*x^3-4*x+1 := by linarith only [heq]
  have hn := cubic_ne_zero x
  have hy : 2*y+1 ≠ 0 := by intro hy; rw [hy] at hs; apply hn; linarith only [hs]
  have hny : y ≠ E.negY x y := by
    change y ≠ -y - 0*x - 1
    intro hh
    exact hy (by linarith)
  rw [Affine.Point.add_self_of_Y_ne hny]
  change some (E.addX x x (E.slope x x y y)) = some _
  apply congrArg some
  have hm : E.slope x x y y = (3*x^2-1)/(2*y+1) := by
    rw [Affine.slope_of_Y_ne rfl hny]
    dsimp [E, Affine.negY]
    congr 1 <;> ring
  rw [hm]
  change _ ^2 + 0*_ - 0 - x - x = _
  simp only [zero_mul, add_zero, sub_zero, div_pow]
  rw [hs]
  generalize hd : 4*x^3-4*x+1 = d at hn ⊢
  field_simp [hn]
  rw [← hd]
  ring

theorem four_doubles :
    xCoord ((2 : ℕ) • P) = some 1 ∧ xCoord ((4 : ℕ) • P) = some 2 ∧
    xCoord ((8 : ℕ) • P) = some (21/25) ∧
    xCoord ((16 : ℕ) • P) = some (480106/4225) := by
  rw [mul_two, mul_four, mul_eight, mul_sixteen]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- The multiplicative height of the reduced x-coordinate, with infinity
assigned height one. -/
def height (Q : E.Point) : ℕ := match xCoord Q with
  | none => 1
  | some x => max x.num.natAbs x.den

theorem height_sixteen : height ((16 : ℕ) • P) = 480106 := by
  rw [mul_sixteen]
  change max (480106/4225 : ℚ).num.natAbs (480106/4225 : ℚ).den = 480106
  decide +kernel

noncomputable def logHeight (Q : E.Point) : ℝ := Real.logb 2 (height Q)

theorem logHeight_sixteen :
    18 < logHeight ((16 : ℤ) • P) ∧ logHeight ((16 : ℤ) • P) < 19 := by
  change 18 < Real.logb 2 (height ((16 : ℕ) • P)) ∧
    Real.logb 2 (height ((16 : ℕ) • P)) < 19
  rw [height_sixteen]
  constructor
  · apply (Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)).mpr
    norm_num
  · apply (Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)).mpr
    norm_num

theorem generator_bounds {α : ℝ}
    (hh : HeightWindow.QuadraticEstimate (fun j : ℤ => logHeight (j • P)) α) :
    1/20 < α ∧ α < 1/10 :=
  HeightWindow.generator_bounds hh logHeight_sixteen.1 logHeight_sixteen.2

private theorem monomial_bound {u v H : ℝ} (hu : |u| ≤ H) (hv : |v| ≤ H) (i j : ℕ) :
    |u^i*v^j| ≤ H^(i+j) := by
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hu i)
    (pow_le_pow_left₀ (abs_nonneg _) hv j) (by positivity)
    (pow_nonneg ((abs_nonneg _).trans hu) _)

/-- Bounds on both homogeneous coordinates before their common factor is
removed. The separate integer common-divisor theorem bounds it by 37. -/
theorem homogeneous_bounds (u v : ℝ) :
    let H := max |u| |v|
    let F := u^4+2*u^2*v^2-2*u*v^3+v^4
    let G := 4*u^3*v-4*u*v^3+v^4
    H^4/2 ≤ max |F| |G| ∧ max |F| |G| ≤ 9*H^4 := by
  dsimp only
  let H := max |u| |v|
  have hu : |u| ≤ H := le_max_left _ _
  have hv : |v| ≤ H := le_max_right _ _
  have hu4 : |u|^4 = u^4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hv4 : |v|^4 = v^4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hf₁ := sq_nonneg (u*v-v^2/2)
  have hf₂ := pow_nonneg (sq_nonneg u) 2
  have hf₃ := pow_nonneg (sq_nonneg v) 2
  constructor
  · refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_abs_self _)
    rcases le_total |u| |v| with h | h
    · rw [max_eq_right h, hv4]
      nlinarith
    · rw [max_eq_left h, hu4]
      nlinarith
  · have h40 := abs_le.mp (monomial_bound hu hv 4 0)
    have h31 := abs_le.mp (monomial_bound hu hv 3 1)
    have h22 := abs_le.mp (monomial_bound hu hv 2 2)
    have h13 := abs_le.mp (monomial_bound hu hv 1 3)
    have h04 := abs_le.mp (monomial_bound hu hv 0 4)
    norm_num at h40 h31 h22 h13 h04
    change _ ≤ 9 * H^4
    apply max_le <;> apply abs_le.mpr <;> constructor <;>
      linarith [h40.1,h40.2,h31.1,h31.2,h22.1,h22.2,h13.1,h13.2,h04.1,h04.2]

private def formF (u v : ℤ) := u^4+2*u^2*v^2-2*u*v^3+v^4
private def formG (u v : ℤ) := 4*u^3*v-4*u*v^3+v^4
private def raw (u v : ℤ) := max u.natAbs v.natAbs

private theorem raw_cast (u v : ℤ) : (raw u v : ℝ) = max |(u : ℝ)| |(v : ℝ)| := by
  simp [raw]

theorem reduced_scaling {f g : ℤ} {z : ℚ} (hg : g ≠ 0) (hz : z = (f : ℚ)/g) :
    ∃ k : ℤ, f = k*z.num ∧ g = k*z.den := by
  have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have hd : (z.den : ℚ) ≠ 0 := by exact_mod_cast z.den_ne_zero
  have hc := (div_eq_div_iff hd hg').mp (z.num_div_den.trans hz)
  have hi : z.num*g = f*(z.den : ℤ) := by exact_mod_cast hc
  have hnd : IsCoprime z.num (z.den : ℤ) := Int.isCoprime_iff_nat_coprime.mpr z.reduced
  have hdg : (z.den : ℤ) ∣ g :=
    hnd.symm.dvd_of_dvd_mul_left (show (z.den : ℤ) ∣ z.num*g by rw [hi]; exact dvd_mul_left _ _)
  obtain ⟨k, hk⟩ := hdg
  refine ⟨k, ?_, by linarith only [hk]⟩
  apply mul_left_cancel₀ (show (z.den : ℤ) ≠ 0 by exact_mod_cast z.den_ne_zero)
  rw [hk] at hi
  linarith only [hi]

private theorem projective_forms (x : ℚ) :
    formG x.num x.den ≠ 0 ∧
    (x^4+2*x^2-2*x+1)/(4*x^3-4*x+1) =
    (formF x.num x.den : ℚ)/(formG x.num x.den : ℚ) := by
  have hv : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hx : (x.num : ℚ) = x*x.den := (div_eq_iff hv).mp x.num_div_den
  have hF : (formF x.num x.den : ℚ) = (x^4+2*x^2-2*x+1)*(x.den : ℚ)^4 := by
    dsimp only [formF]
    push_cast
    rw [hx]
    ring
  have hG : (formG x.num x.den : ℚ) = (4*x^3-4*x+1)*(x.den : ℚ)^4 := by
    dsimp only [formG]
    push_cast
    rw [hx]
    ring
  refine ⟨?_, ?_⟩
  · exact_mod_cast (hG ▸ mul_ne_zero (cubic_ne_zero x) (pow_ne_zero 4 hv) :
      (formG x.num x.den : ℚ) ≠ 0)
  · rw [hF,hG]
    exact (mul_div_mul_right _ _ (pow_ne_zero 4 hv)).symm

/-- The height bound for every rational point of the actual curve,
including the point at infinity. -/
theorem doubling_height (Q : E.Point) :
    (height Q : ℝ)^4 / 74 ≤ height (Q+Q) ∧
    (height (Q+Q) : ℝ) ≤ 9*(height Q : ℝ)^4 := by
  cases Q with
  | zero =>
    have he : (Affine.Point.zero : E.Point) + Affine.Point.zero = Affine.Point.zero := zero_add _
    rw [he]
    norm_num [height,xCoord]
  | @some x y h =>
    let f := formF x.num x.den
    let g := formG x.num x.den
    let z := (x^4+2*x^2-2*x+1)/(4*x^3-4*x+1)
    obtain ⟨hg, hz⟩ := projective_forms x
    obtain ⟨k, hf, hgk⟩ := reduced_scaling hg hz
    have hk₀ : k ≠ 0 := by intro hk; rw [hk,zero_mul] at hgk; exact hg hgk
    have hk : k ∣ 37 := Pell.duplication_common_factor
      (Int.isCoprime_iff_nat_coprime.mpr x.reduced)
      ⟨z.num,hf⟩ ⟨z.den,hgk⟩
    have hk₁ : 1 ≤ k.natAbs := Int.natAbs_pos.mpr hk₀
    have hk₂ : k.natAbs ≤ 37 := Nat.le_of_dvd (by decide) (Int.natAbs_dvd_natAbs.mpr hk)
    have heq : raw f g = k.natAbs * raw z.num z.den := by
      dsimp only [f,g,raw]
      rw [hf,hgk,Int.natAbs_mul,Int.natAbs_mul,mul_max]
    have hnum :
        (raw x.num x.den : ℝ)^4/2 ≤ raw f g ∧
        (raw f g : ℝ) ≤ 9*(raw x.num x.den : ℝ)^4 := by
      simp only [raw_cast, f,g,formF,formG]
      push_cast
      exact homogeneous_bounds _ _
    have hlo : raw z.num z.den ≤ raw f g := by
      rw [heq]; simpa using Nat.mul_le_mul_right (raw z.num z.den) hk₁
    have hhi : raw f g ≤ 37 * raw z.num z.den := by
      rw [heq]; exact Nat.mul_le_mul_right _ hk₂
    have hcoord := double_x h
    have hnew : height (Affine.Point.some h + Affine.Point.some h) = raw z.num z.den := by
      simp [height,hcoord,raw,z]
    have hold : height (Affine.Point.some h) = raw x.num x.den := rfl
    rw [hold,hnew]
    have hlo' : (raw z.num z.den : ℝ) ≤ raw f g := by exact_mod_cast hlo
    have hhi' : (raw f g : ℝ) ≤ 37*(raw z.num z.den : ℝ) := by exact_mod_cast hhi
    constructor <;> linarith [hnum.1,hnum.2]

theorem height_pos (Q : E.Point) : 0 < height Q := by
  cases Q with
  | zero => decide
  | @some x y h => exact lt_of_lt_of_le x.den_pos (le_max_right _ _)

theorem doubling_logHeight (Q : E.Point) :
    |logHeight (Q+Q) - 4*logHeight Q| ≤ 12 := by
  have hp : 0 < (height Q : ℝ) := by exact_mod_cast height_pos Q
  have hp' : 0 < (height (Q+Q) : ℝ) := by exact_mod_cast height_pos (Q+Q)
  obtain ⟨hl, hu⟩ := doubling_height Q
  have h₁ := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hl
  have h₂ := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp' hu
  rw [Real.logb_div (by positivity) (by norm_num), Real.logb_pow] at h₁
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow] at h₂
  norm_num only [Nat.cast_ofNat] at h₁ h₂
  have h₃ : Real.logb 2 74 ≤ 12 := (Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)).mpr (by norm_num)
  have h₄ : Real.logb 2 9 ≤ 12 := (Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)).mpr (by norm_num)
  dsimp only [logHeight]
  apply abs_le.mpr
  constructor <;> linarith

private noncomputable def orbitHeight (Q : E.Point) (n : ℕ) : ℝ :=
  logHeight ((2^n : ℕ) • Q)

private theorem orbit_step (Q : E.Point) (n : ℕ) :
    |orbitHeight Q (n+1)-4*orbitHeight Q n| ≤ 12 := by
  dsimp only [orbitHeight]
  rw [pow_succ, Nat.mul_two, add_nsmul]
  exact doubling_logHeight ((2^n : ℕ) • Q)

/-- Canonical height in the draft's base-two normalization, obtained as
the limit along the actual doubling orbit. -/
noncomputable def canonicalHeight (Q : E.Point) : ℝ :=
  Classical.choose (HeightWindow.canonical_exists (orbit_step Q))

theorem canonical_limit (Q : E.Point) :
    Filter.Tendsto (fun n : ℕ => logHeight ((2^n : ℕ) • Q)/4^n)
      Filter.atTop (nhds (canonicalHeight Q)) :=
  Classical.choose_spec (HeightWindow.canonical_exists (orbit_step Q))

theorem canonical_comparison (Q : E.Point) :
    |logHeight Q - canonicalHeight Q| ≤ 4 := by
  have h := HeightWindow.canonical_error (orbit_step Q) (canonical_limit Q)
  simpa [orbitHeight] using h

/-- The adjacent-point height window from cyclicity and quadraticity, supplied by
`Curve37.rational_points_cyclic` and `Curve37.canonicalHeight_zsmul`. -/
theorem adjacent_height_window
    (hcyclic : ∀ Q : E.Point, ∃ j : ℤ, j • P = Q)
    (hquadratic : ∀ j : ℤ, canonicalHeight (j • P) = canonicalHeight P * (j : ℝ)^2)
    {L : ℝ} (hL : 1024 ≤ L) :
    (∃ Q : E.Point, L ≤ logHeight (Q+P) - logHeight Q ∧
      logHeight (Q+P) - logHeight Q ≤ 2*L) ∧
    ∀ Q : E.Point, L ≤ logHeight (Q+P) - logHeight Q →
      logHeight (Q+P) - logHeight Q ≤ 2*L →
      L^2/2 ≤ logHeight Q ∧ logHeight Q ≤ 45*L^2 := by
  have hh : HeightWindow.QuadraticEstimate (fun j : ℤ => logHeight (j • P)) (canonicalHeight P) := by
    intro j
    simpa [hquadratic j] using canonical_comparison (j • P)
  obtain ⟨ha, ha'⟩ := generator_bounds hh
  constructor
  · obtain ⟨j,hj⟩ := HeightWindow.exists_adjacent ha ha' hL hh
    exact ⟨j • P, by simpa [add_zsmul] using hj⟩
  · intro Q hlo hhi
    obtain ⟨j,rfl⟩ := hcyclic Q
    exact HeightWindow.bounds_of_adjacent ha ha' hL hh
      (by simpa [add_zsmul] using hlo) (by simpa [add_zsmul] using hhi)

end DiophantineNP.Curve37
