import DiophantineNP.Curve37

/-! # Size of the reduced y-coordinate on curve 37a1

This supplies the coordinate-size estimate for the existential elliptic height
tests in Appendix A. The height of a rational uses the reduced numerator and
positive denominator. The statements below therefore bound the actual integer
coordinates that the graph stores.
-/

namespace DiophantineNP.Curve37

open WeierstrassCurve

def rationalHeight (z : ℚ) : ℕ := max z.num.natAbs z.den

/-- Reducing a nonzero-denominator integer fraction can only decrease the
absolute numerator and denominator, individually. -/
theorem reduced_coordinates_le {a b : ℤ} {z : ℚ} (hb : b ≠ 0) (hz : z = (a : ℚ)/b) :
    z.num.natAbs ≤ a.natAbs ∧ z.den ≤ b.natAbs := by
  obtain ⟨k, ha, hb'⟩ := reduced_scaling hb hz
  have hk : k ≠ 0 := by rintro rfl; exact hb (by simpa only [zero_mul] using hb')
  have hk' : 1 ≤ k.natAbs := by exact Nat.pos_of_ne_zero (by simpa using hk)
  rw [ha, hb', Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]
  exact ⟨by simpa using Nat.mul_le_mul_right z.num.natAbs hk',
    by simpa using Nat.mul_le_mul_right z.den hk'⟩

private def cubicNumerator (u v : ℤ) : ℤ := 4*u^3-4*u*v^2+v^3

private theorem cubic_mass (x : ℚ) :
    (cubicNumerator x.num x.den).natAbs ≤ 9*(rationalHeight x)^3 := by
  let u := x.num
  let v : ℤ := x.den
  let H := rationalHeight x
  have hu : u.natAbs ≤ H := le_max_left ..
  have hv : v.natAbs ≤ H := by simp [v,H,rationalHeight]
  have ha := Nat.pow_le_pow_left hu 3
  have hb := Nat.mul_le_mul hu (Nat.pow_le_pow_left hv 2)
  have hc := Nat.pow_le_pow_left hv 3
  calc
    _ ≤ (4*u^3).natAbs + (4*u*v^2).natAbs + (v^3).natAbs :=
      (Int.natAbs_add_le _ _).trans (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _)
    _ = 4*u.natAbs^3 + 4*u.natAbs*v.natAbs^2 + v.natAbs^3 := by
      simp only [Int.natAbs_mul, Int.natAbs_pow]; rfl
    _ ≤ 9*H^3 := by nlinarith only [ha,hb,hc]

/-- The numerator and denominator of `2y+1` have controlled squares. -/
theorem completed_square_coordinate_bounds {x y : ℚ} (h : y^2+y=x^3-x) :
    (2*y+1).num.natAbs^2 ≤ 9*(rationalHeight x)^3 ∧
    (2*y+1).den^2 ≤ (rationalHeight x)^3 := by
  let v : ℤ := x.den
  have hv : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hx : (x.num : ℚ) = x*x.den := (div_eq_iff hv).mp x.num_div_den
  have heq : (2*y+1)^2 = (cubicNumerator x.num v : ℚ)/(v^3 : ℤ) := by
    apply (eq_div_iff (by dsimp [v]; exact_mod_cast pow_ne_zero 3 x.den_ne_zero)).2
    dsimp [v, cubicNumerator]
    push_cast
    rw [hx]
    linear_combination 4 * (x.den : ℚ)^3 * h
  have hv0 : v^3 ≠ 0 := pow_ne_zero 3 (by dsimp [v]; exact_mod_cast x.den_ne_zero)
  obtain ⟨hnum, hden⟩ := reduced_coordinates_le hv0 heq
  rw [Rat.num_pow, Int.natAbs_pow] at hnum
  simp only [Rat.den_pow, Int.natAbs_pow, v, Int.natAbs_natCast] at hden
  exact ⟨hnum.trans (cubic_mass x), hden.trans (Nat.pow_le_pow_left (le_max_right ..) 3)⟩

/-- Both reduced integer coordinates of `y` have at most a constant times
the bit length of the reduced `x`. The displayed squared-height estimate is
uniform on the entire affine curve. -/
theorem y_height_squared {x y : ℚ} (h : y^2+y=x^3-x) :
    (rationalHeight y)^2 ≤ 20*(rationalHeight x)^3 := by
  let z := 2*y+1
  have hd : (z.den : ℚ) ≠ 0 := by exact_mod_cast z.den_ne_zero
  have hnum : (z.num : ℚ) = z*z.den := (div_eq_iff hd).mp z.num_div_den
  have hrep : y = ((z.num-(z.den:ℤ) : ℤ):ℚ)/((2*(z.den:ℤ):ℤ):ℚ) := by
    push_cast
    apply (eq_div_iff (mul_ne_zero (by norm_num) hd)).2
    rw [hnum]
    dsimp [z]
    ring
  have hd' : (2:ℤ)*z.den ≠ 0 := mul_ne_zero (by decide) (by exact_mod_cast z.den_ne_zero)
  obtain ⟨ha, hb⟩ := reduced_coordinates_le hd' hrep
  have hs := completed_square_coordinate_bounds h
  change z.num.natAbs^2 ≤ _ ∧ z.den^2 ≤ _ at hs
  have hy : y.num.natAbs ≤ z.num.natAbs + z.den :=
    ha.trans (by simpa using Int.natAbs_sub_le z.num (z.den:ℤ))
  have hy' : y.den ≤ 2*z.den := by simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hb
  change (max y.num.natAbs y.den)^2 ≤ 20*(rationalHeight x)^3
  rcases le_total y.den y.num.natAbs with hmax | hmax
  · rw [max_eq_left hmax]
    have hadd : (z.num.natAbs + z.den)^2 ≤ 2*(z.num.natAbs^2 + z.den^2) := by
      have hh := sq_nonneg (|z.num| - (z.den : ℤ))
      zify
      nlinarith
    exact (Nat.pow_le_pow_left hy 2).trans (hadd.trans (by nlinarith only [hs.1,hs.2]))
  · rw [max_eq_right hmax]
    exact (Nat.pow_le_pow_left hy' 2).trans (by nlinarith only [hs.2])

/-- Specialization to mathlib's nonsingular point and the draft's projective x-height. -/
theorem y_coordinate_size {x y : ℚ} (h : E.Nonsingular x y) :
    (max y.num.natAbs y.den)^2 ≤ 20*(height (Affine.Point.some h))^3 := by
  apply y_height_squared
  have he := (Affine.equation_iff x y).mp ((Affine.nonsingular_iff x y).mp h).1
  dsimp [E] at he
  linarith only [he]

/-- If the x-height fits in `L` bits, each magnitude stored for the y-coordinate
fits in `3*L+5` bits. This directly supplies a linear bit budget. -/
theorem y_coordinate_fits {x y : ℚ} (h : E.Nonsingular x y) {L : ℕ}
    (hx : height (Affine.Point.some h) < 2^L) :
    max y.num.natAbs y.den < 2^(3*L+5) := by
  let H := height (Affine.Point.some h)
  have hy := (Nat.le_self_pow (n := 2) (by decide) (max y.num.natAbs y.den)).trans
    (y_coordinate_size h)
  have hh := Nat.pow_le_pow_left hx.le 3
  have hp : 0 < (2^L : ℕ)^3 := by positivity
  have hr : (2 : ℕ)^(3*L+5) = 32*(2^L)^3 := by
    rw [pow_add, Nat.mul_comm 3 L, pow_mul]
    ring
  rw [hr]
  nlinarith only [hy,hh,hp]

end DiophantineNP.Curve37
