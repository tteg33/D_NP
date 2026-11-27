import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Log

/-! # The integer correction for geometric-series division

For a positive divisor `y`, choose `b` with `y ≤ b ≤ 2*y`. The intended
choice is the least power of two at least `y`. The approximation below
then needs just one comparison to recover the exact quotient.

This proves the arithmetic step in §3 of Hesse, Allender and Barrington,
*Uniform constant-depth threshold circuits for division and iterated
multiplication*. Constructing a fixed finite-logic formula for this
computation is a separate theorem. -/

namespace HABDivision

/-- The numerator for the first `n` terms of the reciprocal approximation,
with common denominator `b^n`. -/
def numerator (y b n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, (b - y)^i * b^(n - 1 - i)

/-- A division-free identity, valid also for an empty sum. -/
theorem numerator_identity {y b : ℕ} (hyb : y ≤ b) (n : ℕ) :
    numerator y b n * y + (b-y)^n = b^n := by
  have hb : y + (b-y) = b := by omega
  simpa only [numerator, hb, geom_sum₂_comm b (b-y) n] using
    (geom_sum₂_mul_add y (b-y) n)

/-- When `b` is a power of two, this last division is a binary shift. -/
def estimate (x y b n : ℕ) : ℕ := x * numerator y b n / b^n

/-- The estimate rounds down and its distance from the exact quotient is at most one. -/
theorem estimate_bounds {x y b n : ℕ} (hy : 0 < y) (hyb : y ≤ b)
    (hby : b ≤ 2*y) (hx : x < 2^n) :
    estimate x y b n ≤ x/y ∧ x/y ≤ estimate x y b n + 1 := by
  let s := numerator y b n
  let d := b^n
  let q := estimate x y b n
  have hd : 0 < d := pow_pos (hy.trans_le hyb) n
  have identity : s*y + (b-y)^n = d := numerator_identity hyb n
  have total : x*s*y + x*(b-y)^n = x*d := by
    rw [←identity]; ring
  have tail : x*(b-y)^n ≤ d := calc
    x*(b-y)^n ≤ 2^n * (b-y)^n := Nat.mul_le_mul_right _ hx.le
    _ = (2*(b-y))^n := (mul_pow ..).symm
    _ ≤ d := Nat.pow_le_pow_left (by omega) n
  have lo : q*d ≤ x*s := Nat.div_mul_le_self _ _
  have hi : x*s < (q+1)*d := by
    rw [Nat.mul_comm (q+1) d]
    exact Nat.lt_mul_div_succ (x*s) hd
  constructor
  · apply (Nat.le_div_iff_mul_le hy).mpr
    apply Nat.le_of_mul_le_mul_right (c := d) _ hd
    calc
      q*y*d = q*d*y := by ring
      _ ≤ x*s*y := Nat.mul_le_mul_right _ lo
      _ ≤ x*d := by omega
  · apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hy).mpr
    apply Nat.lt_of_mul_lt_mul_right (a := d)
    calc
      x*d = x*s*y + x*(b-y)^n := total.symm
      _ < (q+1)*d*y + d := Nat.add_lt_add_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hi hy) tail
      _ ≤ (q+1)*d*y + d*y := Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hy) _
      _ = (q+1+1)*y*d := by ring

/-- The exact floor quotient, including the cases `x=0`, `y=1`, and `x<y`. -/
theorem corrected_quotient {x y b n : ℕ} (hy : 0 < y) (hyb : y ≤ b)
    (hby : b ≤ 2*y) (hx : x < 2^n) :
    (let q := estimate x y b n
     if (q+1)*y ≤ x then q+1 else q) = x/y := by
  obtain ⟨lo,hi⟩ := estimate_bounds hy hyb hby hx
  dsimp only
  split <;> rename_i h
  · exact Nat.le_antisymm ((Nat.le_div_iff_mul_le hy).mpr h) hi
  · have below : ¬ (estimate x y b n + 1 ≤ x/y) := by
      intro hq
      exact h ((Nat.le_div_iff_mul_le hy).mp hq)
    omega

/-- The least power of two above a positive divisor meets both normalization bounds. -/
theorem binary_scale_bounds {y : ℕ} (hy : 0 < y) :
    y ≤ 2^(Nat.clog 2 y) ∧ 2^(Nat.clog 2 y) ≤ 2*y := by
  refine ⟨Nat.le_pow_clog (by decide) y, ?_⟩
  cases hj : Nat.clog 2 y with
  | zero => simp; omega
  | succ j =>
    have hlt : j < Nat.clog 2 y := hj ▸ Nat.lt_succ_self j
    have hpow : 2^j < y := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp hlt
    rw [pow_succ]; omega

/-- A single right shift produces the preliminary quotient. One comparison then suffices
for every positive divisor and every dividend of at most `n` bits. -/
theorem binary_quotient {x y n : ℕ} (hy : 0 < y) (hx : x < 2^n) :
    (let j := Nat.clog 2 y
     let b := 2^j
     let q := (x * numerator y b n) >>> (j*n)
     if (q+1)*y ≤ x then q+1 else q) = x/y := by
  obtain ⟨lo,hi⟩ := binary_scale_bounds hy
  simpa only [estimate, Nat.shiftRight_eq_div_pow, pow_mul] using
    (corrected_quotient hy lo hi hx)

end HABDivision
