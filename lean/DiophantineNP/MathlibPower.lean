import Mathlib.NumberTheory.PellMatiyasevic

/-! # Why mathlib's unbounded power graph does not discharge the size estimate

In the positive branch of `Pell.eq_pow_of_pell`, `w` is at least the base
and a nontrivial Pell point has second coordinate divisible by `w`.
This forces a large witness even for exponent one.
-/

namespace DiophantineNP.MathlibPower

theorem outer_witness_lower_bound {g w a z : ℕ} (hg : 0 < g) (hw : g ≤ w)
    (ha : 1 < a) (h : a*a - ((w+1)*(w+1)-1)*(w*z)*(w*z) = 1) :
    (g+1)^g ≤ a := by
  have hwp : 0 < w := by omega
  have hw1 : 1 < w+1 := by omega
  obtain ⟨j, rfl, hy⟩ := Pell.eq_pell hw1 h
  have hj : 0 < j := by
    by_contra! hn
    have he : j = 0 := by omega
    rw [he, Pell.xn_zero] at ha
    omega
  have hwj : w ≤ j :=
    Nat.le_of_dvd hj
      (Nat.modEq_zero_iff_dvd.1 ((Pell.yn_modEq_a_sub_one hw1 j).symm.trans
        (Nat.modEq_zero_iff_dvd.2 ⟨z,hy.symm⟩)))
  calc
    (g+1)^g ≤ (w+1)^g := Nat.pow_le_pow_left (by omega) _
    _ ≤ (w+1)^j := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ Pell.xn hw1 j := Pell.xn_ge_a_pow hw1 j

/-- Take native base and output both `2^N`, with exponent one. The witness
`a` alone needs at least `N * 2^N + 1` bits. -/
theorem exponential_witness (N w a z : ℕ) (hw : 2^N ≤ w) (ha : 1 < a)
    (h : a*a - ((w+1)*(w+1)-1)*(w*z)*(w*z) = 1) :
    N * 2^N ≤ a.log2 := by
  have hbig := outer_witness_lower_bound (Nat.two_pow_pos N) hw ha h
  have he : 2^(N*2^N) ≤ a := by
    rw [pow_mul]
    exact (Nat.pow_le_pow_left (Nat.le_succ (2^N)) (2^N)).trans hbig
  exact (Nat.le_log2 (by omega)).2 he

end DiophantineNP.MathlibPower
