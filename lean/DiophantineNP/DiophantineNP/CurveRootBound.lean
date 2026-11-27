import DiophantineNP.Curve37

/-! # Bounding the heights of two rational roots by their quadratic

The product of the reduced denominators divides the leading coefficient.
The middle coefficient controls the mixed numerator-denominator products.
-/
namespace DiophantineNP.Curve37

private theorem quadratic_factors {A B C u v j k : ℤ} (hv : v ≠ 0) (hk : k ≠ 0)
    (huv : IsCoprime u v) (hjk : IsCoprime j k)
    (hs : A * (u*k+v*j) = B * (v*k)) (hp : A*(u*j) = C*(v*k)) :
    ∃ m : ℤ, A=m*(v*k) ∧ B=m*(u*k+v*j) ∧ C=m*(u*j) := by
  have hvdiv : v ∣ A := by
    apply (huv.symm.mul_right huv.symm).dvd_of_dvd_mul_right
    refine ⟨B*u-C*v, ?_⟩
    apply mul_right_cancel₀ hk
    linear_combination u * hs - v * hp
  obtain ⟨g,hg⟩ := hvdiv
  have ss : g * (u*k+v*j) = B*k := by
    apply mul_left_cancel₀ hv
    rw [hg] at hs
    linear_combination hs
  have pp : g*(u*j) = C*k := by
    apply mul_left_cancel₀ hv
    rw [hg] at hp
    linear_combination hp
  have ku : k ∣ g*u := hjk.symm.dvd_of_dvd_mul_right ⟨C, by linear_combination pp⟩
  have kv : k ∣ g*v := hjk.symm.dvd_of_dvd_mul_right ⟨B-g*u, by linear_combination ss⟩
  obtain ⟨d,e,h⟩ := huv
  have kg : k ∣ g := by
    convert dvd_add (ku.mul_left d) (kv.mul_left e) using 1
    linear_combination -g * h
  obtain ⟨m,hm⟩ := kg
  refine ⟨m, by rw [hg,hm]; ring, ?_, ?_⟩
  · apply mul_right_cancel₀ hk
    rw [hm] at ss
    linear_combination -ss
  · apply mul_right_cancel₀ hk
    rw [hm] at pp
    linear_combination -pp

private theorem raw_height_bound (u j : ℤ) (v k : ℕ) :
    max u.natAbs v * max j.natAbs k ≤
      2 * max (v*k) (max (u*(k:ℤ)+(v:ℤ)*j).natAbs (u*j).natAbs) := by
  let H := max (v*k) (max (u*(k:ℤ)+(v:ℤ)*j).natAbs (u*j).natAbs)
  have hh₁ : v*k ≤ H := le_max_left .. 
  have hh₂ : (u*(k:ℤ)+(v:ℤ)*j).natAbs ≤ H := (le_max_left ..).trans (le_max_right ..)
  have hh₃ : u.natAbs*j.natAbs ≤ H := by
    rw [← Int.natAbs_mul]
    exact (le_max_right ..).trans (le_max_right ..)
  change _ ≤ 2*H
  by_cases hx : u.natAbs ≤ v <;> by_cases hy : j.natAbs ≤ k
  · rw [max_eq_right hx, max_eq_right hy]; omega
  · rw [max_eq_right hx, max_eq_left (by omega : k ≤ j.natAbs)]
    have h := Int.natAbs_add_le (u*(k:ℤ)+(v:ℤ)*j) (-(u*(k:ℤ)))
    rw [show u*(k:ℤ)+(v:ℤ)*j+ -(u*(k:ℤ)) = (v:ℤ)*j by ring] at h
    simp only [Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_natCast] at h
    have := (Nat.mul_le_mul_right k hx).trans hh₁
    omega
  · rw [max_eq_left (by omega : v ≤ u.natAbs), max_eq_right hy]
    have h := Int.natAbs_add_le (u*(k:ℤ)+(v:ℤ)*j) (-((v:ℤ)*j))
    rw [show u*(k:ℤ)+(v:ℤ)*j+ -((v:ℤ)*j) = u*(k:ℤ) by ring] at h
    simp only [Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_natCast] at h
    have := (Nat.mul_le_mul_left v hy).trans hh₁
    omega
  · rw [max_eq_left (by omega : v ≤ u.natAbs), max_eq_left (by omega : k ≤ j.natAbs)]; omega

/-- The product of the naive multiplicative heights of the two rational
roots of a quadratic is bounded by twice its largest coefficient magnitude. -/
theorem root_height_product {A B C : ℤ} {r t : ℚ} (hA : A ≠ 0)
    (hs : (A:ℚ)*(r+t) = B) (hp : (A:ℚ)*(r*t) = C) :
    max r.num.natAbs r.den * max t.num.natAbs t.den ≤ 2 * max A.natAbs (max B.natAbs C.natAbs) := by
  have hv : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hk : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_ne_zero
  have es : A*(r.num*(t.den:ℤ)+(r.den:ℤ)*t.num) = B*((r.den:ℤ)*(t.den:ℤ)) := by
    rw [← r.num_div_den, ← t.num_div_den] at hs
    field_simp [hv,hk] at hs
    exact_mod_cast (by linear_combination hs : (A:ℚ) * ((r.num:ℚ)*(t.den:ℚ)+(r.den:ℚ)*(t.num:ℚ)) =
      (B:ℚ)*((r.den:ℚ)*(t.den:ℚ)))
  have ep : A*(r.num*t.num) = C*((r.den:ℤ)*(t.den:ℤ)) := by
    rw [← r.num_div_den, ← t.num_div_den] at hp
    field_simp [hv,hk] at hp
    exact_mod_cast (by linear_combination hp : (A:ℚ) * ((r.num:ℚ)*(t.num:ℚ)) =
      (C:ℚ)*((r.den:ℚ)*(t.den:ℚ)))
  obtain ⟨m,ha,hb,hc⟩ := quadratic_factors (by exact_mod_cast r.den_ne_zero)
    (by exact_mod_cast t.den_ne_zero) (Int.isCoprime_iff_nat_coprime.mpr r.reduced)
    (Int.isCoprime_iff_nat_coprime.mpr t.reduced) es ep
  have hm : m ≠ 0 := by rintro rfl; simp [ha] at hA
  have mono (z : ℤ) : z.natAbs ≤ (m*z).natAbs := by
    rw [Int.natAbs_mul]; exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hm)
  refine (raw_height_bound _ _ _ _).trans (Nat.mul_le_mul_left 2 (max_le_max ?_ (max_le_max ?_ ?_)))
  · simpa only [ha, Int.natAbs_mul,Int.natAbs_natCast] using mono ((r.den:ℤ)*(t.den:ℤ))
  · simpa only [hb] using mono (r.num*(t.den:ℤ)+(r.den:ℤ)*t.num)
  · simpa only [hc] using mono (r.num*t.num)

end DiophantineNP.Curve37
