import DiophantineNP.Extraction
import DiophantineNP.Fourier

/-! # Arithmetic computation of a finite Laurent mean

A Laurent polynomial supported on `[-b,b]` is stored by the ordinary
coefficients of its shift by `X^b`. The same integer returned by the closed
radix formula is the normalized average on the complex roots of unity.
-/
namespace DiophantineNP.LaurentExtraction

open Extraction Finset
open scoped BigOperators

private theorem periodicSum_eq (cs : List ℤ) (m k n : ℕ) :
    periodicSum cs m k n = ∑ h ∈ range n,
      if m*h ≤ k then coefficient cs (k-m*h) else 0 := by
  induction n with
  | zero => simp [periodicSum]
  | succ n ih => rw [periodicSum, ih, sum_range_succ]

theorem sum_sampled_coefficients (cs : List ℤ) (b m : ℕ) (hm : 0 < m) (hb : m ∣ b) :
    periodicSum cs m (2*b) (2*b/m+1) =
      ∑ i ∈ range (2*b+1), if (m : ℤ) ∣ (i : ℤ)-(b : ℤ) then coefficient cs i else 0 := by
  rw [periodicSum_eq]
  conv_rhs => rw [← sum_filter]
  have hsmall (h : ℕ) (hh : h ∈ range (2*b/m+1)) : m*h ≤ 2*b := by
    have hle := Nat.le_of_lt_succ (mem_range.mp hh)
    simpa only [Nat.mul_comm h m] using (Nat.le_div_iff_mul_le hm).mp hle
  have hval (h : ℕ) (hh : h ∈ range (2*b/m+1)) :
      ((2*b-m*h : ℕ) : ℤ)-(b : ℤ) = (b : ℤ)-(m : ℤ)*(h : ℤ) := by
    rw [Int.ofNat_sub (hsmall h hh)]
    push_cast
    ring
  apply sum_bij (fun h _ => 2*b-m*h)
  · intro h hh
    apply mem_filter.mpr
    constructor
    · exact mem_range.mpr (by omega)
    · exact ((periodic_indices b m hm hb _).mpr ⟨h, Nat.le_of_lt_succ (mem_range.mp hh), hval h hh⟩).2.2
  · intro x hx y hy heq
    apply periodic_index_unique b m x y hm
    rw [← hval x hx, ← hval y hy, heq]
  · intro i hi
    obtain ⟨hi, hdvd⟩ := mem_filter.mp hi
    have hr := mem_range.mp hi
    obtain ⟨h,hbound,heq⟩ := (periodic_indices b m hm hb ((i:ℤ)-(b:ℤ))).mp ⟨by omega, by omega, hdvd⟩
    have hh : h ∈ range (2*b/m+1) := mem_range.mpr (by omega)
    refine ⟨h,hh,?_⟩
    have he := hval h hh
    omega
  · intro h hh; simp [hsmall h hh]

/-- The univariate specialization of the manuscript's cyclic-mean extraction,
including the equality to the complex mean. `cs` stores integral coefficients
indexed from degree `-b`. The hypotheses hold for its prescribed generous
positive radix. The evaluator on the left runs on positive integers alone. -/
theorem mean_from_integer_evaluation (cs : List ℤ) (m b : ℕ) [NeZero m]
    (hb : m ∣ b) (z : ℤ) (hz : 1 < z)
    (h : 2*((2*b/m+1 : ℕ)*mass cs) < z) :
    (extractCoefficient (evaluate z cs * ((z^(m*(2*b/m+1))-1)/(z^m-1))) z (2*b) : ℂ) =
    (m : ℂ)⁻¹ * (∑ k : ZMod m, ∑ i ∈ range (2*b+1), (coefficient cs i : ℂ) *
      ZMod.stdAddChar ((((i : ℤ)-(b : ℤ) : ℤ) : ZMod m) * k)) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [extract_periodic_quotient _ _ _ _ _ hm hz h, sum_sampled_coefficients _ _ _ hm hb]
  rw [Fourier.laurent_mean (range (2*b+1)) (fun i => (i:ℤ)-(b:ℤ)) (fun i => (coefficient cs i : ℂ))]
  push_cast
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- Clearing a positive rational coordinate at a signed Laurent exponent
leaves an integer factor. Its two exponents add to exactly twice the bound. -/
def coordinateFactor (p q G : ℕ) (e : ℤ) : ℕ :=
  p^((G : ℤ)+e).toNat * q^((G : ℤ)-e).toNat

theorem clear_coordinate (p q G : ℕ) (e : ℤ) (hp : 0 < p) (hq : 0 < q)
    (hlo : -(G : ℤ) ≤ e) (hhi : e ≤ G) :
    ((p : ℚ)*(q : ℚ))^G * ((p : ℚ)/(q : ℚ))^e = (coordinateFactor p q G e : ℚ) := by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [coordinateFactor, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, mul_pow, div_zpow,
    ← zpow_natCast (p : ℚ) (((G : ℤ) + e).toNat),
    ← zpow_natCast (q : ℚ) (((G : ℤ) - e).toNat),
    Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega),
    zpow_add₀ hp', zpow_sub₀ hq', zpow_natCast, zpow_natCast]
  ring

theorem coordinateFactor_bound (p q G : ℕ) (e : ℤ)
    (hlo : -(G : ℤ) ≤ e) (hhi : e ≤ G) :
    coordinateFactor p q G e ≤ (max p q)^(2*G) := by
  have hplus : ((G : ℤ)+e).toNat + ((G : ℤ)-e).toNat = 2*G := by omega
  rw [← hplus, pow_add, coordinateFactor]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left _ _) _)
    (Nat.pow_le_pow_left (le_max_right _ _) _)

/-- After specializing all remaining coordinates, a single multiplier works
for every monomial satisfying the common support bound. -/
theorem clear_monomial {k : ℕ} (p q : Fin k → ℕ) (G : ℕ) (e : Fin k → ℤ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (he : ∀ i, -(G : ℤ) ≤ e i ∧ e i ≤ G) :
    (∏ i, ((p i : ℚ)*(q i : ℚ))^G) * (∏ i, ((p i : ℚ)/(q i : ℚ))^(e i)) =
      (∏ i, coordinateFactor (p i) (q i) G (e i) : ℕ) := by
  rw [← prod_mul_distrib, Nat.cast_prod]
  exact prod_congr rfl fun i _ => clear_coordinate _ _ _ _ (hp _) (hq _) (he _).1 (he _).2

/-- A version of the manuscript's coefficient-mass estimate before equal
exponents are combined. Combining them can only reduce the sum of magnitudes. -/
theorem specialized_mass_le {ι : Type*} (s : Finset ι) {k : ℕ} (p q : Fin k → ℕ)
    (G : ℕ) (e : ι → Fin k → ℤ) (c : ι → ℤ)
    (he : ∀ j ∈ s, ∀ i, -(G : ℤ) ≤ e j i ∧ e j i ≤ G) :
    (∑ j ∈ s, |c j * ((∏ i, coordinateFactor (p i) (q i) G (e j i) : ℕ) : ℤ)|) ≤
      (∑ j ∈ s, |c j|) * ((∏ i, max (p i) (q i) ^ (2*G) : ℕ) : ℤ) := by
  rw [sum_mul]
  apply sum_le_sum
  intro j hj
  rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact Int.ofNat_le.mpr (prod_le_prod' fun i _ =>
    coordinateFactor_bound _ _ _ _ (he j hj i).1 (he j hj i).2)

end DiophantineNP.LaurentExtraction
