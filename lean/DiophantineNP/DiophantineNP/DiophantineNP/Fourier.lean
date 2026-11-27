import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact Fourier steps of the finite-arithmetic packing construction

All Fourier sums here range over the complete residue system `ZMod J`.
This treats every frequency once, including when the period is composite.
The manuscript uses the centered representatives when `J = 2*B+1`.
-/

namespace DiophantineNP.Fourier

open scoped BigOperators
open Finset

/-- Exact unnormalized character sum. The test is equality in the residue ring,
so it applies to signed Laurent exponents after casting them to this ring. -/
theorem character_sum {J : ℕ} [NeZero J] (t : ZMod J) :
    (∑ k : ZMod J, ZMod.stdAddChar (t * k)) = if t = 0 then (J : ℂ) else 0 := by
  by_cases h : t = 0
  · simp [h, AddChar.map_zero_eq_one, ZMod.card]
  · rw [if_neg h]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar J h)

/-- Summing a Laurent expression on the cyclic grid kills precisely the
nonmultiples of its period. Distinct terms may have the same exponent. -/
theorem cyclic_filter {J : ℕ} [NeZero J] {ι : Type*}
    (s : Finset ι) (e : ι → ℤ) (c : ι → ℂ) :
    (∑ k : ZMod J, ∑ m ∈ s, c m * ZMod.stdAddChar ((e m : ZMod J) * k)) =
      (J : ℂ) * ∑ m ∈ s, if (e m : ZMod J) = 0 then c m else 0 := by
  classical
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.mul_sum, character_sum]
  by_cases h : (e m : ZMod J) = 0 <;> simp [h, mul_comm]

/-- The normalized form of the same identity states the paper's divisibility
filter on integer Laurent exponents. -/
theorem laurent_mean {J : ℕ} [NeZero J] {ι : Type*}
    (s : Finset ι) (e : ι → ℤ) (c : ι → ℂ) :
    (J : ℂ)⁻¹ * (∑ k : ZMod J, ∑ m ∈ s,
       c m * ZMod.stdAddChar ((e m : ZMod J) * k)) =
       ∑ m ∈ s, if (J : ℤ) ∣ e m then c m else 0 := by
  rw [cyclic_filter, ← mul_assoc, inv_mul_cancel₀ (NeZero.ne (J : ℂ)), one_mul]
  simp_rw [ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- At either sign of a selected arc, exact phases isolate the desired
coefficient. The integer-division selector identifies the exponent in the
paper's summand with the residue of this product. -/
theorem signed_weight {J : ℕ} [NeZero J] (reversed : Bool)
    (c : ZMod J → ℂ) (i : ZMod J) :
    (∑ k : ZMod J, ∑ b : ZMod J, c b *
        ZMod.stdAddChar ((if reversed then -(i-b) else i-b) * k)) = (J : ℂ) * c i := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, character_sum]
  have h (b : ZMod J) : (if reversed then -(i-b) else i-b) = 0 ↔ i = b := by
    cases reversed <;> simp [sub_eq_zero, eq_comm]
  simp_rw [h]
  simp [mul_ite, mul_comm]

/-- Removing the quotient term is valid inside the character because its
coefficient is the whole period. Here all four word labels are signed. -/
theorem balanced_phase {J : ℕ} (i k q t b : ℤ) (h : i*k = (J:ℤ)*q+t) :
    ((t-b*k : ℤ) : ZMod J) = ((i-b : ℤ) : ZMod J) * (k : ZMod J) := by
  have hc := congrArg (fun x : ℤ => (x : ZMod J)) h
  push_cast at hc ⊢
  simp at hc
  rw [← hc]
  ring

/-- The manuscript's binary-weight identity, in standard-character notation.
The forward and inverse transforms have opposite signs. -/
theorem binary_weight_inversion {J : ℕ} [NeZero J] (i : ZMod J) :
    (J : ℂ)⁻¹ * (∑ k : ZMod J, ZMod.stdAddChar (k * i) *
      ∑ b : ZMod J, ZMod.stdAddChar (-(b * k)) * (2 : ℂ) ^ b.val) =
      (2 : ℂ) ^ i.val := by
  let f : ZMod J → ℂ := fun b => 2 ^ b.val
  have h := congrFun (ZMod.dft.symm_apply_apply f) i
  simpa only [ZMod.invDFT_apply, ZMod.dft_apply, smul_eq_mul, f] using h

/-- This is the ideal (exact-selector) weighted sum on a truth set. -/
theorem packed_weight_inversion {J : ℕ} [NeZero J] (truth : Finset (ZMod J)) :
    (∑ i ∈ truth, (J : ℂ)⁻¹ * (∑ k : ZMod J, ZMod.stdAddChar (k * i) *
      ∑ b : ZMod J, ZMod.stdAddChar (-(b * k)) * (2 : ℂ) ^ b.val)) =
      ∑ i ∈ truth, (2 : ℂ) ^ i.val :=
  Finset.sum_congr rfl fun i _ => binary_weight_inversion i

/-- Every integer has exactly one quotient and centered remainder for the
positive odd modulus `2*B+1`. The pair is ordered as (quotient, remainder). -/
theorem balanced_division (B p : ℤ) (hB : 0 ≤ B) :
    ∃! qt : ℤ × ℤ,
      -B ≤ qt.2 ∧ qt.2 ≤ B ∧ p = (2 * B + 1) * qt.1 + qt.2 := by
  let J := 2 * B + 1
  have hJ : 0 < J := by dsimp [J]; omega
  refine ⟨((p + B) / J, (p + B) % J - B), ?_, ?_⟩
  · have h0 := Int.emod_nonneg (p + B) hJ.ne'
    have h1 := Int.emod_lt_of_pos (p + B) hJ
    have h2 := Int.mul_ediv_add_emod (p + B) J
    dsimp only
    change -B ≤ (p + B) % J - B ∧ (p + B) % J - B ≤ B ∧
      p = J * ((p + B) / J) + ((p + B) % J - B)
    exact ⟨by omega, by have hdef : J = 2*B+1 := rfl; omega, by omega⟩
  · rintro ⟨q,t⟩ ⟨hlo,hhi,he⟩
    change -B ≤ t at hlo
    change t ≤ B at hhi
    change p = J * q + t at he
    have hdiv : (p + B) / J = q ∧ (p + B) % J = t + B := by
      apply (Int.ediv_emod_unique hJ).2
      exact ⟨by omega, by omega, by dsimp [J]; omega⟩
    exact Prod.ext hdiv.1.symm (by dsimp only; omega)

/-- The quotient coordinate selected by the Fourier kernel also fits the
centered label window. This includes both signs of the frequency. -/
theorem balanced_quotient_bounds (B p q t : ℤ) (hB : 0 ≤ B)
    (hp : - (B * B) ≤ p ∧ p ≤ B * B) (ht : -B ≤ t ∧ t ≤ B)
    (he : p = (2 * B + 1) * q + t) : -B ≤ q ∧ q ≤ B := by
  have hJ : 0 ≤ 2 * B + 1 := by omega
  constructor
  · by_contra! hn
    have hq : q ≤ -B - 1 := by omega
    have hm := mul_le_mul_of_nonneg_left hq hJ
    nlinarith [hp.1, ht.2, sq_nonneg B]
  · by_contra! hn
    have hq : B + 1 ≤ q := by omega
    have hm := mul_le_mul_of_nonneg_left hq hJ
    nlinarith [hp.2, ht.1, sq_nonneg B]

/-- A finite product of selectors of absolute value at most one accumulates
at most one copy of the pointwise error per factor. At seven factors this is
the estimate used just before rounding the four-coordinate sum. -/
theorem selector_product_error {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (ε : ℝ) (hf : ∀ j, |f j| ≤ 1) (hg : ∀ j, |g j| ≤ 1)
    (herr : ∀ j, |f j - g j| ≤ ε) :
    |(∏ j ∈ s, f j) - ∏ j ∈ s, g j| ≤ (s.card : ℝ) * ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hp : |∏ j ∈ s, g j| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ => hg j)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      _ = |f a * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j) +
          (f a - g a) * ∏ j ∈ s, g j| := by congr 1; ring
      _ ≤ |f a| * |(∏ j ∈ s, f j) - ∏ j ∈ s, g j| +
          |f a - g a| * |∏ j ∈ s, g j| := by
            simpa only [abs_mul] using abs_add_le
              (f a * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j))
              ((f a - g a) * ∏ j ∈ s, g j)
      _ ≤ 1 * ((s.card : ℝ) * ε) + ε * 1 :=
        add_le_add (mul_le_mul (hf a) ih (abs_nonneg _) zero_le_one)
          (mul_le_mul (herr a) hp (abs_nonneg _) ((abs_nonneg _).trans (herr a)))
      _ = _ := by push_cast; ring

end DiophantineNP.Fourier
