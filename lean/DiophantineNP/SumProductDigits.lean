import DiophantineNP.WidthFormulaTools

/-! # Recovering the bits of a sum from one product

In base B the coefficient of degree one in the product of (1+B fᵢ)
is the sum of the fᵢ. The higher terms contribute only multiples of B².
-/
namespace DiophantineNP.SumProductDigits
open WidthFormula

theorem product_expansion (f : ℕ → ℕ) (B U : ℕ) :
    ∃ q, productPrefix (fun i => 1+B*f i) U = 1+B*(Readout.prefixSum f U+B*q) := by
  induction U with
  | zero => exact ⟨0, by simp [productPrefix,Readout.prefixSum]⟩
  | succ U ih =>
    obtain ⟨q,hq⟩ := ih
    refine ⟨q + (Readout.prefixSum f U + B*q)*f U, ?_⟩
    rw [product_succ, hq, Readout.prefixSum]
    ring

theorem product_sum_digit (f : ℕ → ℕ) (U s h : ℕ) (hs : 0 < s) (hj : h < s) :
    (productPrefix (fun i => 1+2^s*f i) U).testBit (s+h) =
      (Readout.prefixSum f U).testBit h := by
  obtain ⟨q, hq⟩ := product_expansion f (2^s) U
  have hb := Nat.one_lt_two_pow (by omega : s ≠ 0)
  rw [hq, Nat.add_comm s h, Nat.testBit_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos s),
    Nat.div_eq_of_lt hb, Nat.zero_add]
  rw [← show ((Readout.prefixSum f U+2^s*q)%2^s).testBit h =
       (Readout.prefixSum f U+2^s*q).testBit h by rw [Nat.testBit_mod_two_pow]; simp [hj]]
  simp [Nat.add_mul_mod_self_left, Nat.testBit_mod_two_pow, hj]

end DiophantineNP.SumProductDigits
