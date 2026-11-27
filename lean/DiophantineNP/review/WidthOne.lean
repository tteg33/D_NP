import DiophantineNP.ModularVerifier

/-! # An explicit width-one witness for the modular polynomial

For `a = b = 1`, the five inputs are `(1, 1, 4782969, 597871, 8)`. The 17
coordinates below solve its equations and cost 185 bits in total. The full
two-input verifier also certifies the three width parameters internally.
-/

namespace Review.WidthOne

open DiophantineNP ModularPolynomial WidthData
open private polynomial_zero_iff System from DiophantineNP.ModularPolynomial

def witness : Fin 17 → ℕ :=
  ![1, 1, 597871, 597871, 0, 0, 0, 0, 0, 4782967, 4782967, 4185097, 4185097,
    1, 4782967, 1, 4782967]

theorem width_modulus : widthD 1 = 4782969 := by
  norm_num [widthD, widthFactor, List.range_succ, Nat.nth_prime_one_eq_three]

theorem width_multiplier : widthJ 1 = 597871 := by
  norm_num [widthJ, Readout.prefixSum, Readout.weight, width_modulus, widthFactor, scale,
    Nat.nth_prime_one_eq_three]

theorem concrete_certificate :
    natCost witness = 185 ∧ scale 1 = 8 ∧
      MvPolynomial.eval (assignment 1 1 (widthD 1) (widthJ 1) (scale 1) witness)
        polynomial = 0 := by
  refine ⟨by decide, by decide, ?_⟩
  rw [width_modulus, width_multiplier]
  apply (polynomial_zero_iff ..).mpr
  unfold System
  decide

#print axioms concrete_certificate

end Review.WidthOne
