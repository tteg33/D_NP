import DiophantineNP.SmallSumTemplate

/-! # Both width descriptions from one iterated-product formula

The total sum defining the CRT multiplier fits in the lower half of the
product template's word. Consequently its exact bits are supplied by
the first-order coefficient of a product.
-/
namespace DiophantineNP.FiniteArithmeticGap
open WidthFormula WidthData Counting Packing

private def nativeBits : BitTemplate where
  nativeBit := bitAt 0 1
  bit_correct := fun x j => bitAt_eval 0 1 (pairEnv x j)

def ProductTemplate.operations (A : ProductTemplate) : ProductArithmetic where
  bit := bitAt
  bit_spec := bitAt_eval
  product j input := substitute nativeBits input A.product (fun _ => j) id
  product_spec j input env f fits correct := by
    rw [substitute_eval]
    change A.product.eval (fun r c => input.eval (extend c r env)) (fun _ => env j) = _
    have h : (fun r c => input.eval (extend c r env)) = fun r c => (f r.val).testBit c.val :=
      funext fun r => funext fun c => correct c r
    rw [h, A.product_correct f fits]

theorem widthJ_fits_half (n : ℕ) (hn : 0 < n) : widthJ n < 2^(universeSize n/2) := by
  have h : 40 ≤ (n+2)^6 := le_trans (by decide : 40 ≤ 2^6) (Nat.pow_le_pow_left (by omega) _)
  have hcap : 40*(n+2)^3 ≤ universeSize n := calc
    _ ≤ (n+2)^6 * (n+2)^3 := Nat.mul_le_mul_right _ h
    _ = (n+2)^9 := (pow_add _ 6 3).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide : 9 ≤ 20)
  have hh : 20*(n+2)^3 ≤ universeSize n/2 := by omega
  exact (widthJ_lt_D n hn).trans_le ((widthD_bound n).trans (Nat.pow_le_pow_right (by decide) hh))

theorem ProductTemplate.widthDescriptions (A : ProductTemplate) : WidthDescriptions := by
  constructor
  · refine ⟨productBit A.operations 0 1 none, ?_⟩
    intro n _ j
    exact fullProduct_spec _ 0 1 (Fin.cases j (widthParam n)) rfl
  · let row := JRow A.operations (1 : Fin 2)
    refine ⟨substitute nativeBits row A.smallSum (fun _ => (0:Fin 2)) id, ?_⟩
    intro n hn j
    let env : Fin 2 → Fin (universeSize n) := Fin.cases j (widthParam n)
    rw [substitute_eval]
    change A.smallSum.eval (fun r c => row.eval (extend c r env)) (fun _ => j) = _
    have table : (fun r c => row.eval (extend c r env)) =
        (fun r c : Fin (universeSize n) => (paddedJRow n r.val).testBit c.val) := by
      funext r c
      exact JRow_spec _ 1 env rfl c r
    have hU : 2 ≤ universeSize n := by have := WidthFormula.exponent_fits n; omega
    have hsmall := widthJ_fits_half n hn
    rw [← paddedJ_sum] at hsmall
    rw [table, A.smallSum_correct _ hU hsmall, paddedJ_sum]

end DiophantineNP.FiniteArithmeticGap
