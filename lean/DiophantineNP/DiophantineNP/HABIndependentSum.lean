import DiophantineNP.HABSumSelectors
import DiophantineNP.HABSumFormula
import DiophantineNP.HABMultiplyWords
import DiophantineNP.GeneralSumTemplate

/-! # Uniform iterated addition without an iterated multiplication oracle

The binary input relation supplies U little-endian rows of U bits. A single
formula gives each of the low U bits of their sum, including carries from every
row. The construction counts encoded block contributions, splits the totals
into two words, and performs one ordinary binary addition. -/
namespace DiophantineNP.HABIndependentSum
open Counting PrimeFormula WidthFormula FiniteArithmeticGap HABSumSelectors HABSumParameters

private noncomputable def largeSum : Template 1 :=
  addWords (component HABSumFormula.blockAt false) (component HABSumFormula.blockAt true)

private def large : Template 1 := fromFormula (.ex (isNat 1024 0))

private theorem large_spec {U : ℕ} (e : Fin U → Fin U → Bool) (j : Fin U) :
    large.eval e (fun _ => j) = decide (1024<U) := by
  apply Bool.eq_iff_iff.mpr
  rw [large,fromFormula_eval,exists_true,decide_eq_true_eq]
  simp only [isNat_spec,Fin.cases_zero]
  exact ⟨fun ⟨v,eq⟩ => eq ▸ v.isLt,fun h => ⟨⟨1024,h⟩,rfl⟩⟩

/-- At small widths the balanced tree has at most ten levels of binary adders. -/
noncomputable def formula : Template 1 :=
  .disj (.conj large largeSum) (.conj (.neg large) (boundedRows 10))

theorem formula_correct {U : ℕ} (f : ℕ→ℕ) (fits : ∀ i<U, f i<2^U) (j : Fin U) :
    formula.eval (fun r c => (f r.val).testBit c.val) (fun _=>j) =
      (Readout.prefixSum f U).testBit j.val := by
  simp only [formula,Template.eval.eq_5,Template.eval.eq_6,Template.eval.eq_4,large_spec]
  by_cases h : 1024<U
  · simp only [decide_eq_true h,Bool.true_and,Bool.not_true,Bool.false_and,Bool.or_false]
    classical
    let k := Nat.find (eligible_exists h)
    have hg : Eligible U k := Nat.find_spec _
    have hm : ∀ l, Eligible U l → k≤l := fun _ => Nat.find_min' _
    have hs : BlockSpec HABSumFormula.blockAt U f := by
      intro env he hv hb hb'
      exact HABSumFormula.blockAt_iff f U env (he _) (he _) (he _) (hb'.trans hb)
        (by rw [hb',hb]; exact hv.2.1.le)
    have spec := fun high i => component_spec HABSumFormula.blockAt high f hg hm hs i
    rw [largeSum, addWords_correct _ _ _ _ _ (spec false) (spec true)]
    exact HABSumBlocks.sum_bit f hg.1 (eligible_fits hg).2.2.1 j.isLt fits
  · simp only [decide_eq_false h,Bool.false_and,Bool.not_false,Bool.true_and,Bool.false_or]
    exact boundedRows_correct (d:=10) (by omega) f j

/-- A fixed binary multiplication gate for any two query words, constructed
from the unconditional row-sum formula. -/
noncomputable def multiply (a b : Template 1) : Template 1 :=
  HABMultiplyWords.multiply formula a b

theorem multiply_correct {U : ℕ} (a b : Template 1) (e : Fin U→Fin U→Bool) (x y : ℕ)
    (ha : ∀ i : Fin U, a.eval e (fun _ => i) = x.testBit i.val)
    (hb : ∀ i : Fin U, b.eval e (fun _ => i) = y.testBit i.val) (j : Fin U) :
    (multiply a b).eval e (fun _=>j) = (x*y).testBit j.val :=
  HABMultiplyWords.multiply_correct formula a b (fun f => formula_correct f) e x y ha hb j

end DiophantineNP.HABIndependentSum
