import DiophantineNP.HABProductPadding
import DiophantineNP.HABSourceTranslation
import DiophantineNP.HABPairInterpretation

/-! The manuscript's low-bit product interface and the two-index HAB
iterated product theorem are equivalent. A square-universe interpretation
makes every one of the U² possible product-bit positions accessible. -/
namespace DiophantineNP.HAB
open Counting WidthFormula FiniteArithmeticGap HABProductPadding HABPairInterpretation

/-- The same low-bit template operates on a definable U²-element universe. -/
noncomputable def fullProduct (p : ProductTemplate) : Form 2 :=
  toSource (compile @cell (toSource p.product) (fun _ => 0) (fun _ => 1))

theorem fullProduct_correct (p : ProductTemplate) {U : ℕ} (hU : 2≤U)
    (A : Matrix U) (hi lo : Fin U) :
    (fullProduct p).Holds A (pairEnv hi lo) ↔
      (∏ r : Fin U, rowWord (A r)).testBit (hi.val*U+lo.val)=true := by
  let B : Matrix (U*U) := fun r c => (factor A r.val).testBit c.val
  let arg : Fin (U*U) := code hi lo
  have harg : arg.val=hi.val*U+lo.val := by
    change lo.val + U*hi.val = _; ring
  have hprod := p.product_correct (factor A) (fun r _ => factor_fits hU A r) arg
  rw [product_factor hU A,harg] at hprod
  rw [fullProduct,toSource_correct,
    compile_correct @cell (toSource p.product) (fun _ => 0) (fun _ => 1) A B (pairEnv hi lo)
      (fun rh rl ch cl e => cell_spec rh rl ch cl A e)]
  change (toSource p.product).Holds B (fun _ => arg) ↔ _
  rw [toSource_correct]
  exact Iff.of_eq (congrArg (· = true) hprod)

theorem imult_of_productTemplate (p : ProductTemplate) : ImultInFOM :=
  ⟨fullProduct p,fun hU A hi lo => fullProduct_correct p hU A hi lo⟩

/-- Existence of the two-digit source formula is equivalent to existence of
the manuscript's single-digit product template. -/
theorem imult_iff_productTemplate : ImultInFOM ↔ Nonempty ProductTemplate :=
  ⟨fun h => ⟨productTemplate_of_imult h⟩,fun ⟨p⟩ => imult_of_productTemplate p⟩

end DiophantineNP.HAB
