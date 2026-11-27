import DiophantineNP.HABProductEquivalence
import DiophantineNP.HABGeometricDivision

/-! # The two conclusions of Hesse–Allender–Barrington, Corollary 6.3

The first two rows encode the dividend and divisor. The source theorem
requires one formula for division and one formula for the iterated product.
The equivalence below isolates the missing unrestricted low-bit construction.
-/
namespace DiophantineNP.HAB
open FiniteArithmeticGap

/-- On positive divisors this is ordinary unsigned binary integer division.
The formula also supplies Lean's totalized value zero on a zero divisor. -/
def DivisionInFOM : Prop := ∃ φ : Form 1, ∀ {U : ℕ} (hU : 2≤U) (A : Matrix U) (j : Fin U),
  φ.Holds A (fun _ => j) ↔ (rowWord (A ⟨0,by omega⟩) / rowWord (A ⟨1,by omega⟩)).testBit j.val=true

/-- Both output-bit statements of the published corollary in the source language. -/
def Corollary63 : Prop := DivisionInFOM ∧ ImultInFOM

theorem corollary63_of_imult (h : ImultInFOM) : Corollary63 :=
  ⟨HABGeometricDivision.division_in_FOM_of_imult h,h⟩

/-- The low-bit product interface suffices for the entire corollary, including
the division algorithm. Conversely, the corollary supplies that interface. -/
theorem corollary63_iff_productTemplate : Corollary63 ↔ Nonempty ProductTemplate :=
  ⟨fun h => imult_iff_productTemplate.mp h.2,
   fun h => corollary63_of_imult (imult_iff_productTemplate.mpr h)⟩

end DiophantineNP.HAB
