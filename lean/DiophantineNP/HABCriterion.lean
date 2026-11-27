import DiophantineNP.CoordinateClass
import DiophantineNP.HABTranslation
import DiophantineNP.ProductCriterion

/-! # The numerical class equality from the source-language iterated-product theorem -/
namespace DiophantineNP

/-- Corollary 6.3 in the Hesse–Allender–Barrington FOM language suffices
for the native verifier; the translation to the project's syntax is verified. -/
theorem nativeVerifier_of_hab (hab : HAB.ImultInFOM) : NativeVerifier :=
  nativeVerifier_of_product (HAB.productTemplate_of_imult hab)

/-- The finite-model theorem is the sole mathematical input to this implication. -/
theorem classEquality_of_hab (hab : HAB.ImultInFOM) : Classes.D = Classes.NP :=
  classEquality_of_native (nativeVerifier_of_hab hab)

/-- Per-coordinate inclusive numerical bounds give the same equality. -/
theorem classEquality_powerCutoff_of_hab (hab : HAB.ImultInFOM) : Classes.Dpower = Classes.NP :=
  Classes.Dpower_eq_D.trans (classEquality_of_hab hab)

end DiophantineNP
