import DiophantineNP.HABModularArithmetic
import DiophantineNP.HABWideBitDecision
import DiophantineNP.HABCorollary63
import DiophantineNP.HABCriterion

/-! # Hesse–Allender–Barrington Corollary 6.3 and the draft's class equality

The lower-scale readout supplies the short modular products. Those yield prime
powering at the upper scale. The upper-scale CRT readout produces the entire
iterated product, and geometric-series division yields the quotient bits.
-/
namespace DiophantineNP

/-- One formula in the source grammar computes any bit of an unrestricted product. -/
theorem HAB.imultInFOM : HAB.ImultInFOM :=
  HABWideOutput.imult_of_local _ (HABWideBitDecision.localSpec HABModularArithmetic.shortProducts)

/-- Division and iterated multiplication in finite first-order logic with unary majority. -/
theorem HAB.corollary63 : HAB.Corollary63 := HAB.corollary63_of_imult HAB.imultInFOM

/-- The draft's globally sound native polynomial verifier, including the honest-witness bound. -/
theorem nativeVerifier : NativeVerifier := nativeVerifier_of_hab HAB.imultInFOM

/-- Equality for binary numerical languages under the total witness-bit convention. -/
theorem classEquality : Classes.D = Classes.NP := classEquality_of_hab HAB.imultInFOM

/-- The equivalent inclusive, per-coordinate numerical bound. -/
theorem classEquality_powerCutoff : Classes.Dpower = Classes.NP :=
  classEquality_powerCutoff_of_hab HAB.imultInFOM

end DiophantineNP
