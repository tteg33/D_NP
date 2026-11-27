import DiophantineNP.Assembly
import DiophantineNP.Classes
import DiophantineNP.WidthFormulaSubstitution
import DiophantineNP.ScalarSystems

/-! The complete dependency statement. The four named hypotheses are ordinary
arguments. Their proofs are not supplied by this project. -/
namespace DiophantineNP

theorem classEquality_of_packing (pack : Packing.PackingClaim)
    (uniform : Packing.WidthDescriptions) (jm : Classes.JonesMatiyasevichDirection)
    (machine : Classes.PolynomialEvaluationInP) : Classes.D = Classes.NP :=
  Classes.classes_eq_of_nativeVerifier (Assembly.nativeVerifier_of_packing pack uniform) jm machine

/-- The specified form of the published finite arithmetic operations suffices to
build both width formulas, with their low-bit semantics checked in this project. -/
theorem nativeVerifier_of_arithmetic (pack : Packing.PackingClaim)
    (arithmetic : WidthFormula.Arithmetic) : NativeVerifier :=
  Assembly.nativeVerifier_of_packing pack (WidthFormula.widthDescriptions arithmetic)

/-- A constructive target for the unfinished scalar evaluator. The analytic
estimate and the fixed constraint system refer to the same rational function. -/
def ScalarPackingConstruction : Prop :=
  ∀ (k : ℕ) (φ : Counting.Formula (k+1)),
    ∃ f : Packing.Scalar k, Packing.ShortScalarSystem f ∧ Packing.RoundsTo f φ

theorem classEquality_of_scalarSystems (scalar : ScalarPackingConstruction)
    (arithmetic : WidthFormula.Arithmetic) (jm : Classes.JonesMatiyasevichDirection)
    (machine : Classes.PolynomialEvaluationInP) : Classes.D = Classes.NP :=
  Classes.classes_eq_of_nativeVerifier (nativeVerifier_of_arithmetic
    (Packing.packing_of_scalar_systems scalar) arithmetic) jm machine

/-- The three fixed external formulas have one numerical BIT relation and
two low-output-bit templates, for iterated products and sums of bit arrays. -/
theorem classEquality_of_templates (scalar : ScalarPackingConstruction)
    (templates : WidthFormula.LiteratureFormulas) (jm : Classes.JonesMatiyasevichDirection)
    (machine : Classes.PolynomialEvaluationInP) : Classes.D = Classes.NP :=
  classEquality_of_packing (Packing.packing_of_scalar_systems scalar)
    (WidthFormula.widthDescriptions_of_literature templates) jm machine

end DiophantineNP
