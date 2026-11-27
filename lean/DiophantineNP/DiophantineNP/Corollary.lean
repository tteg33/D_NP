import DiophantineNP.Main
import DiophantineNP.ScalarTermGraph
import DiophantineNP.FormulaRounding

/-! # From an evaluator for the explicit rational readout to the class equality

The scalar in this hypothesis is the rational number obtained from the
manuscript's four cyclic projections. The strict rounding estimate for this
specific number is already proved.
-/

namespace DiophantineNP

/-- For each formula, one fixed system must evaluate its specified rational
readout on every finite universe, with polynomially bounded total witness bits. -/
def PackedScalarSystems : Prop :=
  ∀ (k : ℕ) (φ : Counting.Formula (k+1)),
    Packing.ShortScalarSystem (fun _ t => FormulaLaurent.packedScalar φ t)

/-- An explicit sufficient construction for the graph: a fixed pair of integer
programs for each formula, with a positive denominator and polynomial peak
intermediate bit length. The computed fraction must equal the specified scalar. -/
def PackedScalarPrograms : Prop :=
  ∀ (k : ℕ) (φ : Counting.Formula (k+1)), ∃ num den : Packing.IntegerTerm k,
    (∀ U, 0<U → ∀ t : Fin k → Fin U, 0 < den.run (Packing.termInputs t)) ∧
    (∃ c : ℕ, ∀ U, 0<U → ∀ t : Fin k → Fin U,
      max (num.peak (Packing.termInputs t)) (den.peak (Packing.termInputs t)) ≤ (1+U)^c) ∧
    (∀ U, 0<U → ∀ t : Fin k → Fin U, Packing.termRatio num den U t = FormulaLaurent.packedScalar φ t)

theorem packedScalarSystems_of_programs (programs : PackedScalarPrograms) : PackedScalarSystems := by
  intro k φ
  obtain ⟨num,den,pos,small,exactValue⟩ := programs k φ
  obtain ⟨r,c,F,hF⟩ := Packing.scalarSystem_of_terms num den pos small
  refine ⟨r,c,F,fun U hU t => ?_⟩
  simpa only [← exactValue U hU t] using hF U hU t

theorem packing_of_packedScalarSystems (systems : PackedScalarSystems) :
    Packing.PackingClaim :=
  Packing.packing_of_scalar_systems (fun k φ =>
    ⟨_, systems k φ, FormulaLaurent.packedScalar_roundsTo φ⟩)

theorem nativeVerifier_of_packedScalarSystems (systems : PackedScalarSystems)
    (templates : WidthFormula.LiteratureFormulas) : NativeVerifier :=
  Assembly.nativeVerifier_of_packing (packing_of_packedScalarSystems systems)
    (WidthFormula.widthDescriptions_of_literature templates)

/-- Reduction via packed scalar systems and the Jones–Matiyasevich criterion. -/
theorem classEquality_of_packedScalarSystems (systems : PackedScalarSystems)
    (templates : WidthFormula.LiteratureFormulas) (jm : Classes.JonesMatiyasevichDirection)
    (machine : Classes.PolynomialEvaluationInP) : Classes.D = Classes.NP :=
  Classes.classes_eq_of_nativeVerifier
    (nativeVerifier_of_packedScalarSystems systems templates) jm machine

end DiophantineNP
