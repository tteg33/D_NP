import DiophantineNP.EvaluatorFormula

/-! # Uniform evaluation of the packed Fourier expression -/

namespace DiophantineNP.Blueprint
open LaurentBounds ScalarProgram ScalarProjection FormulaLaurent
open scoped BigOperators
noncomputable section

open ConcreteGrid Counting

private theorem codeCentered {k d : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (j : Fin d) :
    ExprCode k d (fun U _ => centeredExpr U j) :=
  codeSub hc hq (codeXLeaf hc hq j) (ExprCode.const (RatCode.ofNat NatCode.radius))

private theorem codeResidual {k d : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (z w u v : Fin d) : ExprCode k d (fun U _ => eqResidual U z w u v) :=
  codeSub hc hq (codeSub hc hq
    (ExprCode.mul (codeXLeaf hc hq z) (codeCentered hc hq w))
    (ExprCode.mul (ExprCode.const (RatCode.ofNat NatCode.gridJ)) (codeCentered hc hq u)))
    (codeCentered hc hq v)

private theorem codeLExpr {k d : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (z w u v : Fin d) : ExprCode k d (fun U _ => LExpr U z w u v) :=
  codeTail hc hq (codeNormalize (codeSub hc hq (ExprCode.const (RatCode.literal (1/4)))
    (ExprCode.pow hc hq (codeResidual hc hq z w u v) (NatCode.const 2))))

private theorem codeDiffExpr {k d : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (j : Fin d) : ExprCode k d (fun _ _ => diffExpr j) :=
  codeSub hc hq (codeMono j 1) (codeMono j (-1))

private theorem codeSExpr {k d : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (w v : Fin d) : ExprCode k d (fun U _ => SExpr U w v) :=
  codeTail hc hq (ExprCode.mul (ExprCode.mul (codeDiffExpr hc hq w) (codeDiffExpr hc hq v))
    (ExprCode.const (RatCode.literal (-1/16))))

private theorem codeCarrierExpr {k d : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (w v : Fin d) : ExprCode k d (fun U _ => carrierExpr U w v) :=
  ExprCode.mul (ExprCode.pow hc hq (codeMono v 1) NatCode.stride)
    (ExprCode.geometric hc hq w NatCode.stride NatCode.gridJ)

/-- Add the four windows, the two selectors, and the Fourier carrier to the compiled formula. -/
theorem codeKernelExpr {k : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (φ : Counting.Formula (k+1)) : ExprCode k (4+depth φ) (fun _ t => kernelExpr φ t) := by
  let win (j : Fin (4+depth φ)) : ExprCode k _ (fun U _ => tail U (yLeaf U j)) :=
    codeTail hc hq (codeYLeaf hc hq j)
  let z : Fin (4+depth φ) := ⟨0,by omega⟩
  let w : Fin (4+depth φ) := ⟨1,by omega⟩
  let u : Fin (4+depth φ) := ⟨2,by omega⟩
  let v : Fin (4+depth φ) := ⟨3,by omega⟩
  exact ExprCode.mul (ExprCode.mul (ExprCode.mul
    (ExprCode.mul (ExprCode.mul (ExprCode.mul (ExprCode.mul (code_truthExpr hc hq φ) (win z))
      (win w)) (win u)) (win v)) (codeLExpr hc hq z w u v)) (codeSExpr hc hq w v))
    (codeCarrierExpr hc hq w v)

/-- Compile the four projections and the rational Fourier normalization. -/
theorem codePackedExpr {k : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (φ : Counting.Formula (k+1)) : ExprCode k (4+depth φ) (fun _ t => packedExpr φ t) := by
  let z : Fin (4+depth φ) := ⟨0,by omega⟩
  let w : Fin (4+depth φ) := ⟨1,by omega⟩
  let u : Fin (4+depth φ) := ⟨2,by omega⟩
  let v : Fin (4+depth φ) := ⟨3,by omega⟩
  have norm : RatCode k (fun U _ => (size U : ℚ)^4 / (8 * J U)) :=
    RatCode.divPos (RatCode.pow (RatCode.ofNat NatCode.size) 4)
      (RatCode.mul (RatCode.literal 8) (RatCode.ofNat NatCode.gridJ))
      (by intro U t hU; unfold ConcreteGrid.J; positivity)
  exact ExprCode.mul (ExprCode.const norm)
    (ExprCode.project hc hq (ExprCode.project hc hq (ExprCode.project hc hq
      (ExprCode.project hc hq (codeKernelExpr hc hq φ) v NatCode.size) u NatCode.size)
      w NatCode.size) z NatCode.size)

theorem packedExpr_evaluated (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (k : ℕ) (φ : Counting.Formula (k+1)) :
    ∃ e : ((Option (Fin k)) → ℤ) → Expr (4 + depth φ),
      Nonempty (Evaluated (Option (Fin k)) (4 + depth φ) (ValidInput k) e) ∧
      ∀ (U : ℕ) (t : Fin k → Fin U), 0 < U →
        ScalarEquiv U (e (Packing.termInputs t)) (packedExpr φ t) := by
  exact codePackedExpr hc hq φ

/-- Fixed polynomial-peak numerator and denominator programs for every formula. -/
theorem packedScalarPrograms (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) :
    PackedScalarPrograms := by
  intro k φ
  obtain ⟨e, ⟨E⟩, hequiv⟩ := packedExpr_evaluated hc hq k φ
  obtain ⟨num, den, hn, hd, hrun⟩ := E.programs
  refine ⟨num, den, ?_, peak_poly_of_tame hn hd, ?_⟩
  · intro U hU t
    exact (hrun (Packing.termInputs t) ⟨U, t, hU, rfl⟩).1
  · intro U hU t
    have h := (hrun (Packing.termInputs t) ⟨U, t, hU, rfl⟩).2
    rw [(hequiv U t hU).scalarAtOne_eq] at h
    exact h

/-- The class equality under the explicit external hypotheses. -/
theorem classEquality (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (templates : WidthFormula.LiteratureFormulas) (jm : Classes.JonesMatiyasevichDirection)
    (machine : Classes.PolynomialEvaluationInP) : Classes.D = Classes.NP :=
  classEquality_of_packedScalarSystems
    (packedScalarSystems_of_programs (packedScalarPrograms hc hq)) templates jm machine

end
end DiophantineNP.Blueprint
