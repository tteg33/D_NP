import DiophantineNP.KernelGrowth
import DiophantineNP.FourGridReadout
import DiophantineNP.CertifiedRounding

/-! # Rounding the actual rational Laurent readout -/
namespace DiophantineNP.FormulaLaurent
open Counting ConcreteGrid LaurentBounds
open scoped BigOperators
noncomputable section

private theorem sum_carrier {U : ℕ} (w v : Point U) :
    (∑ b : Fin (J U), ZMod.stdAddChar (rootIndex v) ^ stride U *
      (2*(ZMod.stdAddChar (rootIndex w)^stride U)⁻¹)^b.val) = FourGrid.carrier w v := by
  haveI : NeZero (J U) := ⟨by unfold J; omega⟩
  let f : ZMod (J U) → ℂ := fun b => ZMod.stdAddChar (rootIndex v) ^ stride U *
      (2*(ZMod.stdAddChar (rootIndex w)^stride U)⁻¹)^b.val
  change _ = ∑ b, f b
  rw [← (FourGrid.residues (J U)).sum_comp f]
  exact Finset.sum_congr rfl fun i _ => by simp [f, FourGrid.residues, ZMod.val_natCast_of_lt i.isLt]

theorem packedScalar_eq_readout {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) :
    (packedScalar φ t : ℂ) = FourGrid.readout φ t := by
  rw [scalar_eq_sum, FourGrid.readout]
  simp only [kernelValue, sum_carrier]
  rfl

/-- The actual rational scalar is within one quarter of the word. This
is stronger than the half-unit needed for the final integer rounding gate. -/
theorem packedScalar_close {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) :
    |packedScalar φ t - (Packing.packed φ t : ℚ)| < 1/4 := by
  have h := FourGrid.readout_close φ t
  rw [← packedScalar_eq_readout] at h
  have hreal : |((packedScalar φ t : ℚ):ℝ) - (Packing.packed φ t : ℝ)| < 1/4 := by
    have eq : (packedScalar φ t : ℂ) - (Packing.packed φ t : ℂ) =
      ((((packedScalar φ t : ℚ):ℝ) - (Packing.packed φ t : ℝ):ℝ) : ℂ) := by push_cast; rfl
    rw [eq, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  apply (Rat.cast_lt (K := ℝ)).mp
  simpa using hreal

/-- The sole remaining hypothesis of the rational-evaluator route concerns
the Diophantine graph of this particular scalar function. -/
theorem packedScalar_roundsTo {k : ℕ} (φ : Formula (k+1)) :
    Packing.RoundsTo (fun _ t => packedScalar φ t) φ :=
  fun _ _ t => (packedScalar_close φ t).trans (by norm_num)

end
end DiophantineNP.FormulaLaurent
