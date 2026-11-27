import DiophantineNP.KernelExpressions
import DiophantineNP.FormulaRational

/-! # The normalized Fourier scalar as one closed Laurent expression

Coordinates zero through three are the four roots. Four successive cyclic
projections evaluate the entire sum. The extra coordinates belong to the
logical quantifiers and the resulting value is independent of their assignments.
-/

namespace DiophantineNP.FormulaLaurent
open Counting ConcreteGrid LaurentBounds
open scoped BigOperators
noncomputable section

private def c0 {d : ℕ} : Fin (4+d) := ⟨0,by omega⟩
private def c1 {d : ℕ} : Fin (4+d) := ⟨1,by omega⟩
private def c2 {d : ℕ} : Fin (4+d) := ⟨2,by omega⟩
private def c3 {d : ℕ} : Fin (4+d) := ⟨3,by omega⟩

/-- The factors occur in manuscript order, with all four windows applied. -/
def kernelExpr {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) : Expr (4+depth φ) :=
  let win (j : Fin _) := tail U (yLeaf U j)
  let mask := ((((((truthExpr φ t).mul (win c0)).mul (win c1)).mul (win c2)).mul (win c3)).mul
    (LExpr U c0 c1 c2 c3)).mul (SExpr U c1 c3)
  mask.mul (carrierExpr U c1 c3)

def kernelValue {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) (z w u v : Point U) : ℂ :=
  let win := (observed U).tests.window
  ((output φ t z * win z * win w * win u * win v * KernelSelectors.L z w u v *
    KernelSelectors.S w v : ℝ):ℂ) *
    ∑ b : Fin (J U), ZMod.stdAddChar (rootIndex v) ^ stride U *
      (2*(ZMod.stdAddChar (rootIndex w)^stride U)⁻¹)^b.val

theorem eval_kernelExpr {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U)
    (z : Fin (4+depth φ) → Point U) :
    (kernelExpr φ t).evaluate (gridChar z) = kernelValue φ t (z c0) (z c1) (z c2) (z c3) := by
  have hw (j : Fin (4+depth φ)) :
      (tail U (yLeaf U j)).evaluate (gridChar z) = ((observed U).tests.window (z j) : ℂ) :=
    eval_tail _ ((concreteBackend U _).eval_y j z)
  simp only [kernelExpr, Expr.evaluate_mul, evaluate_truthExpr, hw, eval_LExpr, eval_SExpr,
    eval_carrierExpr, kernelValue, Complex.ofReal_mul]
  rfl

/-- Undo four normalized means and apply the exact Fourier normalization. -/
def packedExpr {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) : Expr (4+depth φ) :=
  let m := period U
  let avg := ((((kernelExpr φ t).project c3 m).project c2 m).project c1 m).project c0 m
  (const ((size U:ℚ)^4/(8*J U))).mul avg

private theorem normalization {G : Type} [Fintype G] (M J : ℂ) (hm : M ≠ 0) (hj : J ≠ 0)
    (f : G → G → G → G → ℂ) :
    M^4/(8*J) * (M⁻¹ * ∑ z, M⁻¹ * ∑ w, M⁻¹ * ∑ u, M⁻¹ * ∑ v, f z w u v)
      = (∑ z, ∑ w, ∑ u, ∑ v, f z w u v)/(8*J) := by
  simp_rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  refine Finset.sum_congr rfl (fun w _ => ?_)
  refine Finset.sum_congr rfl (fun u _ => ?_)
  refine Finset.sum_congr rfl (fun v _ => ?_)
  field_simp

/-- Evaluation at any ambient assignment is the same normalized sum. -/
theorem eval_packedExpr {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U)
    (e : Fin (4+depth φ) → Point U) :
    (packedExpr φ t).evaluate (gridChar e) =
      (∑ z, ∑ w, ∑ u, ∑ v, kernelValue φ t z w u v)/(8*(J U:ℂ)) := by
  have h01 : (c0 : Fin (4+depth φ)) ≠ c1 := by simp [c0,c1]
  have h02 : (c0 : Fin (4+depth φ)) ≠ c2 := by simp [c0,c2]
  have h03 : (c0 : Fin (4+depth φ)) ≠ c3 := by simp [c0,c3]
  have h12 : (c1 : Fin (4+depth φ)) ≠ c2 := by simp [c1,c2]
  have h13 : (c1 : Fin (4+depth φ)) ≠ c3 := by simp [c1,c3]
  have h23 : (c2 : Fin (4+depth φ)) ≠ c3 := by simp [c2,c3]
  simp only [packedExpr, Expr.evaluate_mul, eval_const, gridChar_project, eval_kernelExpr,
    Function.update_self, Function.update_of_ne h01, Function.update_of_ne h02,
    Function.update_of_ne h03, Function.update_of_ne h12, Function.update_of_ne h13,
    Function.update_of_ne h23]
  push_cast
  apply normalization
  · exact_mod_cast (period U).ne_zero
  · have h : 0 < J U := by unfold J; omega
    exact_mod_cast h.ne'

/-- This scalar is rational and suitable for an exact graph and integer rounding. -/
def packedScalar {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) : ℚ :=
  scalarAtOne (packedExpr φ t)

theorem scalar_eq_sum {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) :
    (packedScalar φ t : ℂ) = (∑ z, ∑ w, ∑ u, ∑ v, kernelValue φ t z w u v)/(8*(J U:ℂ)) := by
  rw [packedScalar, ← eval_at_roots_one (U := U), eval_packedExpr]

end
end DiophantineNP.FormulaLaurent
