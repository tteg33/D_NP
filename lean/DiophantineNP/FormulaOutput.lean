import DiophantineNP.FormulaCompiler
import DiophantineNP.FormulaLeaves
import DiophantineNP.FormulaProjection

/-! # A rational Laurent expression for the guarded truth function -/
namespace DiophantineNP.FormulaLaurent
open Counting ConcreteGrid LaurentBounds
noncomputable section

def concreteBackend (U d : ℕ) : Backend U d where
  char := gridChar
  x := xLeaf U
  y := yLeaf U
  eval_x j z := (leaves_on_root j (z j) (gridChar z) (gridChar_single z j)).1
  eval_y j z := (leaves_on_root j (z j) (gridChar z) (gridChar_single z j)).2
  eval_project := gridChar_project

/-- Coordinate zero is the free query. Coordinates 1,2,3 are reserved for
the Fourier kernel. All subsequent coordinates are reused for nested quantifiers. -/
def truthExpr {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) : Expr (4 + depth φ) :=
  outputExpr (concreteBackend U _) φ t ⟨0,by omega⟩ 4 le_rfl

theorem evaluate_truthExpr {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U)
    (z : Fin (4 + depth φ) → Point U) :
    (truthExpr φ t).evaluate (gridChar z) = (output φ t (z ⟨0,by omega⟩) : ℂ) :=
  eval_outputExpr (concreteBackend U _) φ t ⟨0, by omega⟩ 4 le_rfl (by change 0 < 4; decide) z

/-- Every valid query point recovers the Boolean answer with the stated
precision in the real part of a concrete Laurent evaluation. -/
theorem truthExpr_on_valid {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U)
    (z : Fin (4+depth φ) → Point U) (i : Fin U) (b : Bool)
    (h : z ⟨0,by omega⟩ = .inl (.inl (i,b))) :
    |((truthExpr φ t).evaluate (gridChar z)).re - bit (φ.eval (Fin.cases i t))| ≤ epsilon U := by
  rw [evaluate_truthExpr, h, Complex.ofReal_re]
  exact output_valid φ t i b

end
end DiophantineNP.FormulaLaurent
