import DiophantineNP.GridLogic
import DiophantineNP.LaurentSemantics
/-! # Interfaces for evaluating Laurent formulas on the actual cyclic grid -/
namespace DiophantineNP.FormulaLaurent
open Counting ConcreteGrid LaurentBounds
open scoped BigOperators
noncomputable section

abbrev Point (U : ℕ) := LabelGrid U (Invalid U) (Outside U)

def period (U : ℕ) : ℕ+ := ⟨size U, by unfold size Grid.period; positivity⟩

/-- One character per simultaneous grid assignment. Only two leaves use the
parametrization explicitly; the remaining syntax uses ring operations and
the cyclic coordinate projection. -/
structure Backend (U d : ℕ) where
  char : (Fin d → Point U) → Character d ℂ
  x : Fin d → Expr d
  y : Fin d → Expr d
  eval_x : ∀ j z, (x j).evaluate (char z) = (((observed U).x (z j)) : ℂ)
  eval_y : ∀ j z, (y j).evaluate (char z) = (((observed U).Y (z j)) : ℂ)
  eval_project : ∀ (e : Expr d) j z, (e.project j (period U)).evaluate (char z) =
    (size U:ℂ)⁻¹ * ∑ p : Point U, e.evaluate (char (Function.update z j p))

end
end DiophantineNP.FormulaLaurent
