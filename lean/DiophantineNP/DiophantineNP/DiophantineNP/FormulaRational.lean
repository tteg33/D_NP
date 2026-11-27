import DiophantineNP.FormulaCoordinates

/-! # Rationality of a closed projected expression -/
namespace DiophantineNP.FormulaLaurent
open ConcreteGrid LaurentBounds
noncomputable section

/-- The grid point of index zero has root of unity equal to one. -/
def rootOne (U : ℕ) : Point U := (roots U).symm ⟨0,(period U).property⟩

theorem rootIndex_one (U : ℕ) : rootIndex (rootOne U) = 0 := by
  simp [rootOne,rootIndex]

theorem char_roots_one {d U : ℕ} (v : Fin d → ℤ) :
    (gridChar (fun _ : Fin d => rootOne U) v).toMul = 1 := by
  simp [gridChar_apply,rootIndex_one,AddChar.map_zero_eq_one]

/-- A rational scalar for any Laurent expression evaluated at coordinates one.
For the complete projected kernel this is the rational value to be rounded. -/
def scalarAtOne {d : ℕ} (e : Expr d) : ℚ :=
  e.evaluate (coordinateCharacter (fun _ => (1:ℚˣ)))

theorem eval_at_roots_one {d U : ℕ} (e : Expr d) :
    e.evaluate (gridChar (fun _ : Fin d => rootOne U)) = (scalarAtOne e:ℂ) := by
  unfold scalarAtOne Expr.evaluate Raw.evaluate
  simp [char_roots_one, coordinateCharacter]

end
end DiophantineNP.FormulaLaurent
