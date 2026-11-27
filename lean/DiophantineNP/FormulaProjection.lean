import DiophantineNP.FormulaCoordinates

/-! # Averaging a Laurent expression over the concrete finite grid -/
namespace DiophantineNP.FormulaLaurent
open Counting ConcreteGrid LaurentBounds Finset
open scoped BigOperators
noncomputable section

private theorem updated_phase {d m : ℕ} {P : Type*} (r : P → ZMod m)
    (z : Fin d → P) (j : Fin d) (p : P) (v : Fin d → ℤ) :
    (∑ i, (v i : ZMod m)*r (Function.update z j p i)) =
      (∑ i, ((Raw.without v j i : ℤ) : ZMod m)*r (z i)) + (v j : ZMod m)*r p := by
  classical
  have eq (i : Fin d) : (v i : ZMod m)*r (Function.update z j p i) =
      ((Raw.without v j i : ℤ) : ZMod m)*r (z i) +
        (if i = j then (v j : ZMod m)*r p else 0) := by
    by_cases h : i = j <;> simp [h, Raw.without, Function.update]
  simp only [eq, Finset.sum_add_distrib]
  simp

/-- A character with independent cyclic coordinates implements syntactic
projection as a normalized average over replacements of just one coordinate. -/
theorem evaluate_project_grid {d m : ℕ} [NeZero m] {P : Type*} [Fintype P]
    (r : P ≃ ZMod m) (χ : (Fin d → P) → Character d ℂ)
    (hχ : ∀ z v, (χ z v).toMul = ZMod.stdAddChar (∑ i, (v i : ZMod m)*r (z i)))
    (e : Expr d) (j : Fin d) (z : Fin d → P) :
    (e.project j ⟨m,Nat.pos_of_ne_zero (NeZero.ne m)⟩).evaluate (χ z) =
      (m:ℂ)⁻¹ * ∑ p : P, e.evaluate (χ (Function.update z j p)) := by
  classical
  have factor (p : P) (v : Fin d → ℤ) :
      (χ (Function.update z j p) v).toMul =
        (χ z (Raw.without v j)).toMul * ZMod.stdAddChar ((v j : ZMod m)*r p) := by
    rw [hχ,hχ, ← AddChar.map_add_eq_mul, updated_phase]
  let F (k : ZMod m) := e.expand.evaluate (fun v => (χ z (Raw.without v j)).toMul *
      ZMod.stdAddChar ((v j : ZMod m)*k))
  have hpoint (p : P) : e.expand.evaluate (fun v => (χ (Function.update z j p) v).toMul) = F (r p) := by
    simp only [factor,F]
  change ((e.expand.project j m).evaluate (fun v => (χ z v).toMul))/(e.bounds.denominator : ℂ) =
    (m:ℂ)⁻¹ * ∑ p : P, e.expand.evaluate (fun v => (χ (Function.update z j p) v).toMul) /
      (e.bounds.denominator : ℂ)
  rw [Raw.evaluate_project]
  simp_rw [hpoint]
  change ((m:ℂ)⁻¹*∑ k : ZMod m, F k)/(e.bounds.denominator : ℂ) =
    (m:ℂ)⁻¹ * ∑ p : P, F (r p)/(e.bounds.denominator : ℂ)
  rw [← Finset.sum_div, r.sum_comp F, mul_div_assoc]

/-- The projection field of the backend for the actual grid, with no extra
analytic or representation hypothesis. -/
theorem gridChar_project {U d : ℕ} (e : Expr d) (j : Fin d) (z : Fin d → Point U) :
    (e.project j (period U)).evaluate (gridChar z) =
      (size U:ℂ)⁻¹ * ∑ p : Point U, e.evaluate (gridChar (Function.update z j p)) := by
  apply evaluate_project_grid (rootEquiv U) gridChar
  intro z v
  simp only [gridChar_apply, rootEquiv_apply]

end
end DiophantineNP.FormulaLaurent
