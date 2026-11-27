import DiophantineNP.ScalarCertified

/-! # Fixed signed floor-division operation with bounded witnesses

On a positive denominator the operation returns the Euclidean quotient even
for negative numerators. Zero and negative denominators take a fixed zero
branch. No primary witness registers are needed.
-/

namespace DiophantineNP.ScalarProgram

open MvPolynomial Compiler
noncomputable section

def positiveDiv (a b : ℤ) : ℤ := if 0 < b then a/b else 0

private def divisionFormula : Compiler.Formula (Option Bool ⊕ Empty) :=
  let a : MvPolynomial (Option Bool ⊕ Empty) ℤ := X (.inl (some false))
  let b : MvPolynomial (Option Bool ⊕ Empty) ℤ := X (.inl (some true))
  let y : MvPolynomial (Option Bool ⊕ Empty) ℤ := X (.inl none)
  .either (.both (.nonnegative (b-1))
    (.both (.nonnegative (a-y*b)) (.nonnegative ((y+1)*b-a-1))))
    (.both (.nonnegative (-b)) (.zero y))

private theorem divisionFormula_iff (a b y : ℤ) (w : Empty → ℤ) :
    divisionFormula.Holds (Sum.elim (opInputs a b y) w) ↔ y = positiveDiv a b := by
  change ((0 ≤ eval _ _ ∧ 0 ≤ eval _ _ ∧ 0 ≤ eval _ _) ∨ (0 ≤ eval _ _ ∧ eval _ _ = 0)) ↔ _
  simp only [map_sub, map_mul, map_add, map_one, map_neg, eval_X, Sum.elim_inl, opInputs,
    Bool.false_eq_true, ↓reduceIte]
  by_cases hb : 0 < b
  · rw [positiveDiv, if_pos hb, eq_comm (a := y) (b := a/b), Int.ediv_eq_iff_of_pos hb]
    rw [add_mul, one_mul]
    constructor
    · rintro (⟨_,hl,hu⟩|⟨hn,_⟩) <;> omega
    · rintro ⟨hl,hu⟩; exact Or.inl ⟨by omega,by omega,by omega⟩
  · rw [positiveDiv, if_neg hb]
    constructor
    · rintro (⟨hp,_,_⟩|⟨_,hy⟩) <;> omega
    · intro hy; exact Or.inr ⟨by omega,hy⟩

/-- A fixed-polynomial scalar operation with unrestricted soundness and
polynomial total witness cost, supplied by the bounded constraint compiler. -/
def divisionOperation : Operation :=
  Operation.ofShortFormula positiveDiv divisionFormula
    (fun a b y w => (divisionFormula_iff a b y w).mp)
    ⟨0,0,fun a b => ⟨Empty.elim, by simp [intCost],
      (divisionFormula_iff a b _ _).mpr rfl⟩⟩

@[simp] theorem divisionOperation_apply (a b : ℤ) :
    divisionOperation.apply a b = positiveDiv a b := rfl

theorem divisionOperation_pos (a b : ℤ) (hb : 0 < b) :
    divisionOperation.apply a b = a / b := by simp [positiveDiv,hb]

theorem divisionOperation_nonpos (a b : ℤ) (hb : b ≤ 0) :
    divisionOperation.apply a b = 0 := by simp [positiveDiv,not_lt.mpr hb]

end
end DiophantineNP.ScalarProgram
