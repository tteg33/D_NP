import DiophantineNP.PackingBridge

/-! # A fixed order formula for the single set bit of the CRT scale -/

namespace DiophantineNP.Packing
open Counting WidthData

private def lessThan {k : ℕ} (x y : Fin k) : Formula k :=
  .neg (.atom (.leq y x))

private theorem lessThan_true {k U : ℕ} (x y : Fin k) (env : Fin k → Fin U) :
    (lessThan x y).eval env = true ↔ (env x).val < (env y).val := by
  change (!decide ((env y).val ≤ (env x).val)) = true ↔ _
  simp

private theorem ex_true {k U : ℕ} (φ : Formula (k+1)) (env : Fin k → Fin U) :
    (Formula.ex φ).eval env = true ↔ ∃ i : Fin U, φ.eval (Fin.cases i env) = true := by
  simp [Formula.eval, count, Finset.card_pos, Finset.Nonempty]

/-- Two variables are consecutive if they are ordered with no point between. -/
def successorFormula {k : ℕ} (x y : Fin k) : Formula k :=
  .conj (lessThan x y) (.neg (.ex (.conj (lessThan x.succ 0) (lessThan 0 y.succ))))

theorem successorFormula_true {k U : ℕ} (x y : Fin k) (env : Fin k → Fin U) :
    (successorFormula x y).eval env = true ↔ (env x).val+1 = (env y).val := by
  have hex : (Formula.ex (.conj (lessThan x.succ 0) (lessThan 0 y.succ))).eval env = true ↔
      ∃ p : Fin U, (env x).val < p.val ∧ p.val < (env y).val := by
    rw [ex_true]
    apply exists_congr
    intro p
    simp only [Formula.eval, Bool.and_eq_true, lessThan_true, Fin.cases_succ, Fin.cases_zero]
  change ((lessThan x y).eval env && !_) = true ↔ _
  rw [Bool.and_eq_true, lessThan_true, Bool.not_eq_true', ← Bool.not_eq_true, hex]
  constructor
  · rintro ⟨hlt, hno⟩
    by_contra h
    exact hno ⟨⟨(env x).val+1, by have := (env y).isLt; omega⟩, by simp, by dsimp; omega⟩
  · intro h
    refine ⟨by omega, ?_⟩
    rintro ⟨p,hl,hu⟩
    omega

/-- The free variables are the queried bit position at slot zero and the
width parameter at slot one. The only set bit of the scale is two successors
after the width parameter. -/
def scaleFormula : Formula 2 :=
  .ex (.conj (successorFormula (1 : Fin 2).succ 0) (successorFormula 0 (0 : Fin 2).succ))

theorem scaleFormula_true {U : ℕ} (env : Fin 2 → Fin U) :
    scaleFormula.eval env = true ↔ (env 1).val+2 = (env 0).val := by
  rw [scaleFormula, ex_true]
  simp only [Formula.eval, Bool.and_eq_true, successorFormula_true, Fin.cases_zero, Fin.cases_succ]
  constructor
  · rintro ⟨p,h,h'⟩; omega
  · intro h
    exact ⟨⟨(env 1).val+1, by have := (env 0).isLt; omega⟩, rfl, by dsimp; omega⟩

theorem scale_bit_fits (n : ℕ) : n+2 < universeSize n := by
  change n+2 < (n+2)^20
  have hp := Nat.pow_lt_pow_right (show 1 < n+2 by omega) (show 1 < 20 by decide)
  simpa using hp

theorem scale_description : Describes scaleFormula scale := by
  intro n _ j
  apply Bool.eq_iff_iff.mpr
  rw [scaleFormula_true, scale, Nat.testBit_two_pow, decide_eq_true_eq]
  rfl

/-- The packing theorem used for the two width words
also supplies the bounded, fully sound fixed-width scale graph. -/
theorem scaleGraph (pack : PackingClaim) : HasWidthGraph scale := by
  apply widthGraph_of_description pack scale_description
  intro n _
  exact Nat.pow_lt_pow_right (by decide) (scale_bit_fits n)

end DiophantineNP.Packing
