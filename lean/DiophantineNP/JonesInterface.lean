import DiophantineNP.Classes
import Mathlib.Data.Nat.Size

/-! # The numerical normal form in Jones–Matiyasevich, equation (53) -/
namespace DiophantineNP.Classes.Jones

/-- A fixed natural-witness polynomial for the length used in (53).
This charges zero bits to the numerical value zero in the graph itself. -/
def LengthGraph : Prop :=
  ∃ (r C : ℕ) (P : Equation (Fin r)),
    (∀ (a l : ℕ) (w : Fin r → ℕ),
      value P a l (fun i => (w i : ℤ)) = 0 → l = a.size) ∧
    (∀ a : ℕ, ∃ w : Fin r → ℕ, natCost w ≤ (bits a + 2)^C ∧
      value P a a.size (fun i => (w i : ℤ)) = 0)

/-- Source equation (53): both polynomials have integer coefficients, all
guessed numbers are natural, and the inclusive length bound applies to each. -/
def NormalForm (L : Language) : Prop :=
  ∃ (r : ℕ) (P : Polynomial ℤ) (Q : MvPolynomial (Option (Fin (r+2))) ℤ),
    ∀ x : ℕ, x ∈ L ↔ ∃ w : Fin (r+2) → ℕ,
      (∀ i, (Nat.size (w i) : ℤ) ≤ P.eval (x.size : ℤ)) ∧
      BitIncl (w 0) (w 1) ∧ polyValue Q x w = 0

end DiophantineNP.Classes.Jones
