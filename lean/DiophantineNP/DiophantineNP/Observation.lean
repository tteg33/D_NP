import DiophantineNP.Grid
import DiophantineNP.Counting

/-! # The geometric observations used by the finite formula evaluator -/
namespace DiophantineNP.ConcreteGrid

@[irreducible] def radius (U : ℕ) : ℕ := max 2 U
@[irreducible] def size (U : ℕ) : ℕ := Grid.period (radius U)
@[irreducible] noncomputable def error (U : ℕ) : ℝ :=
  32*(radius U:ℝ)^3/(size U:ℝ)^2+(radius U:ℝ)/(size U:ℝ)^4

set_option maxHeartbeats 1600000 in
structure Observed (U : ℕ) (I O : Type) [Fintype I] [Fintype O] where
  card_eq : Fintype.card (Counting.LabelGrid U I O) = size U
  x : Counting.LabelGrid U I O → ℝ
  Y : Counting.LabelGrid U I O → ℝ
  x_bound : ∀ (z : Counting.LabelGrid U I O), |x z| ≤ (size U:ℝ)
  y_bound : ∀ (z : Counting.LabelGrid U I O), |Y z| ≤ 1
  y_selected : ∀ (z : (Fin U × Bool) ⊕ I), 1/(size U:ℝ)^2 ≤ Y (.inl z)
  y_off : ∀ (o : O), Y (.inr o) ≤ -(1/(size U:ℝ)^2)
  close_valid : ∀ (i : Fin U) (b : Bool), |x (.inl (.inl (i,b))) - ((i:ℕ):ℝ)| ≤ error U
  close_invalid : ∀ i:I, ∃ j:ℕ, U ≤ j ∧ j ≤ 2*radius U ∧ |x (.inl (.inr i)) - (j:ℝ)| ≤ error U

end DiophantineNP.ConcreteGrid
