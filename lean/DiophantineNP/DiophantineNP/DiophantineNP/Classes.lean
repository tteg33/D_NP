import DiophantineNP.Statement
import Mathlib.Computability.TMComputable

/-! # Numerical languages and the complexity corollary

Both classes are defined on subsets of the natural numbers with binary input.
Verification uses mathlib's finite-alphabet, polynomial-time Turing machines.
The two complexity-theoretic library obligations are explicit hypotheses.
-/
namespace DiophantineNP.Classes

open MvPolynomial Computability

abbrev Language := Set ℕ

/-- An unambiguous framed binary encoding of the instance followed by a fixed
number of natural-number certificate fields. `none` is the delimiter. -/
def field (n : ℕ) : List (Option Bool) :=
  (finEncodingNatBool.encode n).map some ++ [none]

def tape {r : ℕ} (x : ℕ) (w : Fin r → ℕ) : List (Option Bool) :=
  field x ++ (List.ofFn (fun i => field (w i))).flatten

def tapeEncoding : FinEncoding (List (Option Bool)) where
  Γ := Option Bool
  encode := id
  decode := some
  decode_encode := fun _ => rfl
  ΓFin := inferInstance

/-- Total polynomial-time verifier on tapes; behavior on malformed tapes is free. -/
def PolytimePredicate {r : ℕ} (V : ℕ → (Fin r → ℕ) → Bool) : Prop :=
  ∃ f : List (Option Bool) → Bool,
    Nonempty (Turing.TM2ComputableInPolyTime tapeEncoding finEncodingBoolBool f) ∧
    ∀ x w, f (tape x w) = V x w

noncomputable def polyValue {r : ℕ} (P : MvPolynomial (Option (Fin r)) ℤ)
    (x : ℕ) (w : Fin r → ℕ) : ℤ :=
  aeval (fun i => match i with | none => (x : ℤ) | some j => (w j : ℤ)) P

/-- Bounded Diophantine languages over one native numerical input. -/
def D : Set Language := {L | ∃ (r : ℕ) (q : Polynomial ℕ)
    (P : MvPolynomial (Option (Fin r)) ℤ), ∀ x, x ∈ L ↔
      ∃ w : Fin r → ℕ, natCost w ≤ q.eval (bits x) ∧ polyValue P x w = 0}

/-- The witness-verifier definition using fixed tuples of binary naturals.
One natural can hold an arbitrary binary certificate with a leading sentinel. -/
def NP : Set Language := {L | ∃ (r : ℕ) (q : Polynomial ℕ) (V : ℕ → (Fin r → ℕ) → Bool),
    PolytimePredicate V ∧ ∀ x, x ∈ L ↔
      ∃ w : Fin r → ℕ, natCost w ≤ q.eval (bits x) ∧ V x w = true}

/-- The machine implementation obligation for evaluation of a fixed polynomial. -/
def PolynomialEvaluationInP : Prop :=
  ∀ (r : ℕ) (P : MvPolynomial (Option (Fin r)) ℤ),
    PolytimePredicate (fun x w => decide (polyValue P x w = 0))

theorem D_subset_NP (heval : PolynomialEvaluationInP) : D ⊆ NP := by
  rintro L ⟨r, q, P, h⟩
  refine ⟨r, q, _, heval r P, ?_⟩
  intro x
  simpa using h x

/-- Needed direction of the published Jones–Matiyasevich criterion, including
the identification of their numerical model with the definitions in this file. -/
def JonesMatiyasevichDirection : Prop := InBoundedD BitIncl → NP ⊆ D

/-- The corollary and its complete list of external premises. -/
theorem classes_eq_of_nativeVerifier (native : NativeVerifier)
    (jm : JonesMatiyasevichDirection) (machine : PolynomialEvaluationInP) : D = NP :=
  Set.Subset.antisymm (D_subset_NP machine) (jm (nativeVerifier_implies_boundedD native))

end DiophantineNP.Classes
