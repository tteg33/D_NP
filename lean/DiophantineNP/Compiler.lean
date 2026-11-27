import DiophantineNP.Gates

/-! # Fixed-arity compilation of integer constraints

Each fixed formula has a fixed finite type of additional integer witnesses.
Any pre-existing existential variables, such as the registers of a computation,
can occupy a designated block of the formula's ordinary variable type.
-/

namespace DiophantineNP.Compiler

open MvPolynomial
open DiophantineNP.Gates

variable {σ : Type*}

/-- The atoms and positive Boolean operations used to assemble integer graphs. -/
inductive Formula (σ : Type*) where
  | zero (p : MvPolynomial σ ℤ)
  | nonnegative (p : MvPolynomial σ ℤ)
  | divides (p q : MvPolynomial σ ℤ)
  | both (f g : Formula σ)
  | either (f g : Formula σ)

/-- Integer semantics. Existence of a divisibility quotient includes the divisor zero. -/
def Formula.Holds (x : σ → ℤ) : Formula σ → Prop
  | .zero p => eval x p = 0
  | .nonnegative p => 0 ≤ eval x p
  | .divides p q => eval x p ∣ eval x q
  | .both f g => f.Holds x ∧ g.Holds x
  | .either f g => f.Holds x ∨ g.Holds x

/-- Shape of the witnesses, determined by the syntax alone. -/
def Formula.Aux : Formula σ → Type
  | .zero _ => Empty
  | .nonnegative _ => Fin 4
  | .divides _ _ => Unit
  | .both f g | .either f g => f.Aux ⊕ g.Aux

/-- Each formula requires finitely many auxiliary coordinates. -/
instance (f : Formula σ) : Finite f.Aux := by
  induction f with
  | zero _ => exact inferInstanceAs (Finite Empty)
  | nonnegative _ => exact inferInstanceAs (Finite (Fin 4))
  | divides _ _ => exact inferInstanceAs (Finite Unit)
  | both f g hf hg => exact inferInstanceAs (Finite (f.Aux ⊕ g.Aux))
  | either f g hf hg => exact inferInstanceAs (Finite (f.Aux ⊕ g.Aux))

/-- One polynomial for a fixed formula. The two branch witness types are disjoint. -/
noncomputable def Formula.compile : (f : Formula σ) → MvPolynomial (σ ⊕ f.Aux) ℤ
  | .zero p => rename Sum.inl p
  | .nonnegative p => nonnegGate p
  | .divides p q => rename Sum.inl q - rename Sum.inl p * X (Sum.inr ())
  | .both f g =>
      let pq := separate f.compile g.compile
      pq.1 ^ 2 + pq.2 ^ 2
  | .either f g =>
      let pq := separate f.compile g.compile
      pq.1 * pq.2

/-- Sound for every integer assignment and complete for every true formula. -/
theorem Formula.compile_exact (f : Formula σ) (x : σ → ℤ) :
    (∃ w : f.Aux → ℤ, eval (Sum.elim x w) f.compile = 0) ↔ f.Holds x := by
  induction f with
  | zero p =>
    change (∃ w : Empty → ℤ, eval (Sum.elim x w) (rename Sum.inl p) = 0) ↔ eval x p = 0
    simp [eval_rename, Function.comp_def]
  | nonnegative p => exact nonnegGate_exact x p
  | divides p q =>
    change (∃ w : Unit → ℤ, eval (Sum.elim x w)
      (rename Sum.inl q - rename Sum.inl p * X (Sum.inr ())) = 0) ↔ eval x p ∣ eval x q
    simp only [map_sub, map_mul, eval_X, eval_rename, sub_eq_zero]
    exact ⟨fun ⟨w, h⟩ => ⟨w (), h⟩, fun ⟨k, h⟩ => ⟨fun _ => k, h⟩⟩
  | both f g hf hg =>
    change (∃ w, eval (Sum.elim x w) ((separate f.compile g.compile).1 ^ 2 +
      (separate f.compile g.compile).2 ^ 2) = 0) ↔ f.Holds x ∧ g.Holds x
    exact (disjoint_and_exact x f.compile g.compile).trans (and_congr hf hg)
  | either f g hf hg =>
    change (∃ w, eval (Sum.elim x w) ((separate f.compile g.compile).1 *
      (separate f.compile g.compile).2) = 0) ↔ f.Holds x ∨ g.Holds x
    exact (disjoint_or_exact x f.compile g.compile).trans (or_congr hf hg)

/-- Extra existential registers may be chosen before the gate witnesses. -/
theorem Formula.compile_exists {τ : Type*} (f : Formula (σ ⊕ τ)) (x : σ → ℤ) :
    (∃ z : τ → ℤ, ∃ w : f.Aux → ℤ, eval (Sum.elim (Sum.elim x z) w) f.compile = 0) ↔
      ∃ z : τ → ℤ, f.Holds (Sum.elim x z) :=
  exists_congr fun z => f.compile_exact (Sum.elim x z)

end DiophantineNP.Compiler
