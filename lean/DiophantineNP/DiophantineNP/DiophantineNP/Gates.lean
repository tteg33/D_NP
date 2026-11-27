import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic.FinCases

/-! # Compiling integer gates into one polynomial

The conjunction, disjunction and order gates from Section 4 of the draft.
Every evaluation uses an integer-coefficient `MvPolynomial`. Independent
auxiliary coordinates can be introduced by taking a sum of variable types.
-/

namespace DiophantineNP.Gates

open MvPolynomial

variable {σ ι : Type*}

/-- A finite conjunction of equations, including the empty conjunction. -/
noncomputable def andGate (s : Finset ι) (p : ι → MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  ∑ i ∈ s, (p i) ^ 2

/-- A finite disjunction of equations, including the empty disjunction. -/
noncomputable def orGate (s : Finset ι) (p : ι → MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  ∏ i ∈ s, p i

theorem andGate_zero_iff (x : σ → ℤ) (s : Finset ι) (p : ι → MvPolynomial σ ℤ) :
    eval x (andGate s p) = 0 ↔ ∀ i ∈ s, eval x (p i) = 0 := by
  classical
  simp only [andGate, map_sum, map_pow]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (eval x (p i)))]
  simp

theorem orGate_zero_iff (x : σ → ℤ) (s : Finset ι) (p : ι → MvPolynomial σ ℤ) :
    eval x (orGate s p) = 0 ↔ ∃ i ∈ s, eval x (p i) = 0 := by
  classical
  rw [orGate, map_prod, Finset.prod_eq_zero_iff]

/-- The last four variables are fresh witnesses for the inequality `0 ≤ p`. -/
noncomputable def nonnegGate (p : MvPolynomial σ ℤ) : MvPolynomial (σ ⊕ Fin 4) ℤ :=
  rename Sum.inl p - (X (Sum.inr 0) ^ 2 + X (Sum.inr 1) ^ 2 +
    X (Sum.inr 2) ^ 2 + X (Sum.inr 3) ^ 2)

private theorem nonnegGate_zero_iff (x : σ → ℤ) (w : Fin 4 → ℤ) (p : MvPolynomial σ ℤ) :
    eval (Sum.elim x w) (nonnegGate p) = 0 ↔
      eval x p = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := by
  simp [nonnegGate, eval_rename, Function.comp_def, sub_eq_zero]

/-- Completeness with square-root coordinate bounds, and soundness for any witness. -/
theorem nonnegGate_exact_bounded (x : σ → ℤ) (p : MvPolynomial σ ℤ) :
    0 ≤ eval x p ↔ ∃ w : Fin 4 → ℤ,
      eval (Sum.elim x w) (nonnegGate p) = 0 ∧ ∀ i, (w i) ^ 2 ≤ eval x p := by
  constructor
  · intro h
    obtain ⟨a, b, c, d, hs⟩ := Nat.sum_four_squares (eval x p).toNat
    have hsq : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 = eval x p := by
      rw [← Int.toNat_of_nonneg h]
      exact_mod_cast hs
    let w : Fin 4 → ℤ := fun i => match i.val with
      | 0 => a | 1 => b | 2 => c | _ => d
    refine ⟨w, (nonnegGate_zero_iff x w p).2 hsq.symm, ?_⟩
    intro i
    fin_cases i <;> dsimp [w] <;> nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ),
      sq_nonneg (c : ℤ), sq_nonneg (d : ℤ)]
  · rintro ⟨w, _, h⟩
    exact (sq_nonneg (w 0)).trans (h 0)

/-- The gate also characterizes the inequality when witness bounds are omitted. -/
theorem nonnegGate_exact (x : σ → ℤ) (p : MvPolynomial σ ℤ) :
    (∃ w : Fin 4 → ℤ, eval (Sum.elim x w) (nonnegGate p) = 0) ↔ 0 ≤ eval x p := by
  constructor
  · rintro ⟨w, hw⟩
    rw [(nonnegGate_zero_iff x w p).1 hw]
    positivity
  · intro h
    obtain ⟨w, hw, _⟩ := (nonnegGate_exact_bounded x p).1 h
    exact ⟨w, hw⟩

/-- Strict comparison of integer-valued polynomials uses the slack `q - p - 1`. -/
theorem strict_gate_exact (x : σ → ℤ) (p q : MvPolynomial σ ℤ) :
    (∃ w : Fin 4 → ℤ, eval (Sum.elim x w) (nonnegGate (q - p - 1)) = 0) ↔
      eval x p < eval x q := by
  rw [nonnegGate_exact]
  simp only [map_sub, map_one]
  omega

/-- Embed two existential blocks in disjoint coordinates while retaining the common inputs. -/
noncomputable def separate {α β : Type*} (p : MvPolynomial (σ ⊕ α) ℤ)
    (q : MvPolynomial (σ ⊕ β) ℤ) :
    MvPolynomial (σ ⊕ (α ⊕ β)) ℤ × MvPolynomial (σ ⊕ (α ⊕ β)) ℤ :=
  (rename (Sum.map id Sum.inl) p, rename (Sum.map id Sum.inr) q)

private theorem eval_separate_left {α β : Type*} (x : σ → ℤ)
    (p : MvPolynomial (σ ⊕ α) ℤ) (q : MvPolynomial (σ ⊕ β) ℤ) (w : α ⊕ β → ℤ) :
      eval (Sum.elim x w) (separate p q).1 = eval (Sum.elim x (w ∘ Sum.inl)) p := by
    unfold separate
    rw [eval_rename]
    congr 2
    funext j
    cases j <;> rfl

private theorem eval_separate_right {α β : Type*} (x : σ → ℤ)
    (p : MvPolynomial (σ ⊕ α) ℤ) (q : MvPolynomial (σ ⊕ β) ℤ) (w : α ⊕ β → ℤ) :
      eval (Sum.elim x w) (separate p q).2 = eval (Sum.elim x (w ∘ Sum.inr)) q := by
    unfold separate
    rw [eval_rename]
    congr 2
    funext j
    cases j <;> rfl

/-- Compiling an existential disjunction permits all unused witness values to be zero. -/
theorem disjoint_or_exact {α β : Type*} (x : σ → ℤ)
    (p : MvPolynomial (σ ⊕ α) ℤ) (q : MvPolynomial (σ ⊕ β) ℤ) :
    (∃ w : α ⊕ β → ℤ, eval (Sum.elim x w) ((separate p q).1 * (separate p q).2) = 0) ↔
      (∃ a, eval (Sum.elim x a) p = 0) ∨ (∃ b, eval (Sum.elim x b) q = 0) := by
  constructor
  · rintro ⟨w, hw⟩
    rw [map_mul, eval_separate_left, eval_separate_right, mul_eq_zero] at hw
    exact hw.imp (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · refine ⟨Sum.elim a (fun _ => 0), ?_⟩
      rw [map_mul, eval_separate_left, mul_eq_zero]
      exact Or.inl ha
    · refine ⟨Sum.elim (fun _ => 0) b, ?_⟩
      rw [map_mul, eval_separate_right, mul_eq_zero]
      exact Or.inr hb

/-- An existential conjunction has disjoint fresh coordinates in its two branches. -/
theorem disjoint_and_exact {α β : Type*} (x : σ → ℤ)
    (p : MvPolynomial (σ ⊕ α) ℤ) (q : MvPolynomial (σ ⊕ β) ℤ) :
    (∃ w : α ⊕ β → ℤ, eval (Sum.elim x w) ((separate p q).1 ^ 2 + (separate p q).2 ^ 2) = 0) ↔
      (∃ a, eval (Sum.elim x a) p = 0) ∧ (∃ b, eval (Sum.elim x b) q = 0) := by
  simp only [map_add, map_pow, eval_separate_left, eval_separate_right]
  constructor
  · rintro ⟨w, h⟩
    have hzero (a b : ℤ) (h : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
      have ha : a ^ 2 = 0 := by linarith [sq_nonneg a, sq_nonneg b]
      have hb : b ^ 2 = 0 := by linarith [sq_nonneg a, sq_nonneg b]
      simpa using And.intro ha hb
    obtain ⟨hl, hh⟩ := hzero _ _ h
    exact ⟨⟨_, hl⟩, ⟨_, hh⟩⟩
  · rintro ⟨⟨wl, hwl⟩, ⟨wh, hwh⟩⟩
    refine ⟨Sum.elim wl wh, ?_⟩
    change (eval (Sum.elim x wl) p) ^ 2 +
      (eval (Sum.elim x wh) q) ^ 2 = 0
    simp [hwl, hwh]

/-- A conjunction of two nonnegativity tests, each with its own four squares. -/
noncomputable def intervalGate (lo hi : MvPolynomial σ ℤ) :
    MvPolynomial (σ ⊕ (Fin 4 ⊕ Fin 4)) ℤ :=
  let pq := separate (nonnegGate lo) (nonnegGate hi)
  pq.1 ^ 2 + pq.2 ^ 2

theorem intervalGate_exact (x : σ → ℤ) (lo hi : MvPolynomial σ ℤ) :
    (∃ w, eval (Sum.elim x w) (intervalGate lo hi) = 0) ↔
        0 ≤ eval x lo ∧ 0 ≤ eval x hi := by
  unfold intervalGate
  rw [disjoint_and_exact, nonnegGate_exact, nonnegGate_exact]

/-- The two endpoint inequalities for signed floor division, as one equation. -/
theorem floor_gate_exact (x : σ → ℤ) (p q k : MvPolynomial σ ℤ) (hq : 0 < eval x q) :
    (∃ w, eval (Sum.elim x w) (intervalGate (p-k*q) ((k+1)*q-p-1)) = 0) ↔
      eval x p / eval x q = eval x k := by
  rw [intervalGate_exact, Int.ediv_eq_iff_of_pos hq]
  simp only [map_sub, map_mul, map_add, map_one, add_mul, one_mul]
  omega

/-- Nearest integer with ties rounded upwards, valid for negative numerators as well. -/
theorem nearest_gate_exact (x : σ → ℤ) (p q k : MvPolynomial σ ℤ) (hq : 0 < eval x q) :
    (∃ w, eval (Sum.elim x w) (intervalGate (2*(p-k*q)+q) (q-2*(p-k*q)-1)) = 0) ↔
      (2 * eval x p + eval x q) / (2 * eval x q) = eval x k := by
  rw [intervalGate_exact, Int.ediv_eq_iff_of_pos (show 0 < 2 * eval x q by omega)]
  simp only [map_sub, map_mul, map_add, map_ofNat, map_one]
  constructor <;> rintro ⟨hl, hh⟩ <;> constructor <;> linarith

end DiophantineNP.Gates
