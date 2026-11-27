import DiophantineNP.Compiler
import DiophantineNP.Statement
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Lemmas

/-! # Signed bit cost of the fixed constraint compiler

The compiled polynomial is exactly `Compiler.Formula.compile`. On true inputs
each new coordinate can be chosen no larger in magnitude than the largest
nonnegativity slack or divisibility dividend in the formula. This yields a
linear total bit bound in the largest input bit length, with a constant
depending on the fixed syntax and its polynomials.
-/

namespace DiophantineNP.Compiler

open MvPolynomial Gates

variable {σ : Type*}

/-- A bound on the magnitudes of all fresh gate witnesses at this input. -/
noncomputable def Formula.atomMagnitude (x : σ → ℤ) : Formula σ → ℕ
  | .zero _ => 0
  | .nonnegative p => (eval x p).natAbs
  | .divides _ q => (eval x q).natAbs
  | .both f g | .either f g => max (f.atomMagnitude x) (g.atomMagnitude x)

private theorem eval_pair {α β : Type*} (x : σ → ℤ) (u : α → ℤ) (v : β → ℤ)
    (p : MvPolynomial (σ ⊕ α) ℤ) (q : MvPolynomial (σ ⊕ β) ℤ) :
    eval (Sum.elim x (Sum.elim u v)) (separate p q).1 = eval (Sum.elim x u) p ∧
    eval (Sum.elim x (Sum.elim u v)) (separate p q).2 = eval (Sum.elim x v) q := by
  constructor <;> unfold separate <;> rw [eval_rename] <;> congr 2 <;>
    funext i <;> cases i <;> rfl

/-- Even when the divisor is zero, a quotient witness can be bounded by the
dividend. The zero-divisor case uses the quotient zero. -/
private theorem small_quotient {p q : ℤ} (h : p ∣ q) :
    ∃ u : ℤ, q = p*u ∧ u.natAbs ≤ q.natAbs := by
  by_cases hp : p = 0
  · subst p
    have hq : q = 0 := zero_dvd_iff.mp h
    exact ⟨0, by simp [hq], by simp⟩
  · obtain ⟨u,hu⟩ := h
    refine ⟨u,hu,?_⟩
    rw [hu, Int.natAbs_mul]
    exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hp)

theorem Formula.compile_small (f : Formula σ) (x : σ → ℤ) (yes : f.Holds x) :
    ∃ w : f.Aux → ℤ, eval (Sum.elim x w) f.compile = 0 ∧
      ∀ i, (w i).natAbs ≤ f.atomMagnitude x := by
  induction f with
  | zero p =>
    refine ⟨Empty.elim, ?_, fun i => nomatch i⟩
    simpa [Formula.compile, eval_rename, Function.comp_def] using yes
  | nonnegative p =>
    obtain ⟨w,hw,hb⟩ := (nonnegGate_exact_bounded x p).mp yes
    refine ⟨w,hw,?_⟩
    intro i
    change (w i).natAbs ≤ (eval x p).natAbs
    rw [Int.natAbs_le_iff_sq_le]
    refine (hb i).trans ?_
    by_cases hn : eval x p = 0
    · simp [hn]
    · have hnon : 0 ≤ eval x p := yes
      have hpos : 0 ≤ eval x p - 1 := by omega
      nlinarith [mul_nonneg hnon hpos]
  | divides p q =>
    obtain ⟨u,hu,hb⟩ := small_quotient yes
    refine ⟨fun _ => u, ?_, fun _ => hb⟩
    change eval (Sum.elim x (fun _ : Unit => u))
      (rename Sum.inl q - rename Sum.inl p * X (Sum.inr ())) = 0
    rw [map_sub, map_mul, eval_X, eval_rename, eval_rename, sub_eq_zero]
    exact hu
  | both f g hf hg =>
    obtain ⟨u,hu,hbu⟩ := hf yes.1
    obtain ⟨v,hv,hbv⟩ := hg yes.2
    obtain ⟨hl,hr⟩ := eval_pair x u v f.compile g.compile
    refine ⟨Sum.elim u v, ?_, ?_⟩
    · change eval (Sum.elim x (Sum.elim u v)) ((separate f.compile g.compile).1^2+
          (separate f.compile g.compile).2^2) = 0
      rw [map_add, map_pow, map_pow, hl, hr, hu, hv]; decide
    · rintro (i | j)
      exact (hbu i).trans (le_max_left _ _)
      exact (hbv j).trans (le_max_right _ _)
  | either f g hf hg =>
    rcases yes with h | h
    · obtain ⟨u,hu,hbu⟩ := hf h
      let v : g.Aux → ℤ := fun _ => 0
      refine ⟨Sum.elim u v, ?_, ?_⟩
      · change eval (Sum.elim x (Sum.elim u v))
          ((separate f.compile g.compile).1 * (separate f.compile g.compile).2) = 0
        rw [map_mul, (eval_pair x u v f.compile g.compile).1, hu, zero_mul]
      · rintro (i | j)
        exact (hbu i).trans (le_max_left _ _)
        exact Nat.zero_le _
    · obtain ⟨v,hv,hbv⟩ := hg h
      let u : f.Aux → ℤ := fun _ => 0
      refine ⟨Sum.elim u v, ?_, ?_⟩
      · change eval (Sum.elim x (Sum.elim u v))
          ((separate f.compile g.compile).1 * (separate f.compile g.compile).2) = 0
        rw [map_mul, (eval_pair x u v f.compile g.compile).2, hv, mul_zero]
      · rintro (i | j)
        exact Nat.zero_le _
        exact (hbv j).trans (le_max_right _ _)

/-- A fixed integer polynomial evaluated on h-bit inputs has O(h+1) bits.
The quantified constant depends only on the polynomial, including its
coefficients, and does not require a finite variable type. -/
theorem eval_magnitude_bound (p : MvPolynomial σ ℤ) :
    ∃ A : ℕ, ∀ h : ℕ, ∀ x : σ → ℤ, (∀ i, (x i).natAbs ≤ 2^h) →
      (eval x p).natAbs ≤ 2^(A*(h+1)) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨bits c.natAbs, fun h x _ => ?_⟩
    rw [eval_C]
    exact Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide)
      (Nat.le_mul_of_pos_right _ (by omega)))
  | add p q hp hq =>
    obtain ⟨A,hA⟩ := hp
    obtain ⟨B,hB⟩ := hq
    refine ⟨max A B+1, fun h x hx => ?_⟩
    let N := max A B*(h+1)
    have ha : (eval x p).natAbs ≤ 2^N := (hA h x hx).trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_left A B)))
    have hb : (eval x q).natAbs ≤ 2^N := (hB h x hx).trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_right A B)))
    rw [map_add]
    calc
      _ ≤ _ := Int.natAbs_add_le _ _
      _ ≤ 2^N+2^N := Nat.add_le_add ha hb
      _ = 2^(N+1) := by rw [pow_succ]; omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by dsimp [N]; rw [Nat.add_mul]; omega)
  | mul_X p i hp =>
    obtain ⟨A,hA⟩ := hp
    refine ⟨A+1, fun h x hx => ?_⟩
    rw [map_mul, eval_X, Int.natAbs_mul]
    refine (Nat.mul_le_mul (hA h x hx) (hx i)).trans ?_
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by rw [Nat.add_mul]; omega)

theorem Formula.atomMagnitude_bound (f : Formula σ) :
    ∃ A : ℕ, ∀ h : ℕ, ∀ x : σ → ℤ, (∀ i, (x i).natAbs ≤ 2^h) →
      f.atomMagnitude x ≤ 2^(A*(h+1)) := by
  induction f with
  | zero p => exact ⟨0, fun _ _ _ => Nat.zero_le _⟩
  | nonnegative p => exact eval_magnitude_bound p
  | divides p q => exact eval_magnitude_bound q
  | both f g hf hg | either f g hf hg =>
    obtain ⟨A,hA⟩ := hf
    obtain ⟨B,hB⟩ := hg
    refine ⟨max A B, fun h x hx => max_le ?_ ?_⟩
    exact (hA h x hx).trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right _ (le_max_left A B)))
    exact (hB h x hx).trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right _ (le_max_right A B)))

/-- A single constant works at all bit widths and every true input. The bit
cost counts signs and charges two bits even for an inactive zero coordinate. -/
theorem Formula.compile_linear_cost (f : Formula σ) [Fintype f.Aux] :
    ∃ K : ℕ, ∀ h : ℕ, ∀ x : σ → ℤ, (∀ i, bits (x i).natAbs ≤ h) → f.Holds x →
      ∃ w : f.Aux → ℤ, eval (Sum.elim x w) f.compile = 0 ∧ intCost w ≤ K*(h+1) := by
  obtain ⟨A,hA⟩ := f.atomMagnitude_bound
  refine ⟨Fintype.card f.Aux*(A+2), fun h x hx yes => ?_⟩
  obtain ⟨w,hw,hb⟩ := f.compile_small x yes
  have hm := hA h x fun i => Nat.lt_log2_self.le.trans
    (Nat.pow_le_pow_right (by decide) (hx i))
  refine ⟨w,hw,?_⟩
  unfold intCost
  calc
    _ ≤ ∑ _ : f.Aux, (A+2)*(h+1) := by
      apply Finset.sum_le_sum
      intro i _
      have ha : (w i).natAbs.log2 ≤ A*(h+1) := by
        by_cases hz : (w i).natAbs = 0
        · simp [hz]
        · exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
            ((Nat.log2_self_le hz).trans ((hb i).trans hm))
      unfold bits
      rw [Nat.add_mul]
      omega
    _ = _ := by simp [Nat.mul_assoc]

end DiophantineNP.Compiler
