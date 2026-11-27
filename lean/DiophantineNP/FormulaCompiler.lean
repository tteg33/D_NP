import DiophantineNP.FormulaOperations

/-! # Fixed-coordinate translation of a formula to Laurent syntax

The maximum number of nested quantifiers determines the scratch coordinates
before the universe is chosen. Both branches of a Boolean operation reuse the
same coordinates. Each quantifier eliminates its fresh coordinate by projection.
-/
namespace DiophantineNP.FormulaLaurent

open Counting ConcreteGrid LaurentBounds
noncomputable section

def depth : {k : ℕ} → Formula k → ℕ
  | _, .atom _ => 0
  | _, .neg φ => depth φ
  | _, .conj φ ψ | _, .disj φ ψ => max (depth φ) (depth ψ)
  | _, .ex φ | _, .maj φ => depth φ + 1

/-- A slot is either an exact input parameter or an allocated root coordinate. -/
abbrev Address (U d : ℕ) := Fin U ⊕ Fin d

def addressExpr {U d : ℕ} (B : Backend U d) : Address U d → Expr d
  | .inl u => const u.val
  | .inr j => B.x j

private def env {U d k : ℕ} (r : Fin k → Address U d) (z : Fin d → Point U) :
    Fin k → Operand U := Sum.map id z ∘ r

private def Fresh {U d k : ℕ} (r : Fin k → Address U d) (next : ℕ) : Prop :=
  ∀ i j, r i = .inr j → j.val < next

private theorem fresh_enter {U d k s : ℕ} {r : Fin k → Address U d} (h : Fresh r s)
    (j : Fin d) (hj : j.val = s) : Fresh (Fin.cases (.inr j) r) (s+1) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · intro v hv
    have : j = v := Sum.inr.inj hv
    simp [← this, hj]
  · intro i v hv
    exact (h i v hv).trans (Nat.lt_succ_self _)

private theorem env_enter {U d k s : ℕ} {r : Fin k → Address U d} (h : Fresh r s)
    (j : Fin d) (hj : j.val = s) (z : Fin d → Point U) (v : Point U) :
    env (Fin.cases (.inr j) r) (Function.update z j v) = Fin.cases (.inr v) (env r z) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [env]
  · intro i
    cases he : r i with
    | inl u => simp [env, he]
    | inr l =>
      have hl := h i l he
      have hne : l ≠ j := by intro eq; rw [eq, hj] at hl; omega
      simp [env, he, hne]

/-- Translate one formula, with address environment and next unallocated slot. -/
def compile {U d : ℕ} (B : Backend U d) :
    {k : ℕ} → (φ : Formula k) → (Fin k → Address U d) →
      (s : ℕ) → s + depth φ ≤ d → Expr d
  | _, .atom a, r, _, _ => atomExpr U a (addressExpr B ∘ r)
  | _, .neg φ, r, s, h => sub (const 1) (compile B φ r s h)
  | _, .conj φ ψ, r, s, h => andExpr U
      (compile B φ r s (by simp only [depth] at h; omega))
      (compile B ψ r s (by simp only [depth] at h; omega))
  | _, .disj φ ψ, r, s, h => orExpr U
      (compile B φ r s (by simp only [depth] at h; omega))
      (compile B ψ r s (by simp only [depth] at h; omega))
  | _, .ex φ, r, s, h =>
      let j : Fin d := ⟨s, by simp only [depth] at h; omega⟩
      quantExpr B j 0 (compile B φ (Fin.cases (.inr j) r) (s+1) (by simp only [depth] at h; omega))
  | _, .maj φ, r, s, h =>
      let j : Fin d := ⟨s, by simp only [depth] at h; omega⟩
      quantExpr B j (U/2) (compile B φ (Fin.cases (.inr j) r) (s+1) (by simp only [depth] at h; omega))

set_option maxHeartbeats 600000 in
/-- Evaluation of the translated expression equals the real grid evaluator,
for every assignment, including invalid and off-window labels. -/
private theorem compile_correct {U d k : ℕ} (B : Backend U d) (φ : Formula k) :
    ∀ (r : Fin k → Address U d) (s : ℕ) (enough : s + depth φ ≤ d), Fresh r s →
    ∀ z, (compile B φ r s enough).evaluate (B.char z) = (sampleEval φ (env r z) : ℂ) := by
  induction φ with
  | atom a =>
    intro r s _ _ z
    apply eval_atom
    intro i
    cases h : r i with
    | inl u => simp [addressExpr, env, scalar, h]
    | inr j => simpa [addressExpr, env, scalar, h] using B.eval_x j z
  | neg φ ih =>
    intro r s enough fresh z
    change (sub (const 1) _).evaluate _ = ((1-sampleEval φ (env r z):ℝ):ℂ)
    rw [eval_sub, eval_const, ih r s enough fresh z]
    push_cast
    rfl
  | conj φ ψ ih jh =>
    intro r s enough fresh z
    exact eval_and _ (ih r s _ fresh z) (jh r s _ fresh z)
  | disj φ ψ ih jh =>
    intro r s enough fresh z
    exact eval_or _ (ih r s _ fresh z) (jh r s _ fresh z)
  | ex φ ih =>
    intro r s enough fresh z
    let j : Fin d := ⟨s, by simp only [depth] at enough; omega⟩
    apply eval_quant B j 0
    intro v
    rw [ih _ (s+1) _ (fresh_enter fresh j rfl) _, env_enter fresh j rfl]
  | maj φ ih =>
    intro r s enough fresh z
    let j : Fin d := ⟨s, by simp only [depth] at enough; omega⟩
    apply eval_quant B j (U/2)
    intro v
    rw [ih _ (s+1) _ (fresh_enter fresh j rfl) _, env_enter fresh j rfl]

/-- Guarded unary output with parameters as rational scalar leaves. The main
input may be placed in any coordinate below the start of the scratch region,
so other free coordinates (for example three Fourier indices) can be reserved. -/
def outputExpr {U d k : ℕ} (B : Backend U d) (φ : Formula (k+1)) (t : Fin k → Fin U)
    (j : Fin d) (s : ℕ) (enough : s + depth φ ≤ d) : Expr d :=
  andExpr U (compile B φ (Fin.cases (.inr j) (Sum.inl ∘ t)) s enough)
    (guardExpr U (B.x j))

theorem eval_outputExpr {U d k : ℕ} (B : Backend U d) (φ : Formula (k+1)) (t : Fin k → Fin U)
    (j : Fin d) (s : ℕ) (enough : s+depth φ ≤ d) (free : j.val < s) (z : Fin d → Point U) :
    (outputExpr B φ t j s enough).evaluate (B.char z) = (output φ t (z j) : ℂ) := by
  let r : Fin (k+1) → Address U d := Fin.cases (.inr j) (Sum.inl ∘ t)
  have fresh : Fresh r s := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro q eq
      have he : j=q := Sum.inr.inj eq
      simpa [← he] using free
    · intro _ _ eq
      exact nomatch eq
  have henv : env r z = Fin.cases (.inr (z j)) (Sum.inl ∘ t) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have ho := compile_correct B φ r s enough fresh z
  rw [henv] at ho
  exact eval_and _ ho (eval_guard _ (B.eval_x j z))

end
end DiophantineNP.FormulaLaurent
