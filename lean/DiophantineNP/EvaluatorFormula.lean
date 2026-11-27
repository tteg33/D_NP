import DiophantineNP.EvaluatorParameters

/-! # Compiling every counting formula to fixed scalar terms -/

namespace DiophantineNP.Blueprint
open LaurentBounds ScalarProgram ScalarProjection FormulaLaurent
open scoped BigOperators
noncomputable section

open ConcreteGrid Counting

variable {k d : ℕ}

theorem codeMono (j : Fin d) (v : ℤ) :
    ExprCode k d (fun _ _ => mono j v) :=
  ExprCode.monomial (Pi.single j v)

theorem codeSub (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {f g : Family k (Expr d)} (hf : ExprCode k d f) (hg : ExprCode k d g) :
    ExprCode k d (fun U t => FormulaLaurent.sub (f U t) (g U t)) :=
  ExprCode.add hc hq hf (ExprCode.neg hg)

private theorem codeCosine (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (j : Fin d) :
    ExprCode k d (fun _ _ => cosineLeaf j) :=
  ExprCode.mul (ExprCode.const (RatCode.literal (1/2)))
    (ExprCode.add hc hq (codeMono j 1) (codeMono j (-1)))

private theorem piParameter_pos (U : ℕ) : 0 < piRational ((size U)^4) := by
  have h : 0 < (size U)^4 := pow_pos (period U).property _
  have hc : 0 < ((2*((size U)^4)).choose ((size U)^4)) := Nat.choose_pos (by omega)
  unfold piRational
  positivity

private theorem codePiParameter (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) :
    RatCode k (fun U _ => piRational ((size U)^4)) :=
  RatCode.piRational hc hq (NatCode.pow NatCode.size 4) (fun U _ _ => pow_pos (period U).property _)

theorem codeXLeaf (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (j : Fin d) :
    ExprCode k d (fun U _ => xLeaf U j) := by
  unfold xLeaf
  apply ExprCode.add hc hq (ExprCode.const (RatCode.ofNat NatCode.radius))
  apply ExprCode.mul _ (codeCosine hc hq j)
  apply ExprCode.const
  exact RatCode.divPos (RatCode.neg (RatCode.ofNat NatCode.size))
    (RatCode.mul (RatCode.literal 2) (codePiParameter hc hq))
    (fun U _ _ => mul_pos (by norm_num) (piParameter_pos U))

theorem codeYLeaf (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (j : Fin d) :
    ExprCode k d (fun U _ => yLeaf U j) := by
  unfold yLeaf
  apply ExprCode.add hc hq _
    (ExprCode.mul (ExprCode.const (RatCode.literal (-1/4)))
      (ExprCode.pow hc hq (codeCosine hc hq j) (NatCode.const 2)))
  apply ExprCode.const
  apply RatCode.divPos _ (RatCode.literal 4) (by intros; norm_num)
  apply RatCode.pow _ 2
  apply RatCode.divPos _ (RatCode.ofNat NatCode.size) (fun U _ _ => by exact_mod_cast (period U).property)
  exact RatCode.mul (codePiParameter hc hq)
    (RatCode.add (RatCode.mul (RatCode.literal 2) (RatCode.ofNat NatCode.radius)) (RatCode.literal 1))

theorem codeNormalize {f : Family k (Expr d)} (hf : ExprCode k d f) :
    ExprCode k d (fun U t => normalize U (f U t)) := by
  unfold FormulaLaurent.normalize
  apply ExprCode.mul hf
  apply ExprCode.const
  exact RatCode.divPos (RatCode.literal 1)
    (RatCode.mul (RatCode.literal 8) (RatCode.pow (RatCode.ofNat NatCode.size) 4))
    (fun U _ _ => mul_pos (by norm_num) (pow_pos (by exact_mod_cast (period U).property) _))

theorem codeTail (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {f : Family k (Expr d)} (hf : ExprCode k d f) :
    ExprCode k d (fun U t => tail U (f U t)) := by
  unfold tail
  have hh : NatCode k (fun U _ => halfDegree U) := NatCode.halfDegree hc hq
  exact ExprCode.threshold hc hq hf (NatCode.add (NatCode.mul (NatCode.const 2) hh) (NatCode.const 1))
    (NatCode.add hh (NatCode.const 1)) (fun U _ _ => by omega)

theorem codeAnd (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {f g : Family k (Expr d)} (hf : ExprCode k d f) (hg : ExprCode k d g) :
    ExprCode k d (fun U t => andExpr U (f U t) (g U t)) :=
  codeTail hc hq (ExprCode.mul (codeSub hc hq (ExprCode.add hc hq hf hg)
    (ExprCode.const (RatCode.literal (3/2)))) (ExprCode.const (RatCode.literal (1/4))))

theorem codeOr (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {f g : Family k (Expr d)} (hf : ExprCode k d f) (hg : ExprCode k d g) :
    ExprCode k d (fun U t => orExpr U (f U t) (g U t)) :=
  codeTail hc hq (ExprCode.mul (codeSub hc hq (ExprCode.add hc hq hf hg)
    (ExprCode.const (RatCode.literal (1/2)))) (ExprCode.const (RatCode.literal (1/4))))

theorem codeGuard (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {f : Family k (Expr d)} (hf : ExprCode k d f) :
    ExprCode k d (fun U t => guardExpr U (f U t)) :=
  codeTail hc hq (codeNormalize (ExprCode.add hc hq (codeSub hc hq (codeSub hc hq
    (ExprCode.const (RatCode.ofNat NatCode.universe)) (ExprCode.const (RatCode.literal 1))) hf)
    (ExprCode.const (RatCode.literal (1/2)))))

theorem codeAtom (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {n : ℕ} (a : Counting.Atom n) {z : Family k (Fin n → Expr d)}
    (hz : ∀ i, ExprCode k d (fun U t => z U t i)) :
    ExprCode k d (fun U t => atomExpr U a (z U t)) := by
  have hres : ExprCode k d (fun U t => residual a (z U t)) := by
    cases a with
    | eqv i j => exact codeSub hc hq (hz i) (hz j)
    | leq i j => exact codeSub hc hq (hz j) (hz i)
    | add i j l => exact codeSub hc hq (ExprCode.add hc hq (hz i) (hz j)) (hz l)
    | mul i j l => exact codeSub hc hq (ExprCode.mul (hz i) (hz j)) (hz l)
  unfold atomExpr
  apply codeTail hc hq
  apply codeNormalize
  by_cases ho : a.isOrder
  · simp only [if_pos ho]
    exact ExprCode.add hc hq hres (ExprCode.const (RatCode.literal (1/2)))
  · simp only [if_neg ho]
    exact codeSub hc hq (ExprCode.const (RatCode.literal (1/4)))
      (ExprCode.pow hc hq hres (NatCode.const 2))

theorem codeQuant (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (j : Fin d) {a : Family k ℕ} (count : NatCode k a)
    {f : Family k (Expr d)} (child : ExprCode k d f) :
    ExprCode k d (fun U t => quantExpr (concreteBackend U d) j (a U t) (f U t)) := by
  unfold quantExpr
  apply codeTail hc hq
  apply ExprCode.mul
  · apply codeSub hc hq _ (ExprCode.const (RatCode.literal (1/2)))
    apply codeSub hc hq _ (ExprCode.const (RatCode.ofNat count))
    apply ExprCode.mul
    · exact ExprCode.const (RatCode.divPos (RatCode.ofNat NatCode.size) (RatCode.literal 2)
        (by intros; norm_num))
    · apply ExprCode.project hc hq _ j NatCode.size
      exact ExprCode.mul (codeTail hc hq (codeYLeaf hc hq j))
        (codeAnd hc hq child (codeGuard hc hq (codeXLeaf hc hq j)))
  · apply ExprCode.const
    exact RatCode.divPos (RatCode.literal 1)
      (RatCode.add (RatCode.add (RatCode.ofNat NatCode.size) (RatCode.ofNat NatCode.universe))
        (RatCode.literal 2)) (fun U _ _ => by positivity)

private abbrev CompileEnv (k ℓ d : ℕ) :=
  (U : ℕ) → (Fin k → Fin U) → Fin ℓ → Address U d

private def EnvCodes {k ℓ d : ℕ} (r : CompileEnv k ℓ d) : Prop :=
  ∀ i, ExprCode k d (fun U t => addressExpr (concreteBackend U d) (r U t i))

private theorem envCodes_cons {k ℓ d : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {r : CompileEnv k ℓ d} (hr : EnvCodes r) (j : Fin d) :
    EnvCodes (fun U t => Fin.cases (.inr j) (r U t)) :=
  Fin.cases (codeXLeaf hc hq j) (fun i => hr i)

private theorem codeCompile {k d ℓ : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (φ : Counting.Formula ℓ) : ∀ (r : CompileEnv k ℓ d), EnvCodes r →
      ∀ (s : ℕ) (h : s + depth φ ≤ d),
        ExprCode k d (fun U t => compile (concreteBackend U d) φ (r U t) s h) := by
  induction φ with
  | atom a =>
    intro r hr s h
    exact codeAtom hc hq a hr
  | neg φ ih =>
    intro r hr s h
    exact codeSub hc hq (ExprCode.const (RatCode.literal 1)) (ih r hr s h)
  | conj φ ψ ih jh =>
    intro r hr s h
    exact codeAnd hc hq (ih r hr s (by simp only [depth] at h; omega))
      (jh r hr s (by simp only [depth] at h; omega))
  | disj φ ψ ih jh =>
    intro r hr s h
    exact codeOr hc hq (ih r hr s (by simp only [depth] at h; omega))
      (jh r hr s (by simp only [depth] at h; omega))
  | ex φ ih =>
    intro r hr s h
    let j : Fin d := ⟨s, by simp only [depth] at h; omega⟩
    exact codeQuant hc hq j (NatCode.const 0)
      (ih _ (envCodes_cons hc hq hr j) (s+1) (by simp only [depth] at h; omega))
  | maj φ ih =>
    intro r hr s h
    let j : Fin d := ⟨s, by simp only [depth] at h; omega⟩
    exact codeQuant hc hq j (NatCode.div NatCode.«universe» (NatCode.const 2))
      (ih _ (envCodes_cons hc hq hr j) (s+1) (by simp only [depth] at h; omega))

/-- The compiled formula and its root guard admit a fixed family evaluator. -/
theorem code_truthExpr {k : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (φ : Counting.Formula (k+1)) :
    ExprCode k (4 + depth φ) (fun _ t => truthExpr φ t) := by
  let d := 4 + depth φ
  let j : Fin d := ⟨0,by dsimp [d]; omega⟩
  let r : CompileEnv k (k+1) d := fun _ t => Fin.cases (.inr j) (Sum.inl ∘ t)
  have hr : EnvCodes r := Fin.cases (codeXLeaf hc hq j)
    (fun i => ExprCode.const (RatCode.ofNat (NatCode.param i)))
  exact codeAnd hc hq (codeCompile hc hq φ r hr 4 le_rfl) (codeGuard hc hq (codeXLeaf hc hq j))

end
end DiophantineNP.Blueprint
