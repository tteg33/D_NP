import DiophantineNP.WidthFormulas

/-! Semantic substitution for the three finite-arithmetic formulas.
The product and sum templates take one binary input relation (row, column).
They each have just one free variable, the queried low output position.
All renaming, addition of free parameters, and substitution under binders
are implemented here. -/
namespace DiophantineNP.WidthFormula
open Counting
noncomputable section

private def liftIndex {a b : ℕ} (σ : Fin a → Fin b) : Fin (a+1) → Fin (b+1) :=
  Fin.cases 0 (fun i => (σ i).succ)

private theorem lift_env {a b U : ℕ} (σ : Fin a → Fin b) (u : Fin U) (env : Fin b → Fin U) :
    Fin.cases u env ∘ liftIndex σ = Fin.cases u (env ∘ σ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private def renameAtom {a b : ℕ} (σ : Fin a → Fin b) : Atom a → Atom b
  | .eqv i j => .eqv (σ i) (σ j)
  | .leq i j => .leq (σ i) (σ j)
  | .add i j t => .add (σ i) (σ j) (σ t)
  | .mul i j t => .mul (σ i) (σ j) (σ t)

private theorem renameAtom_eval {a b U : ℕ} (σ : Fin a → Fin b) (v : Atom a) (env : Fin b → Fin U) :
    (renameAtom σ v).eval env = v.eval (env ∘ σ) := by cases v <;> rfl

private def renameFormula {a : ℕ} (φ : Formula a) : {b : ℕ} → (Fin a → Fin b) → Formula b :=
  match φ with
  | .atom v => fun σ => .atom (renameAtom σ v)
  | .neg v => fun σ => .neg (renameFormula v σ)
  | .conj v w => fun σ => .conj (renameFormula v σ) (renameFormula w σ)
  | .disj v w => fun σ => .disj (renameFormula v σ) (renameFormula w σ)
  | .ex v => fun σ => .ex (renameFormula v (liftIndex σ))
  | .maj v => fun σ => .maj (renameFormula v (liftIndex σ))

private theorem renameFormula_eval {a b U : ℕ} (φ : Formula a) (σ : Fin a → Fin b) (env : Fin b → Fin U) :
    (renameFormula φ σ).eval env = φ.eval (env ∘ σ) := by
  induction φ generalizing b with
  | atom v => exact renameAtom_eval σ v env
  | neg v ih => simp only [renameFormula, Formula.eval, ih]
  | conj v w ih jh => simp only [renameFormula, Formula.eval, ih, jh]
  | disj v w ih jh => simp only [renameFormula, Formula.eval, ih, jh]
  | ex v ih => simp only [renameFormula, Formula.eval, ih, lift_env]
  | maj v ih => simp only [renameFormula, Formula.eval, ih, lift_env]

/-- The published templates may use their binary input relation and BIT in
addition to finite order, addition and multiplication. -/
inductive Template : ℕ → Type
  | atom {k} (a : Atom k) : Template k
  | bit {k} (x j : Fin k) : Template k
  | entry {k} (row col : Fin k) : Template k
  | neg {k} (φ : Template k) : Template k
  | conj {k} (φ ψ : Template k) : Template k
  | disj {k} (φ ψ : Template k) : Template k
  | ex {k} (φ : Template (k+1)) : Template k
  | maj {k} (φ : Template (k+1)) : Template k

def Template.eval {U : ℕ} (entry : Fin U → Fin U → Bool) :
    {k : ℕ} → Template k → (Fin k → Fin U) → Bool
  | _, .atom a, env => a.eval env
  | _, .bit x j, env => (env x).val.testBit (env j).val
  | _, .entry r c, env => entry (env r) (env c)
  | _, .neg φ, env => !(φ.eval entry env)
  | _, .conj φ ψ, env => φ.eval entry env && ψ.eval entry env
  | _, .disj φ ψ, env => φ.eval entry env || ψ.eval entry env
  | _, .ex φ, env => decide (0 < count (fun z => φ.eval entry (Fin.cases z env)))
  | _, .maj φ, env => decide (U/2 < count (fun z => φ.eval entry (Fin.cases z env)))

def pairEnv {β : Type*} (x y : β) : Fin 2 → β := Fin.cases x (fun _ => y)
private theorem comp_pairEnv {a b : Type*} (f : a → b) (x y : a) :
    f ∘ pairEnv x y = pairEnv (f x) (f y) := by
  funext i; fin_cases i <;> rfl

/-- Truth-table specifications for BIT, iterated product and iterated sum,
with a single fixed formula for each operation. -/
structure LiteratureFormulas where
  nativeBit : Formula 2
  bit_correct {U : ℕ} (x j : Fin U) :
    nativeBit.eval (pairEnv x j) = x.val.testBit j.val
  product : Template 1
  sum : Template 1
  product_correct {U : ℕ} (f : ℕ → ℕ) (fits : ∀ t<U, f t<2^U) (j : Fin U) :
    product.eval (fun r c => (f r.val).testBit c.val) (fun _ => j) = (productPrefix f U).testBit j.val
  sum_correct {U : ℕ} (f : ℕ → ℕ) (fits : ∀ t<U, f t<2^U) (j : Fin U) :
    sum.eval (fun r c => (f r.val).testBit c.val) (fun _ => j) = (Readout.prefixSum f U).testBit j.val

/-- Semantics needed to substitute a binary digit predicate under a binder. -/
structure BitTemplate where
  nativeBit : Formula 2
  bit_correct {U : ℕ} (x j : Fin U) :
    nativeBit.eval (pairEnv x j) = x.val.testBit j.val

instance : Coe LiteratureFormulas BitTemplate :=
  ⟨fun L => ⟨L.nativeBit, L.bit_correct⟩⟩

private def bitFromTemplate {k : ℕ} (L : BitTemplate) (x j : Fin k) : Formula k :=
  renameFormula L.nativeBit (pairEnv x j)

private theorem nativeBit_eval {k U : ℕ} (L : BitTemplate) (x j : Fin k) (env : Fin k → Fin U) :
    (bitFromTemplate L x j).eval env = (env x).val.testBit (env j).val := by
  rw [bitFromTemplate, renameFormula_eval, comp_pairEnv, L.bit_correct]

private def insertIndices {k l : ℕ} (row col : Fin l) (params : Fin k → Fin l) :
    Fin (k+2) → Fin l := Fin.cases col (Fin.cases row params)

private theorem comp_insertIndices {k l U : ℕ} (env : Fin l → Fin U) (r c : Fin l) (p : Fin k → Fin l) :
    env ∘ insertIndices r c p = extend (env c) (env r) (env ∘ p) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i <;> rfl

/-- Interpret the additional relation by its supplied formula. Under a binder
we lift both the template variables and the independent free-parameter map. -/
def substitute {k a : ℕ} (L : BitTemplate) (input : Formula (k+2)) (φ : Template a) :
    {l : ℕ} → (Fin a → Fin l) → (Fin k → Fin l) → Formula l :=
  match φ with
  | .atom v => fun σ _ => .atom (renameAtom σ v)
  | .bit i j => fun σ _ => bitFromTemplate L (σ i) (σ j)
  | .entry r c => fun σ p => renameFormula input (insertIndices (σ r) (σ c) p)
  | .neg v => fun σ p => .neg (substitute L input v σ p)
  | .conj v w => fun σ p => .conj (substitute L input v σ p) (substitute L input w σ p)
  | .disj v w => fun σ p => .disj (substitute L input v σ p) (substitute L input w σ p)
  | .ex v => fun σ p => .ex (substitute L input v (liftIndex σ) (Fin.succ ∘ p))
  | .maj v => fun σ p => .maj (substitute L input v (liftIndex σ) (Fin.succ ∘ p))

private theorem pass_params {l k U : ℕ} (z : Fin U) (env : Fin l → Fin U) (p : Fin k → Fin l) :
    Fin.cases z env ∘ (Fin.succ ∘ p) = env ∘ p := by funext i; rfl

theorem substitute_eval {k a l U : ℕ} (L : BitTemplate) (input : Formula (k+2)) (φ : Template a)
    (σ : Fin a → Fin l) (p : Fin k → Fin l) (env : Fin l → Fin U) :
    (substitute L input φ σ p).eval env =
    φ.eval (fun r c => input.eval (extend c r (env ∘ p))) (env ∘ σ) := by
  induction φ generalizing l with
  | atom v => exact renameAtom_eval σ v env
  | bit x j => exact nativeBit_eval L _ _ env
  | entry r c => simp only [substitute, renameFormula_eval, comp_insertIndices, Template.eval, Function.comp_apply]
  | neg v ih => simp only [substitute, Formula.eval, Template.eval, ih]
  | conj v w ih jh => simp only [substitute, Formula.eval, Template.eval, ih, jh]
  | disj v w ih jh => simp only [substitute, Formula.eval, Template.eval, ih, jh]
  | ex v ih => simp only [substitute, Formula.eval, Template.eval, ih, lift_env, pass_params]
  | maj v ih => simp only [substitute, Formula.eval, Template.eval, ih, lift_env, pass_params]

/-- Single-template substitution yields the syntax transformers used by
the complete construction of `widthDescriptions`. -/
def LiteratureFormulas.arithmetic (L : LiteratureFormulas) : Arithmetic where
  bit := bitFromTemplate L
  bit_spec := nativeBit_eval L
  product j input := substitute L input L.product (fun _ => j) id
  sum j input := substitute L input L.sum (fun _ => j) id
  product_spec j input env f fits correct := by
    rw [substitute_eval]
    change L.product.eval (fun r c => input.eval (extend c r env)) (fun _ => env j) = _
    have h : (fun r c => input.eval (extend c r env)) = fun r c => (f r.val).testBit c.val :=
      funext fun r => funext fun c => correct c r
    rw [h, L.product_correct f fits]
  sum_spec j input env f fits correct := by
    rw [substitute_eval]
    change L.sum.eval (fun r c => input.eval (extend c r env)) (fun _ => env j) = _
    have h : (fun r c => input.eval (extend c r env)) = fun r c => (f r.val).testBit c.val :=
      funext fun r => funext fun c => correct c r
    rw [h, L.sum_correct f fits]

theorem widthDescriptions_of_literature (L : LiteratureFormulas) : Packing.WidthDescriptions :=
  widthDescriptions L.arithmetic

end
end DiophantineNP.WidthFormula
