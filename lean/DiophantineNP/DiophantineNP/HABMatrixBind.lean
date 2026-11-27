import DiophantineNP.SmallSumTemplate

/-! Capture-avoiding substitution of a parameterized binary input relation
in a finite template. The replacement may itself inspect the original matrix. -/
namespace DiophantineNP.HABMatrix
open Counting WidthFormula FiniteArithmeticGap

private def lift {a b : ℕ} (f : Fin a → Fin b) : Fin (a+1) → Fin (b+1) :=
  Fin.cases 0 (Fin.succ ∘ f)

private theorem lift_spec {a b U : ℕ} (f : Fin a → Fin b) (e : Fin b → Fin U) (z : Fin U) :
    Fin.cases z e ∘ lift f = Fin.cases z (e ∘ f) := by
  funext i; refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

private def rename {a b : ℕ} (p : Template a) (f : Fin a → Fin b) : Template b :=
  rewriteMatrix (fun i j => .entry i j) p f

private theorem rename_spec {a b U : ℕ} (p : Template a) (f : Fin a → Fin b)
    (A : Fin U → Fin U → Bool) (e : Fin b → Fin U) :
    (rename p f).eval A e=p.eval A (e ∘ f) :=
  rewriteMatrix_eval _ A A (by intros; rfl) _ _ _

/-- Free slots 0 and 1 of the replacement are the column and row. Remaining
slots are ambient parameters, shifted under quantifiers in the outer template. -/
def bind {n a : ℕ} (cell : Template (n+2)) (p : Template a) :
    {k : ℕ} → (Fin n → Fin k) → (Fin a → Fin k) → Template k :=
  match p with
  | .atom v => fun _ f => rename (.atom v) f
  | .bit x j => fun _ f => .bit (f x) (f j)
  | .entry r c => fun g f => rename cell (Fin.cases (f c) (Fin.cases (f r) g))
  | .neg q => fun g f => .neg (bind cell q g f)
  | .conj q t => fun g f => .conj (bind cell q g f) (bind cell t g f)
  | .disj q t => fun g f => .disj (bind cell q g f) (bind cell t g f)
  | .ex q => fun g f => .ex (bind cell q (Fin.succ ∘ g) (lift f))
  | .maj q => fun g f => .maj (bind cell q (Fin.succ ∘ g) (lift f))

theorem bind_spec {n a k U : ℕ} (cell : Template (n+2)) (p : Template a)
    (g : Fin n → Fin k) (f : Fin a → Fin k) (A : Fin U → Fin U → Bool) (e : Fin k → Fin U) :
    (bind cell p g f).eval A e =
    p.eval (fun r c => cell.eval A (extend c r (e ∘ g))) (e ∘ f) := by
  induction p generalizing k with
  | atom v => exact rename_spec .. 
  | bit x j => rfl
  | entry r c =>
    rw [bind,rename_spec]
    apply congrArg (cell.eval A)
    funext i; refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun _ => rfl) j
  | neg q ih => simp only [bind,Template.eval,ih]
  | conj q t ih jh => simp only [bind,Template.eval,ih,jh]
  | disj q t ih jh => simp only [bind,Template.eval,ih,jh]
  | ex q ih => simp only [bind,Template.eval,ih,lift_spec]; rfl
  | maj q ih => simp only [bind,Template.eval,ih,lift_spec]; rfl

end DiophantineNP.HABMatrix
