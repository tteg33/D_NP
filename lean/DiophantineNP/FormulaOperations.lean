import DiophantineNP.FormulaLeaves
/-! # Laurent expressions for the scalar operations of the formula evaluator -/
namespace DiophantineNP.FormulaLaurent
open Counting ConcreteGrid LaurentBounds
open scoped BigOperators
noncomputable section
variable {d U : ℕ}

abbrev const {d : ℕ} (q : ℚ) : Expr d := rational q
def sub (a b : Expr d) : Expr d := .add a (.neg b)

@[simp] theorem eval_const (q : ℚ) (χ : Character d ℂ) :
    (const q).evaluate χ = (q : ℂ) := rational_eval q χ

@[simp] theorem eval_sub (a b : Expr d) (χ : Character d ℂ) :
    (sub a b).evaluate χ = a.evaluate χ - b.evaluate χ := by
  rw [sub, Expr.evaluate_add]
  simp [Expr.evaluate, Expr.expand, Expr.bounds, Raw.evaluate_scale, sub_eq_add_neg, neg_div]

def halfDegree (U : ℕ) : ℕ :=
  2^15*(size U)^8*(precision U+20*((size U).log2+1)+100)

def tail (U : ℕ) (e : Expr d) : Expr d :=
  e.threshold (2*halfDegree U+1) (halfDegree U+1)

theorem eval_tail {x : ℝ} {e : Expr d} (χ : Character d ℂ) (h : e.evaluate χ = (x:ℂ)) :
    (tail U e).evaluate χ = (((gate U).H x : ℝ) : ℂ) := by
  let m := halfDegree U
  change (e.threshold (2*m+1) (m+1)).evaluate χ = ((DiophantineNP.Threshold.majority m x : ℝ):ℂ)
  rw [Expr.evaluate_threshold, h, DiophantineNP.Threshold.majority, DiophantineNP.Threshold.lowerTail_eq_upper]
  push_cast
  let A : ℕ → ℂ := fun i => ((2*m+1).choose i : ℂ)*((1+(x:ℂ))/2)^i*((1-(x:ℂ))/2)^(2*m+1-i)
  change (∑ i : Fin (2*m+1+1), (fun j : ℕ => if m+1 ≤ j then A j else 0) i.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if m+1 ≤ j then A j else 0) (2*m+1+1), ← Finset.sum_filter]
  have he : (Finset.range (2*m+1+1)).filter (fun i => m+1 ≤ i) = Finset.Ico (m+1) (2*m+2) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [A]
  ring

def andExpr (U : ℕ) (f g : Expr d) : Expr d :=
  tail U ((sub (f.add g) (const (3/2))).mul (const (1/4)))

def orExpr (U : ℕ) (f g : Expr d) : Expr d :=
  tail U ((sub (f.add g) (const (1/2))).mul (const (1/4)))

theorem eval_and {f g : Expr d} (χ : Character d ℂ) {x y : ℝ}
    (hx : f.evaluate χ = (x:ℂ)) (hy : g.evaluate χ = (y:ℂ)) :
    (andExpr U f g).evaluate χ = ((andGate (gate U) x y : ℝ):ℂ) := by
  unfold andExpr andGate
  apply eval_tail
  rw [Expr.evaluate_mul, eval_sub, Expr.evaluate_add, eval_const, eval_const, hx, hy]
  push_cast
  ring

theorem eval_or {f g : Expr d} (χ : Character d ℂ) {x y : ℝ}
    (hx : f.evaluate χ = (x:ℂ)) (hy : g.evaluate χ = (y:ℂ)) :
    (orExpr U f g).evaluate χ = ((orGate (gate U) x y : ℝ):ℂ) := by
  unfold orExpr orGate
  apply eval_tail
  rw [Expr.evaluate_mul, eval_sub, Expr.evaluate_add, eval_const, eval_const, hx, hy]
  push_cast
  ring

def normalize (U : ℕ) (x : Expr d) : Expr d :=
  x.mul (const (1/(8*(size U : ℚ)^4)))

private theorem eval_normalize {f : Expr d} (χ : Character d ℂ) {x : ℝ}
    (hx : f.evaluate χ = (x:ℂ)) :
    (normalize U f).evaluate χ = ((x/(8*(size U:ℝ)^4) : ℝ):ℂ) := by
  rw [normalize, Expr.evaluate_mul, eval_const, hx]
  push_cast
  ring

def guardExpr (U : ℕ) (x : Expr d) : Expr d :=
  tail U (normalize U ((sub (sub (const U) (const 1)) x).add (const (1/2))))

theorem eval_guard {f : Expr d} (χ : Character d ℂ) {x : ℝ} (hx : f.evaluate χ = (x:ℂ)) :
    (guardExpr U f).evaluate χ = (((gate U).H (guardArgument U x) : ℝ):ℂ) := by
  unfold guardExpr guardArgument
  apply eval_tail
  apply eval_normalize
  simp only [Expr.evaluate_add, eval_sub, eval_const, hx]
  push_cast
  ring

def residual {k : ℕ} (a : Atom k) (z : Fin k → Expr d) : Expr d :=
  match a with
  | .eqv i j => sub (z i) (z j)
  | .leq i j => sub (z j) (z i)
  | .add i j l => sub ((z i).add (z j)) (z l)
  | .mul i j l => sub ((z i).mul (z j)) (z l)

def atomExpr {k : ℕ} (U : ℕ) (a : Atom k) (z : Fin k → Expr d) : Expr d :=
  let r := residual a z
  tail U (normalize U (if a.isOrder then r.add (const (1/2)) else sub (const (1/4)) (r.pow 2)))

theorem eval_atom {k : ℕ} (χ : Character d ℂ) (a : Atom k) {z : Fin k → Expr d} {v : Fin k → ℝ}
    (h : ∀ i, (z i).evaluate χ = (v i:ℂ)) :
    (atomExpr U a z).evaluate χ = (((gate U).H (atomArgument a v (size U)) : ℝ):ℂ) := by
  have hr : (residual a z).evaluate χ = ((a.residual v : ℝ) : ℂ) := by
    cases a <;> simp [residual, Atom.residual, eval_sub, Expr.evaluate_add, Expr.evaluate_mul, h]
  unfold atomExpr atomArgument
  apply eval_tail
  cases hm : a.isOrder <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · apply eval_normalize
    simp only [eval_sub, eval_const, Expr.evaluate_pow, hr]
    push_cast
    ring
  · apply eval_normalize
    simp only [Expr.evaluate_add, eval_const, hr]
    push_cast
    ring

/-- A single cyclic projection calculates the guarded half-sum. -/
def quantExpr (B : Backend U d) (j : Fin d) (k : ℕ) (child : Expr d) : Expr d :=
  let guarded := andExpr U child (guardExpr U (B.x j))
  let avg := ((tail U (B.y j)).mul guarded).project j (period U)
  let C := (const ((size U:ℚ)/2)).mul avg
  tail U ((sub (sub C (const k)) (const (1/2))).mul (const (1/((size U:ℚ)+U+2))))

theorem eval_quant (B : Backend U d) (j : Fin d) (k : ℕ) {e : Expr d}
    (z : Fin d → Point U) {f : Point U → ℝ}
    (hf : ∀ v, e.evaluate (B.char (Function.update z j v)) = (f v:ℂ)) :
    (quantExpr B j k e).evaluate (B.char z) = ((quantify (observed U).tests k f : ℝ):ℂ) := by
  let g := (observed U).tests
  let wexpr := ((tail U (B.y j)).mul (andExpr U e (guardExpr U (B.x j))))
  have hw (v : Point U) : wexpr.evaluate (B.char (Function.update z j v)) =
      ((g.window v * andGate g.threshold (f v) (g.guard v) : ℝ):ℂ) := by
    have hy := B.eval_y j (Function.update z j v)
    have hx := B.eval_x j (Function.update z j v)
    simp only [Function.update_self] at hx hy
    change ((_ : Expr d).mul _).evaluate _ = _
    rw [Expr.evaluate_mul, Complex.ofReal_mul, eval_tail _ hy]
    exact congrArg (fun c : ℂ => _ * c) (eval_and _ (hf v) (eval_guard _ hx))
  have hM : (size U:ℂ) ≠ 0 := by exact_mod_cast (period U).ne_zero
  have hgs : gridSize U (Invalid U) (Outside U) = (size U:ℝ) := by
    simp [gridSize, (observed U).card_eq]
  have hC : ((const ((size U:ℚ)/2)).mul (wexpr.project j (period U))).evaluate (B.char z) =
      ((halfSum g f : ℝ):ℂ) := by
    rw [Expr.evaluate_mul, eval_const, B.eval_project]
    simp_rw [hw]
    unfold halfSum
    push_cast
    field_simp
  unfold quantExpr quantify
  apply eval_tail
  change (((sub (sub _ _) _).mul _).evaluate _ : ℂ) = _
  rw [Expr.evaluate_mul, eval_sub, eval_sub, hC, eval_const, eval_const, eval_const, hgs]
  push_cast
  ring

end
end DiophantineNP.FormulaLaurent
