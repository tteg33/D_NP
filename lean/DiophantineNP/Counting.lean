import DiophantineNP.Threshold
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Guarded counting on the finite grid

The three kinds of grid points are the two representatives of each valid
label, selected representatives of out-of-domain labels, and points outside
the window. This file treats the scalar threshold approximation, window, and
coordinate parametrization as inputs. It proves how errors propagate through
the Boolean operations and a strict count threshold in §3.3.
-/

namespace DiophantineNP.Counting

open scoped BigOperators

noncomputable section

def bit (b : Bool) : ℝ := if b then 1 else 0

def UnitValue (x : ℝ) : Prop := 0 ≤ x ∧ x ≤ 1

/-- The analytic contract of the binomial-tail polynomial. -/
structure Threshold (ε δ : ℝ) where
  H : ℝ → ℝ
  unit : ∀ t, -1 ≤ t → t ≤ 1 → UnitValue (H t)
  low : ∀ t, -1 ≤ t → t ≤ -δ → |H t - 0| ≤ ε
  high : ∀ t, δ ≤ t → t ≤ 1 → |H t - 1| ≤ ε

/-- The bins of the manuscript's explicit odd degree instantiate the gate
contract. The exponent parameter `l` can be set to the binary length of M. -/
def draftThreshold (M q l : ℕ) (hM : 0 < M) :
    Threshold (((2:ℝ)^q)⁻¹) (1/(64*(M:ℝ)^4)) where
  H := DiophantineNP.Threshold.majority (2^15*M^8*(q+20*l+100))
  unit := fun _ a b => DiophantineNP.Threshold.majority_range _ (abs_le.mpr ⟨a,b⟩)
  low := by
    intro t lo hi
    have hM' : (0:ℝ) < M := by exact_mod_cast hM
    have dpos : 0 < 1/(64*(M:ℝ)^4) := by positivity
    have ht : t ≤ 0 := by linarith
    have margin : 1/(64*(M:ℝ)^4) ≤ |t| := by rw [abs_of_nonpos ht]; linarith
    have h := DiophantineNP.Threshold.draft_degree_precision M q l hM
      (abs_le.mpr ⟨lo, by linarith⟩) margin
    simpa only [if_neg (not_lt.mpr ht)] using h.le
  high := by
    intro t lo hi
    have hM' : (0:ℝ) < M := by exact_mod_cast hM
    have dpos : 0 < 1/(64*(M:ℝ)^4) := by positivity
    have ht : 0 < t := dpos.trans_le lo
    have margin : 1/(64*(M:ℝ)^4) ≤ |t| := by rw [abs_of_pos ht]; exact lo
    have h := DiophantineNP.Threshold.draft_degree_precision M q l hM
      (abs_le.mpr ⟨by linarith, hi⟩) margin
    simpa only [if_pos ht] using h.le

def andGate {ε δ : ℝ} (T : Threshold ε δ) (x y : ℝ) : ℝ :=
  T.H ((x + y - 3/2) / 4)

def orGate {ε δ : ℝ} (T : Threshold ε δ) (x y : ℝ) : ℝ :=
  T.H ((x + y - 1/2) / 4)

theorem andGate_unit {ε δ x y : ℝ} (T : Threshold ε δ)
    (hx : UnitValue x) (hy : UnitValue y) : UnitValue (andGate T x y) :=
  T.unit _ (by rcases hx with ⟨_,_⟩; rcases hy with ⟨_,_⟩; linarith)
    (by rcases hx with ⟨_,_⟩; rcases hy with ⟨_,_⟩; linarith)

theorem orGate_unit {ε δ x y : ℝ} (T : Threshold ε δ)
    (hx : UnitValue x) (hy : UnitValue y) : UnitValue (orGate T x y) :=
  T.unit _ (by rcases hx with ⟨_,_⟩; rcases hy with ⟨_,_⟩; linarith)
    (by rcases hx with ⟨_,_⟩; rcases hy with ⟨_,_⟩; linarith)

theorem negate_error {ε x : ℝ} {b : Bool} (h : |x - bit b| ≤ ε) :
    |(1 - x) - bit (!b)| ≤ ε := by
  rcases abs_le.mp h with ⟨hl,hr⟩
  apply abs_le.mpr
  cases b <;> simp only [Bool.not_false, Bool.not_true, bit, Bool.false_eq_true, ↓reduceIte] at *
  all_goals constructor <;> linarith

theorem andGate_error {ε δ x y : ℝ} {a b : Bool} (T : Threshold ε δ)
    (hε : ε ≤ 1/16) (hδ : δ ≤ 1/16)
    (hx : |x - bit a| ≤ ε) (hy : |y - bit b| ≤ ε) :
    |andGate T x y - bit (a && b)| ≤ ε := by
  rw [abs_le] at hx hy
  rcases hx with ⟨_, _⟩
  rcases hy with ⟨_, _⟩
  cases a <;> cases b <;> simp only [Bool.and_false, Bool.and_true, bit, Bool.false_eq_true,
    ↓reduceIte] at * <;> first | apply T.low <;> linarith | apply T.high <;> linarith

theorem orGate_error {ε δ x y : ℝ} {a b : Bool} (T : Threshold ε δ)
    (hε : ε ≤ 1/16) (hδ : δ ≤ 1/16)
    (hx : |x - bit a| ≤ ε) (hy : |y - bit b| ≤ ε) :
    |orGate T x y - bit (a || b)| ≤ ε := by
  rw [abs_le] at hx hy
  rcases hx with ⟨_, _⟩
  rcases hy with ⟨_, _⟩
  cases a <;> cases b <;> simp only [Bool.or_false, Bool.or_true, bit, Bool.false_eq_true,
    ↓reduceIte] at * <;> first | apply T.low <;> linarith | apply T.high <;> linarith

/-- A false guard suppresses an arbitrary child in [0,1]. -/
theorem andGate_false_guard {ε δ x g : ℝ} (T : Threshold ε δ)
    (hε : ε ≤ 1/16) (hδ : δ ≤ 1/16) (hx : UnitValue x) (hg : |g - 0| ≤ ε) :
    |andGate T x g - 0| ≤ ε := by
  rcases hx with ⟨_,_⟩
  rcases abs_le.mp hg with ⟨_,_⟩
  apply T.low <;> linarith

/-- Two representatives per valid label. The last two summands distinguish
selected invalid labels from points outside the geometric window. -/
abbrev Grid (L I O : Type*) := ((L × Bool) ⊕ I) ⊕ O

def ideal {L I O : Type*} (p : L → Bool) : Grid L I O → ℝ
  | .inl (.inl (i, _)) => bit (p i)
  | .inl (.inr _) => 0
  | .inr _ => 0

def count {L : Type*} [Fintype L] (p : L → Bool) : ℕ :=
  (Finset.univ.filter (fun i => p i = true)).card

/-- Summing the ideal truth values counts each true label exactly twice. -/
theorem sum_ideal {L I O : Type*} [Fintype L] [Fintype I] [Fintype O] (p : L → Bool) :
    ∑ z : Grid L I O, ideal p z = 2 * (count p : ℝ) := by
  classical
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, ideal]
  simp [bit, count, two_mul, Finset.sum_add_distrib]

private theorem window_mul_error {ε w g : ℝ} (b : Bool)
    (hw : UnitValue w) (hg : UnitValue g)
    (win : |w - 1| ≤ ε) (child : |g - bit b| ≤ ε) :
    |w*g - bit b| ≤ 2*ε := by
  rcases hw with ⟨hw0,hw1⟩
  rcases hg with ⟨hg0,hg1⟩
  have hε : 0 ≤ ε := (abs_nonneg _).trans win
  have wm : w*g ≤ g := by nlinarith [mul_nonneg (sub_nonneg.mpr hw1) hg0]
  have gm : g - w*g ≤ 1-w := by nlinarith [mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hg1)]
  cases b <;> simp only [bit, Bool.false_eq_true, ↓reduceIte] at *
  all_goals
    rcases abs_le.mp win with ⟨_,_⟩
    rcases abs_le.mp child with ⟨_,_⟩
    apply abs_le.mpr
    constructor <;> linarith

/-- If the guarded child has the right value on valid labels and is small
on invalid selected labels, the half-sum has error at most M ε.
No approximation of the child is assumed on off-window points. -/
theorem guarded_count_error {L I O : Type*} [Fintype L] [Fintype I] [Fintype O]
    {ε : ℝ} (hε : 0 ≤ ε) (p : L → Bool) (w g : Grid L I O → ℝ)
    (hw : ∀ z, UnitValue (w z)) (hg : ∀ z, UnitValue (g z))
    (hsel : ∀ z : (L × Bool) ⊕ I, |w (.inl z) - 1| ≤ ε)
    (hoff : ∀ z : O, |w (.inr z) - 0| ≤ ε)
    (hvalid : ∀ i b, |g (.inl (.inl (i, b))) - bit (p i)| ≤ ε)
    (hinvalid : ∀ i : I, |g (.inl (.inr i)) - 0| ≤ ε) :
    |(∑ z, w z * g z) / 2 - (count p : ℝ)| ≤ (Fintype.card (Grid L I O) : ℝ) * ε := by
  classical
  have pt (z : Grid L I O) : |w z * g z - ideal p z| ≤ 2*ε := by
    rcases z with ((⟨i,b⟩ | i) | o)
    · exact window_mul_error _ (hw _) (hg _) (hsel _) (hvalid i b)
    · exact window_mul_error false (hw _) (hg _) (hsel _) (hinvalid i)
    · have hw' := hoff o
      rcases hw (.inr o) with ⟨w₀,_⟩
      rcases hg (.inr o) with ⟨g₀,g₁⟩
      change |w (.inr o)*g (.inr o) - 0| ≤ 2*ε
      rw [sub_zero, abs_of_nonneg (mul_nonneg w₀ g₀)]
      have := (abs_le.mp hw').2
      nlinarith [mul_nonneg w₀ (sub_nonneg.mpr g₁)]
  have aux : |∑ z, (w z * g z - ideal p z)| ≤ ∑ _z : Grid L I O, 2*ε := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun z _ => pt z))
  rw [Finset.sum_sub_distrib, sum_ideal] at aux
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at aux
  rcases abs_le.mp aux with ⟨_,_⟩
  apply abs_le.mpr
  constructor <;> linarith

/-- A half-integer separates both outcomes even at a tie. With k=0 this
implements existence; with k=U/2 (natural division), strict majority. -/
theorem countThreshold_error {ε δ C A : ℝ} {c k : ℕ} (T : Threshold ε δ)
    (hA : 0 < A) (hd : δ ≤ (1/4)/A) (hC : |C - (c : ℝ)| ≤ 1/8)
    (hlo : -1 ≤ (C - k - 1/2)/A) (hhi : (C - k - 1/2)/A ≤ 1) :
    |T.H ((C - k - 1/2)/A) - bit (decide (k < c))| ≤ ε := by
  rcases abs_le.mp hC with ⟨_,_⟩
  by_cases h : k < c
  · have h' : (k : ℝ) + 1 ≤ c := by exact_mod_cast (Nat.succ_le_of_lt h)
    simp only [h, decide_true, bit, ↓reduceIte]
    apply T.high _ _ hhi
    exact hd.trans ((div_le_div_iff_of_pos_right hA).mpr (by linarith))
  · have h' : (c : ℝ) ≤ k := by exact_mod_cast Nat.le_of_not_gt h
    simp only [h, decide_false, bit, Bool.false_eq_true, ↓reduceIte]
    apply T.low _ hlo
    calc
      _ ≤ (-(1/4))/A := (div_le_div_iff_of_pos_right hA).mpr (by linarith)
      _ = -((1/4)/A) := neg_div _ _
      _ ≤ -δ := neg_le_neg hd

/-- Addition and multiplication use natural-number results. In particular,
overflow in `Fin U` can never make an atomic relation true. -/
inductive Atom (k : ℕ)
  | eqv (i j : Fin k)
  | leq (i j : Fin k)
  | add (i j t : Fin k)
  | mul (i j t : Fin k)

def Atom.eval {k U : ℕ} (a : Atom k) (ρ : Fin k → Fin U) : Bool :=
  match a with
  | .eqv i j => decide (ρ i = ρ j)
  | .leq i j => decide (ρ i ≤ ρ j)
  | .add i j t => decide ((ρ i).val + (ρ j).val = (ρ t).val)
  | .mul i j t => decide ((ρ i).val * (ρ j).val = (ρ t).val)

inductive Formula : ℕ → Type
  | atom {k} (a : Atom k) : Formula k
  | neg {k} (φ : Formula k) : Formula k
  | conj {k} (φ ψ : Formula k) : Formula k
  | disj {k} (φ ψ : Formula k) : Formula k
  | ex {k} (φ : Formula (k+1)) : Formula k
  | maj {k} (φ : Formula (k+1)) : Formula k

/-- A bound variable occupies slot zero. The semantics uses strict majority. -/
def Formula.eval {U : ℕ} : {k : ℕ} → Formula k → (Fin k → Fin U) → Bool
  | _, .atom a, ρ => a.eval ρ
  | _, .neg φ, ρ => !(φ.eval ρ)
  | _, .conj φ ψ, ρ => φ.eval ρ && ψ.eval ρ
  | _, .disj φ ψ, ρ => φ.eval ρ || ψ.eval ρ
  | _, .ex φ, ρ => decide (0 < count (fun i => φ.eval (Fin.cases i ρ)))
  | _, .maj φ, ρ => decide (U/2 < count (fun i => φ.eval (Fin.cases i ρ)))

section Model

variable {U : ℕ} {I O : Type} [Fintype I] [Fintype O] {ε δ : ℝ}

abbrev LabelGrid (U : ℕ) (I O : Type) := Grid (Fin U) I O

/-- Environments match when every point is either copy of its assigned label. -/
def Matches {k : ℕ} (u : Fin k → Fin U) (z : Fin k → LabelGrid U I O) : Prop :=
  ∀ i, ∃ b : Bool, z i = Sum.inl (Sum.inl (u i, b))

omit [Fintype I] [Fintype O] in
private theorem matches_cons {k : ℕ} {u : Fin k → Fin U} {z : Fin k → LabelGrid U I O}
    (h : Matches u z) (i : Fin U) (b : Bool) :
    Matches (Fin.cases i u) (Fin.cases (.inl (.inl (i,b))) z) :=
  Fin.cases (by exact ⟨b, rfl⟩) (by intro j; exact h j)

def gridSize (U : ℕ) (I O : Type) [Fintype I] [Fintype O] : ℝ :=
  Fintype.card (LabelGrid U I O)

/-- Explicit hypotheses supplied by the threshold, label and window estimates
in §3.1–3.2. No Diophantine graph or bit-length assertion is assumed here. -/
structure GridTests (U : ℕ) (I O : Type) [Fintype I] [Fintype O] (ε δ : ℝ) where
  threshold : Threshold ε δ
  eps_nonneg : 0 ≤ ε
  eps_small : ε ≤ 1/16
  delta_small : δ ≤ 1/16
  sum_error : gridSize U I O * ε ≤ 1/8
  count_margin : δ ≤ (1/4)/(gridSize U I O + U + 2)
  window : LabelGrid U I O → ℝ
  window_unit : ∀ z, UnitValue (window z)
  window_selected : ∀ z, |window (.inl z) - 1| ≤ ε
  window_off : ∀ o, |window (.inr o) - 0| ≤ ε
  guard : LabelGrid U I O → ℝ
  guard_unit : ∀ z, UnitValue (guard z)
  guard_valid : ∀ i b, |guard (.inl (.inl (i,b))) - 1| ≤ ε
  guard_invalid : ∀ i, |guard (.inl (.inr i)) - 0| ≤ ε
  atom : ∀ {k}, Atom k → (Fin k → LabelGrid U I O) → ℝ
  atom_unit : ∀ {k} (a : Atom k) z, UnitValue (atom a z)
  atom_error : ∀ {k} (a : Atom k) u z, Matches u z → |atom a z - bit (a.eval u)| ≤ ε

variable (T : GridTests U I O ε δ)

noncomputable def halfSum (f : LabelGrid U I O → ℝ) : ℝ :=
  (∑ z, T.window z * andGate T.threshold (f z) (T.guard z)) / 2

noncomputable def quantify (k : ℕ) (f : LabelGrid U I O → ℝ) : ℝ :=
  T.threshold.H ((halfSum T f - k - 1/2)/(gridSize U I O + U + 2))

private theorem quantArg_range {k : ℕ} (hk : k ≤ U) (f : LabelGrid U I O → ℝ)
    (unit : ∀ z, UnitValue (f z)) :
    -1 ≤ (halfSum T f - k - 1/2)/(gridSize U I O + U + 2) ∧
      (halfSum T f - k - 1/2)/(gridSize U I O + U + 2) ≤ 1 := by
  have hsum_lo : 0 ≤ ∑ z, T.window z * andGate T.threshold (f z) (T.guard z) :=
    Finset.sum_nonneg fun z _ => mul_nonneg (T.window_unit z).1
      (andGate_unit _ (unit z) (T.guard_unit z)).1
  have hsum_hi : (∑ z, T.window z * andGate T.threshold (f z) (T.guard z)) ≤
      ∑ _z : LabelGrid U I O, (1 : ℝ) := Finset.sum_le_sum fun z _ =>
    mul_le_one₀ (T.window_unit z).2 (andGate_unit _ (unit z) (T.guard_unit z)).1
      (andGate_unit _ (unit z) (T.guard_unit z)).2
  have hM : 0 ≤ gridSize U I O := by unfold gridSize; positivity
  have hA : 0 < gridSize U I O + U + 2 := by positivity
  have hk' : (k : ℝ) ≤ U := by exact_mod_cast hk
  change -1 ≤ _ / _ ∧ _ / _ ≤ 1
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum_hi
  change _ ≤ gridSize U I O at hsum_hi
  unfold halfSum
  constructor
  · apply (le_div_iff₀ hA).mpr
    linarith
  · apply (div_le_iff₀ hA).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) U]

theorem quantify_unit {k : ℕ} (hk : k ≤ U) (f : LabelGrid U I O → ℝ)
    (unit : ∀ z, UnitValue (f z)) : UnitValue (quantify T k f) :=
  T.threshold.unit _ (quantArg_range T hk f unit).1 (quantArg_range T hk f unit).2

theorem quantify_error {k : ℕ} (hk : k ≤ U) (f : LabelGrid U I O → ℝ) (p : Fin U → Bool)
    (unit : ∀ z, UnitValue (f z))
    (valid : ∀ i b, |f (.inl (.inl (i,b))) - bit (p i)| ≤ ε) :
    |quantify T k f - bit (decide (k < count p))| ≤ ε := by
  have hf : |halfSum T f - (count p : ℝ)| ≤ gridSize U I O * ε :=
    guarded_count_error T.eps_nonneg p T.window
      (fun z => andGate T.threshold (f z) (T.guard z)) T.window_unit
      (fun z => andGate_unit _ (unit z) (T.guard_unit z)) T.window_selected T.window_off
      (fun i b => by
        simpa only [Bool.and_true] using andGate_error (b := true) T.threshold T.eps_small
          T.delta_small (valid i b) (T.guard_valid i b))
      (fun j => andGate_false_guard T.threshold T.eps_small T.delta_small (unit _) (T.guard_invalid j))
  have hM : 0 ≤ gridSize U I O := by unfold gridSize; positivity
  exact countThreshold_error T.threshold (by positivity) T.count_margin (hf.trans T.sum_error)
    (quantArg_range T hk f unit).1 (quantArg_range T hk f unit).2

/-- The real-valued expression determined by the Boolean and counting rules
on this grid. Realizability of each expression as a Laurent polynomial and
the evaluation of such polynomials as Diophantine graphs are separate steps. -/
noncomputable def Formula.gridEval : {k : ℕ} → Formula k → (Fin k → LabelGrid U I O) → ℝ
  | _, .atom a, z => T.atom a z
  | _, .neg φ, z => 1 - φ.gridEval z
  | _, .conj φ ψ, z => andGate T.threshold (φ.gridEval z) (ψ.gridEval z)
  | _, .disj φ ψ, z => orGate T.threshold (φ.gridEval z) (ψ.gridEval z)
  | _, .ex φ, z => quantify T 0 (fun x => φ.gridEval (Fin.cases x z))
  | _, .maj φ, z => quantify T (U/2) (fun x => φ.gridEval (Fin.cases x z))

theorem Formula.gridEval_unit {k : ℕ} (φ : Formula k) :
    ∀ z, UnitValue (φ.gridEval T z) := by
  induction φ with
  | atom a => exact T.atom_unit a
  | neg φ ih =>
    intro z
    obtain ⟨l,r⟩ := ih z
    change 0 ≤ 1 - _ ∧ 1 - _ ≤ 1
    constructor <;> linarith
  | conj φ ψ ih jh => exact fun z => andGate_unit _ (ih z) (jh z)
  | disj φ ψ ih jh => exact fun z => orGate_unit _ (ih z) (jh z)
  | ex φ ih => exact fun _ => quantify_unit T (Nat.zero_le U) _ (fun _ => ih _)
  | maj φ ih => exact fun _ => quantify_unit T (Nat.div_le_self U 2) _ (fun _ => ih _)

/-- Structural induction for all formulas, including nested strict-majority
and existence quantifiers. Every clause restores the same error budget ε. -/
theorem Formula.gridEval_correct {k : ℕ} (φ : Formula k) :
    ∀ u z, Matches u z → |φ.gridEval T z - bit (φ.eval u)| ≤ ε := by
  induction φ with
  | atom a => exact T.atom_error a
  | neg φ ih => exact fun u z h => negate_error (ih u z h)
  | conj φ ψ ih jh =>
    exact fun u z h => andGate_error _ T.eps_small T.delta_small (ih u z h) (jh u z h)
  | disj φ ψ ih jh =>
    exact fun u z h => orGate_error _ T.eps_small T.delta_small (ih u z h) (jh u z h)
  | ex φ ih =>
    intro u z h
    exact quantify_error T (Nat.zero_le U) _ _ (fun _ => φ.gridEval_unit T _)
      (fun i b => ih _ _ (matches_cons h i b))
  | maj φ ih =>
    intro u z h
    exact quantify_error T (Nat.div_le_self U 2) _ _ (fun _ => φ.gridEval_unit T _)
      (fun i b => ih _ _ (matches_cons h i b))

end Model
end
end DiophantineNP.Counting
