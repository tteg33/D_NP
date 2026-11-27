import DiophantineNP.FiniteArithmeticGap
import DiophantineNP.SumProductDigits
import Mathlib.Order.Interval.Finset.Fin

/-! A low-bit product formula also computes all the digits of a sum whose
total fits in half the input width.  This is the only kind of sum needed
for the width-dependent CRT readout. -/
namespace DiophantineNP.FiniteArithmeticGap
open Counting PrimeFormula WidthFormula

structure ProductTemplate where
  product : Template 1
  product_correct {U : ℕ} (f : ℕ → ℕ) (fits : ∀ t<U, f t<2^U) (j : Fin U) :
    product.eval (fun r c => (f r.val).testBit c.val) (fun _ => j) = (productPrefix f U).testBit j.val

def fromFormula {k : ℕ} : Formula k → Template k
  | .atom v => .atom v
  | .neg v => .neg (fromFormula v)
  | .conj v w => .conj (fromFormula v) (fromFormula w)
  | .disj v w => .disj (fromFormula v) (fromFormula w)
  | .ex v => .ex (fromFormula v)
  | .maj v => .maj (fromFormula v)

@[simp] theorem fromFormula_eval {k U : ℕ} (v : Formula k) (e : Fin U → Fin U → Bool)
    (env : Fin k → Fin U) : (fromFormula v).eval e env = v.eval env := by
  induction v with
  | atom => rfl
  | neg v ih => simp [fromFormula,Template.eval,Formula.eval, ih]
  | conj v w ih jh => simp [fromFormula,Template.eval,Formula.eval,ih,jh]
  | disj v w ih jh => simp [fromFormula,Template.eval,Formula.eval,ih,jh]
  | ex v ih => simp [fromFormula,Template.eval,Formula.eval,ih]
  | maj v ih => simp [fromFormula,Template.eval,Formula.eval,ih]

theorem Tex_true {k U : ℕ} (v : Template (k+1)) (e : Fin U → Fin U → Bool) (env : Fin k → Fin U) :
    (Template.ex v).eval e env = true ↔ ∃z : Fin U, v.eval e (Fin.cases z env) = true := by
  simp [Template.eval,count,Finset.card_pos,Finset.Nonempty]

theorem Tconj_true {k U : ℕ} (v w : Template k) (e : Fin U → Fin U → Bool) (env : Fin k → Fin U) :
    (Template.conj v w).eval e env = true ↔ v.eval e env = true ∧ w.eval e env = true := by simp [Template.eval]

theorem Tdisj_true {k U : ℕ} (v w : Template k) (e : Fin U → Fin U → Bool) (env : Fin k → Fin U) :
    (Template.disj v w).eval e env = true ↔ v.eval e env = true ∨ w.eval e env = true := by simp [Template.eval]

@[simp] theorem Tentry_eval {k U : ℕ} (r c : Fin k) (e : Fin U → Fin U → Bool) (env : Fin k → Fin U) :
    (Template.entry r c).eval e env = e (env r) (env c) := rfl

private def big {k : ℕ} (x : Fin k) : Formula k := .maj (.atom (.leq 0 x.succ))

private theorem big_true {k U : ℕ} (x : Fin k) (env : Fin k → Fin U) :
    (big x).eval env = true ↔ U/2 ≤ (env x).val := by
  change decide (U/2 < (Finset.univ.filter (fun z : Fin U => decide (z.val ≤ (env x).val) = true)).card) = true ↔ _
  have hf : Finset.univ.filter (fun z : Fin U => decide (z.val ≤ (env x).val) = true) = Finset.Iic (env x) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_Iic]
    rfl
  rw [hf,Fin.card_Iic,decide_eq_true_eq]
  omega

/-- The least element whose closed initial segment is a strict majority. -/
def half {k : ℕ} (x : Fin k) : Formula k :=
  andF (big x) (notF (.ex (andF (big 0) (ltF 0 x.succ))))

theorem half_true {k U : ℕ} (x : Fin k) (env : Fin k → Fin U) :
    (half x).eval env = true ↔ (env x).val = U/2 := by
  simp only [half,andF_spec,notF_spec,exists_true,big_true,ltF_true,Fin.cases_zero,Fin.cases_succ]
  constructor
  · rintro ⟨hb,hn⟩
    by_contra h
    exact hn ⟨⟨U/2,by have := (env x).isLt; omega⟩,le_rfl,by dsimp; omega⟩
  · rintro h
    exact ⟨h.ge,fun ⟨v,hv,hl⟩ => by omega⟩

private def liftMap {a b : ℕ} (σ : Fin a → Fin b) : Fin (a+1) → Fin (b+1) :=
  Fin.cases 0 (fun i => (σ i).succ)

private theorem liftMap_env {a b U : ℕ} (σ : Fin a → Fin b) (u : Fin U) (env : Fin b → Fin U) :
    Fin.cases u env ∘ liftMap σ = Fin.cases u (env ∘ σ) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

private def mapAtom {k l : ℕ} (σ : Fin k → Fin l) : Atom k → Atom l
  | .eqv i j => .eqv (σ i) (σ j)
  | .leq i j => .leq (σ i) (σ j)
  | .mul i j t => .mul (σ i) (σ j) (σ t)
  | .add i j t => .add (σ i) (σ j) (σ t)

private theorem mapAtom_eval {k l U : ℕ} (a : Atom k) (σ : Fin k → Fin l) (env : Fin l → Fin U) :
    (mapAtom σ a).eval env = a.eval (env ∘ σ) := by cases a <;> rfl

/-- Capture-avoiding input substitution with an independent map of variables. -/
def rewriteMatrix (input : {k : ℕ} → Fin k → Fin k → Template k) {a : ℕ} (φ : Template a) :
    {k : ℕ} → (Fin a → Fin k) → Template k :=
  match φ with
  | .atom v => fun σ => .atom (mapAtom σ v)
  | .entry r c => fun σ => input (σ r) (σ c)
  | .bit x j => fun σ => .bit (σ x) (σ j)
  | .neg v => fun σ => .neg (rewriteMatrix @input v σ)
  | .conj v w => fun σ => .conj (rewriteMatrix @input v σ) (rewriteMatrix @input w σ)
  | .disj v w => fun σ => .disj (rewriteMatrix @input v σ) (rewriteMatrix @input w σ)
  | .ex v => fun σ => .ex (rewriteMatrix @input v (liftMap σ))
  | .maj v => fun σ => .maj (rewriteMatrix @input v (liftMap σ))

theorem rewriteMatrix_eval (input : {k : ℕ} → Fin k → Fin k → Template k) {a k U : ℕ}
    (e g : Fin U → Fin U → Bool)
    (hs : ∀ {m : ℕ} (r c : Fin m) (env : Fin m → Fin U), (input r c).eval e env = g (env r) (env c))
    (φ : Template a) (σ : Fin a → Fin k) (env : Fin k → Fin U) :
    (rewriteMatrix @input φ σ).eval e env = φ.eval g (env ∘ σ) := by
  induction φ generalizing k with
  | atom v => exact mapAtom_eval _ _ _
  | entry r c => exact hs _ _ _
  | bit x j => rfl
  | neg v ih => simp only [rewriteMatrix,Template.eval,ih]
  | conj v w ih jh => simp only [rewriteMatrix,Template.eval,ih,jh]
  | disj v w ih jh => simp only [rewriteMatrix,Template.eval,ih,jh]
  | ex v ih => simp only [rewriteMatrix,Template.eval,ih,liftMap_env]
  | maj v ih => simp only [rewriteMatrix,Template.eval,ih,liftMap_env]

private def shiftedEntry {k : ℕ} (r c : Fin k) : Template k :=
  .disj (fromFormula (isNat 0 c)) (.ex (.ex (.conj (fromFormula (half (0 : Fin (k+1)).succ))
    (.conj (fromFormula (addF (0 : Fin (k+1)).succ 0 (up2 c))) (.entry (up2 r) 0)))))

private theorem shiftedEntry_eval {U k : ℕ} (hU : 2≤U) (f : ℕ → ℕ)
    (r c : Fin k) (env : Fin k → Fin U) :
    (shiftedEntry r c).eval (fun r c => (f r.val).testBit c.val) env =
      (1+2^(U/2)*f (env r).val).testBit (env c).val := by
  apply Bool.eq_iff_iff.mpr
  simp only [shiftedEntry,Tentry_eval, Tdisj_true, fromFormula_eval, isNat_spec,Tex_true,
    Tconj_true,half_true,addF_spec,Fin.cases_zero,Fin.cases_succ]
  rw [Nat.add_comm 1, Nat.testBit_two_pow_mul_add _ (show 1<2^(U/2) from Nat.one_lt_two_pow (by omega))]
  by_cases hl : (env c).val < U/2
  · rw [if_pos hl]
    change _ ↔ ((2^0 : ℕ).testBit (env c).val = true)
    rw [Nat.testBit_two_pow, decide_eq_true_eq]
    constructor
    · rintro (hc|⟨v,t,hv,ht,_⟩) <;> omega
    · intro h
      left
      omega
  · rw [if_neg hl]
    constructor
    · rintro (hc|⟨v,t,hv,ht,h⟩)
      · omega
      · rwa [show (env c).val-U/2=t.val by omega]
    · intro h
      right
      exact ⟨⟨U/2,by omega⟩,⟨(env c).val-U/2,by have := (env c).isLt; omega⟩,rfl,by dsimp; omega,h⟩

def ProductTemplate.smallSum (P : ProductTemplate) : Template 1 :=
  .ex (.ex (.conj (fromFormula (half 1)) (.conj (fromFormula (ltF 2 1))
    (.conj (fromFormula (addF 1 2 0)) (rewriteMatrix @shiftedEntry P.product (fun _ => 0))))))

private theorem term_le_total (f : ℕ → ℕ) {U t : ℕ} (ht : t<U) : f t ≤ Readout.prefixSum f U := by
  induction U with
  | zero => omega
  | succ U ih =>
    rw [Readout.prefixSum]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with h|h
    · exact (ih h).trans (by omega)
    · rw [h]; omega

private theorem encoded_fits {U : ℕ} (hU : 2 ≤ U) (f : ℕ → ℕ) (hfit : Readout.prefixSum f U<2^(U/2))
    (t : ℕ) (ht : t<U) : 1+2^(U/2)*f t < 2^U := by
  have h := (term_le_total f ht).trans_lt hfit
  have h2 : 1 < (2:ℕ)^(U/2) := Nat.one_lt_two_pow (by omega)
  have he := Nat.mul_le_mul_left (2^(U/2)) (show f t+1 ≤2^(U/2) by omega)
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show U/2+U/2 ≤ U by omega)
  rw [pow_add] at hpow
  nlinarith

/-- A single fixed product template supplies all digits of every sum whose
total fits in the lower half of the universe's bit positions. -/
theorem ProductTemplate.smallSum_correct (A : ProductTemplate) {U : ℕ} (f : ℕ → ℕ) (hU : 2 ≤ U)
    (hfit : Readout.prefixSum f U < 2^(U/2)) (j : Fin U) :
    A.smallSum.eval (fun r c => (f r.val).testBit c.val) (fun _ => j) =
      (Readout.prefixSum f U).testBit j.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [ProductTemplate.smallSum,Tex_true,Tconj_true,fromFormula_eval,half_true,ltF_true,addF_spec]
  change (∃ s b : Fin U, s.val = U/2 ∧ j.val < s.val ∧ s.val+j.val=b.val ∧
    (rewriteMatrix @shiftedEntry A.product (fun _ => (0:Fin 3))).eval _
      (Fin.cases b (Fin.cases s (fun _ : Fin 1 => j))) = true) ↔ _
  have productBit (b s : Fin U) :
      (rewriteMatrix @shiftedEntry A.product (fun _ => (0:Fin 3))).eval
        (fun r c => (f r.val).testBit c.val)
        (Fin.cases b (Fin.cases s (fun _ : Fin 1 => j))) =
      (productPrefix (fun i => 1+2^(U/2)*f i) U).testBit b.val := by
    rw [rewriteMatrix_eval @shiftedEntry _ (fun r c : Fin U => (1+2^(U/2)*f r.val).testBit c.val) (fun r c env => shiftedEntry_eval hU f r c env)]
    exact A.product_correct _ (encoded_fits hU f hfit) b
  simp_rw [productBit]
  constructor
  · rintro ⟨s,b,hs,hj,hb,h⟩
    rw [← hb,hs,SumProductDigits.product_sum_digit _ _ _ _ (by omega) (by omega)] at h
    exact h
  · intro h
    have hj : j.val < U/2 := by
      have := Nat.ge_two_pow_of_testBit h
      by_contra! hle
      have := Nat.pow_le_pow_right (by decide : 0<2) hle
      omega
    refine ⟨⟨U/2,by omega⟩,⟨U/2+j.val,by omega⟩,rfl,hj,rfl,?_⟩
    exact (SumProductDigits.product_sum_digit _ _ _ _ (by omega) hj).symm ▸ h

end DiophantineNP.FiniteArithmeticGap
