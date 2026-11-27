import DiophantineNP.SmallSumTemplate
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Data.Nat.Bits
import Mathlib.Algebra.BigOperators.Fin

/-! # From the Hesse–Allender–Barrington FOM language to the width formula

Hesse, Allender and Barrington, *Uniform constant-depth threshold circuits for
division and iterated multiplication*, JCSS 65 (2002), 695–716,
https://doi.org/10.1016/S0022-0000(02)00025-9, §§2 and 2.3, Corollary 6.3.

The source semantics uses order, `BIT(position, number)`, a binary input
relation and strict unary majority. The product bit index has two digits in
base `U`. The interface `ImultInFOM` below states the source theorem without
assuming any target-language template; its proof from HAB's algorithm remains
external. The translation, the reconstruction of the input rows, the high
index digit zero, and both degenerate universe sizes are verified here. -/
namespace DiophantineNP.HAB
open Counting WidthFormula FiniteArithmeticGap
open scoped Classical

abbrev Matrix (U : ℕ) := Fin U → Fin U → Bool

/-- Row bits are given in increasing order of significance. -/
def rowWord : {U : ℕ} → (Fin U → Bool) → ℕ
  | 0, _ => 0
  | _+1, a => Nat.bit (a 0) (rowWord (fun i => a i.succ))

theorem rowWord_bit {U : ℕ} (a : Fin U → Bool) (j : Fin U) : (rowWord a).testBit j.val = a j := by
  induction U with
  | zero => exact j.elim0
  | succ U ih =>
    refine Fin.cases (by simp [rowWord]) (fun i => ?_) j
    simpa only [rowWord,Fin.val_succ,Nat.testBit_bit_succ] using ih (fun k => a k.succ) i

theorem rowWord_bound {U : ℕ} (a : Fin U → Bool) : rowWord a < 2^U := by
  induction U with
  | zero => simp [rowWord]
  | succ U ih =>
    have h := ih (fun i => a i.succ)
    rw [rowWord,pow_succ]
    cases e : a 0 <;> simp only [Nat.bit,cond_true,cond_false] <;> omega

theorem rowWord_natural {U : ℕ} {x : ℕ} (h : x<2^U) : rowWord (fun i : Fin U => x.testBit i.val) = x := by
  induction U generalizing x with
  | zero => change 0=x; simpa [eq_comm] using h
  | succ U ih =>
    rw [rowWord]
    simp only [Fin.val_succ,Nat.testBit_succ]
    rw [ih (x:=x/2) (by rw [pow_succ] at h; omega)]
    simpa [Nat.shiftRight_one] using Nat.bit_testBit_zero_shiftRight_one x

/-- The order and BIT vocabulary from §2.3. Subformulas with a bound variable
place that variable at de Bruijn index zero. -/
inductive Form : ℕ → Type where
  | eq {k} (x y : Fin k) : Form k
  | lt {k} (x y : Fin k) : Form k
  | BIT {k} (position number : Fin k) : Form k
  | input {k} (row col : Fin k) : Form k
  | neg {k} (φ : Form k) : Form k
  | conj {k} (φ ψ : Form k) : Form k
  | disj {k} (φ ψ : Form k) : Form k
  | ex {k} (φ : Form (k+1)) : Form k
  | all {k} (φ : Form (k+1)) : Form k
  | many {k} (φ : Form (k+1)) : Form k

noncomputable def Form.Holds {U : ℕ} (A : Matrix U) : {k : ℕ} → Form k → (Fin k → Fin U) → Prop
  | _,.eq i j,e => e i = e j
  | _,.lt i j,e => e i < e j
  | _,.BIT i j,e => (e j).val.testBit (e i).val = true
  | _,.input r c,e => A (e r) (e c) = true
  | _,.neg p,e => ¬p.Holds A e
  | _,.conj p q,e => p.Holds A e ∧ q.Holds A e
  | _,.disj p q,e => p.Holds A e ∨ q.Holds A e
  | _,.ex p,e => ∃ i : Fin U, p.Holds A (Fin.cases i e)
  | _,.all p,e => ∀ i : Fin U, p.Holds A (Fin.cases i e)
  | _,.many p,e => U < 2*(Finset.univ.filter (fun i : Fin U => p.Holds A (Fin.cases i e))).card

/-- Source multiplication is absent from this translation: the project already
implements BIT on ordinary (truncated-domain) addition and multiplication. -/
def Form.translate : {k : ℕ} → Form k → Template k
  | _,.eq x y => .atom (.eqv x y)
  | _,.lt x y => .neg (.atom (.leq y x))
  | _,.BIT i x => .bit x i
  | _,.input r c => .entry r c
  | _,.neg p => .neg p.translate
  | _,.conj p q => .conj p.translate q.translate
  | _,.disj p q => .disj p.translate q.translate
  | _,.ex p => .ex p.translate
  | _,.all p => .neg (.ex (.neg p.translate))
  | _,.many p => .maj p.translate

private theorem neg_true {k U : ℕ} (p : Template k) (A : Matrix U) (e : Fin k → Fin U) :
    p.neg.eval A e=true ↔ ¬p.eval A e=true := by cases h : p.eval A e <;> simp [Template.eval,h]

theorem Form.translate_correct {k U : ℕ} (p : Form k) (A : Matrix U) (e : Fin k → Fin U) :
    p.translate.eval A e=true ↔ p.Holds A e := by
  classical
  induction p with
  | eq i j | lt i j | BIT i j | input i j => simp [Form.translate,Form.Holds,Template.eval,Atom.eval]
  | neg p ih => simpa [Form.translate,Form.Holds,Template.eval,Bool.not_eq_true] using not_congr (ih e)
  | conj p q ih jh => simp [Form.translate,Form.Holds,Template.eval,ih,jh]
  | disj p q ih jh => simp [Form.translate,Form.Holds,Template.eval,ih,jh]
  | ex p ih => simp only [Form.translate,Form.Holds,Tex_true,ih]
  | all p ih =>
    simp only [Form.translate,neg_true,Tex_true,ih,not_exists,not_not,Form.Holds]
  | many p ih =>
    simp only [Form.translate,Form.Holds,Template.eval,count,decide_eq_true_eq]
    simp_rw [ih]; omega

/-- A fixed source formula over a raw binary matrix, with high and low query
coordinates. The exceptional sizes 0 and 1 are handled by the translation. -/
def ImultInFOM : Prop := ∃ φ : Form 2, ∀ {U : ℕ}, 2≤U → ∀ (A : Matrix U) (hi lo : Fin U),
  φ.Holds A (pairEnv hi lo) ↔ (∏ r : Fin U, rowWord (A r)).testBit (hi.val*U+lo.val) = true

private def tiny : Template 1 := .neg (.ex (fromFormula (isNat 1 (0 : Fin 2))))

private theorem tiny_correct {U : ℕ} (A : Matrix U) (e : Fin 1 → Fin U) : tiny.eval A e = true ↔ U≤1 := by
  rw [tiny,neg_true,Tex_true]
  simp only [fromFormula_eval,isNat_spec,Fin.cases_zero,not_exists]
  constructor
  · intro h; by_contra! hU; exact h ⟨1,hU⟩ rfl
  · intro h i; have := i.isLt; omega

/-- On a singleton input the answer at the only possible query is its only
input bit. Otherwise bind the high digit to zero and retain the low digit. -/
def lowQuery (φ : Form 2) : Template 1 :=
  .disj (.conj tiny (.entry 0 0))
    (.conj (.neg tiny) (.ex (.conj (fromFormula (isNat 0 (0 : Fin 2))) φ.translate)))

private theorem prod_natural (U : ℕ) (f : ℕ → ℕ) : (∏ r : Fin U, f r.val)=productPrefix f U := by
  induction U with
  | zero => simp [productPrefix]
  | succ U ih => rw [Fin.prod_univ_castSucc,product_succ,← ih]; rfl

/-- This is the translation of Corollary 6.3 into the manuscript's precise
one-variable low-bit interface. Each use of the source formula is uniform in U. -/
noncomputable def productTemplate_of_imult (source : ImultInFOM) : ProductTemplate where
  product := lowQuery source.choose
  product_correct := by
    intro U f fits j
    let A : Matrix U := fun r c => (f r.val).testBit c.val
    let e : Fin 1 → Fin U := fun _ => j
    change (lowQuery source.choose).eval A e = _
    by_cases h : U≤1
    · have hj := j.isLt
      obtain rfl : U=1 := by omega
      apply Bool.eq_iff_iff.mpr
      simp only [lowQuery,Tdisj_true,Tconj_true,neg_true,tiny_correct,h,true_and,not_true_eq_false,false_and,or_false,Tentry_eval]
      simp [e,A,productPrefix]
    · have hU : 2≤U := by omega
      let z : Fin U := ⟨0,by omega⟩
      have hrow (r : Fin U) : rowWord (A r) = f r.val := rowWord_natural (fits _ r.isLt)
      apply Bool.eq_iff_iff.mpr
      simp only [lowQuery,Tdisj_true,Tconj_true,neg_true,tiny_correct,h,false_and,not_false_eq_true,true_and,false_or,Tex_true,fromFormula_eval,isNat_spec,Fin.cases_zero,Form.translate_correct]
      have spec (i : Fin U) : Fin.cases i e = pairEnv i j := rfl
      simp_rw [spec,source.choose_spec hU A,hrow,prod_natural]
      exact ⟨fun ⟨i,hi,hh⟩ => by simpa [hi] using hh,fun hh => ⟨z,rfl,by simpa [z] using hh⟩⟩

end DiophantineNP.HAB
