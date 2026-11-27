import DiophantineNP.HABTranslation
import Init.Data.BitVec.Bitblast

/-! # Numeric index arithmetic in the source vocabulary

The addition relation on finite indices has a fixed first-order definition
using order and BIT. A candidate output supplies the carry at each position
as the parity of its bit and both input bits. Checking the initial carry and
each adjacent pair of carries suffices. -/
namespace DiophantineNP.HAB
open Counting WidthFormula FiniteArithmeticGap

private def imp {k} (p q : Form k) := Form.disj (.neg p) q
private def same {k} (p q : Form k) := Form.conj (imp p q) (imp q p)
private def bxor {k} (p q : Form k) := Form.disj (.conj p (.neg q)) (.conj (.neg p) q)

private theorem imp_spec {k U} (p q : Form k) (A : Matrix U) (e : Fin k→Fin U) :
    (imp p q).Holds A e ↔ (p.Holds A e → q.Holds A e) := by
  classical
  change (¬_ ∨ _) ↔ _
  tauto

private theorem same_spec {k U} (p q : Form k) (A : Matrix U) (e : Fin k→Fin U) :
    (same p q).Holds A e ↔ (p.Holds A e ↔ q.Holds A e) := by
  change ((_ ∧ _) ↔ _)
  rw [imp_spec,imp_spec]; tauto

private theorem bxor_spec {k U} (p q : Form k) (A : Matrix U) (e : Fin k→Fin U) (a b : Bool)
    (ha : p.Holds A e ↔ a=true) (hb : q.Holds A e ↔ b=true) :
    (bxor p q).Holds A e ↔ (a^^b)=true := by
  change ((_ ∧ ¬_) ∨ (¬_ ∧ _)) ↔ _
  rw [ha,hb]; cases a <;> cases b <;> decide

private def zeroF {k} (j : Fin k) : Form k := .neg (.ex (.lt 0 j.succ))

private theorem zero_spec {k U} (j : Fin k) (A : Matrix U) (e : Fin k→Fin U) :
    (zeroF j).Holds A e ↔ (e j).val=0 := by
  simp only [zeroF,Form.Holds,Fin.cases_zero,Fin.cases_succ,Fin.lt_def,not_exists]
  constructor
  · intro h; by_contra hz; exact h ⟨0,by have := (e j).isLt; omega⟩ (by dsimp;omega)
  · intro h i; omega

private def nextF {k} (i j : Fin k) : Form k :=
  .conj (.lt i j) (.neg (.ex (.conj (.lt i.succ 0) (.lt 0 j.succ))))

private theorem next_spec {k U} (i j : Fin k) (A : Matrix U) (e : Fin k→Fin U) :
    (nextF i j).Holds A e ↔ (e i).val+1=(e j).val := by
  simp only [nextF,Form.Holds,Fin.cases_zero,Fin.cases_succ,Fin.lt_def,not_exists]
  constructor
  · rintro ⟨hi,h⟩; by_contra hn
    exact h ⟨(e i).val+1,by have := (e j).isLt;omega⟩ ⟨by dsimp;omega,by dsimp;omega⟩
  · intro h; exact ⟨by omega,fun t ht => by omega⟩

private def flag {k} (x y z i : Fin k) : Form k := bxor (.BIT i x) (bxor (.BIT i y) (.BIT i z))

private def flagBit (x y z i : ℕ) := x.testBit i ^^ (y.testBit i ^^ z.testBit i)

private theorem flag_spec {k U} (x y z i : Fin k) (A : Matrix U) (e : Fin k→Fin U) :
    (flag x y z i).Holds A e ↔ flagBit (e x).val (e y).val (e z).val (e i).val = true :=
  bxor_spec _ _ _ _ _ _ Iff.rfl (bxor_spec _ _ _ _ _ _ Iff.rfl Iff.rfl)

private def carryOut {k} (x y z i : Fin k) : Form k :=
  .disj (.conj (.BIT i x) (.BIT i y)) (.conj (flag x y z i) (.disj (.BIT i x) (.BIT i y)))

private theorem carryOut_spec {k U} (x y z i : Fin k) (A : Matrix U) (e : Fin k→Fin U) :
    (carryOut x y z i).Holds A e ↔
      Bool.atLeastTwo ((e x).val.testBit (e i).val) ((e y).val.testBit (e i).val)
        (flagBit (e x).val (e y).val (e z).val (e i).val) = true := by
  change ((_ ∧ _) ∨ (_ ∧ (_ ∨ _))) ↔ _
  rw [flag_spec]
  change (((e x).val.testBit (e i).val=true ∧ (e y).val.testBit (e i).val=true) ∨
    (_=true ∧ ((e x).val.testBit (e i).val=true ∨ (e y).val.testBit (e i).val=true))) ↔ _
  cases (e x).val.testBit (e i).val <;> cases (e y).val.testBit (e i).val <;>
    cases flagBit (e x).val (e y).val (e z).val (e i).val <;> decide

/-- Finite, non-wrapping index addition in pure order and BIT. -/
def indexAdd {k} (x y z : Fin k) : Form k :=
  .conj
    (.all (imp (zeroF 0) (.neg (flag x.succ y.succ z.succ 0))))
    (.all (.all (imp (nextF (0 : Fin (k+1)).succ 0)
      (same (flag x.succ.succ y.succ.succ z.succ.succ 0)
        (carryOut x.succ.succ y.succ.succ z.succ.succ (0 : Fin (k+1)).succ)))))

private theorem double_lt (n : ℕ) : 2*n<2^(n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    have h : n+1<2^(n+1) := Nat.lt_two_pow_self
    omega

private theorem flag_iff_add {U x y z : ℕ} (hx : x<U) (hy : y<U) (hz : z<U) :
    (flagBit x y z 0=false ∧ ∀ i, i+1<U →
      flagBit x y z (i+1)=Bool.atLeastTwo (x.testBit i) (y.testBit i) (flagBit x y z i)) ↔
    x+y=z := by
  let X := BitVec.ofNat U x
  let Y := BitVec.ofNat U y
  have bit (a : ℕ) {i : ℕ} (hi : i<U) : (BitVec.ofNat U a).getLsbD i=a.testBit i := by
    simp only [BitVec.getLsbD_ofNat,decide_eq_true hi,Bool.true_and]
  have sumBit {i : ℕ} (hi : i<U) :
      (x+y).testBit i = (x.testBit i ^^ (y.testBit i ^^ BitVec.carry i X Y false)) := by
    simpa only [X,Y,←BitVec.ofNat_add,bit _ hi] using BitVec.getLsbD_add hi X Y
  have cancel (a b c : Bool) : (a ^^ (b ^^ (a ^^ (b ^^ c)))) = c := by
    cases a <;> cases b <;> cases c <;> decide
  have carryStep {i : ℕ} (hi : i<U) : BitVec.carry (i+1) X Y false =
      Bool.atLeastTwo (x.testBit i) (y.testBit i) (BitVec.carry i X Y false) := by
    rw [BitVec.carry_succ]; simp only [X,Y,bit _ hi]
  constructor
  · rintro ⟨base,step⟩
    have carries : ∀ i<U, flagBit x y z i=BitVec.carry i X Y false := by
      intro i; induction i with
      | zero => intro _; simpa using base
      | succ i ih => intro hi; rw [step i hi,carryStep (by omega),ih (by omega)]
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i<U
    · rw [sumBit hi,←carries i hi]; exact cancel _ _ _
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : U≠0)
      have bound := double_lt m
      have bigger := Nat.pow_le_pow_right (by decide : 0<2) (show m + 1 ≤ i by omega)
      rw [Nat.testBit_lt_two_pow (by omega : x+y<2^i),Nat.testBit_lt_two_pow (by omega : z<2^i)]
  · rintro rfl
    have carries {i : ℕ} (hi : i<U) : flagBit x y (x+y) i=BitVec.carry i X Y false := by
      rw [flagBit,sumBit hi,cancel]
    refine ⟨by rw [carries (by omega),BitVec.carry_zero],?_⟩
    intro i hi; rw [carries hi,carryStep (by omega),carries (by omega)]

theorem indexAdd_correct {k U} (x y z : Fin k) (A : Matrix U) (e : Fin k→Fin U) :
    (indexAdd x y z).Holds A e ↔ (e x).val + (e y).val = (e z).val := by
  rw [←flag_iff_add (e x).isLt (e y).isLt (e z).isLt]
  change ((∀ i : Fin U, _) ∧ (∀ i j : Fin U, _)) ↔ _
  simp only [imp_spec,zero_spec,Form.Holds,Fin.cases_zero,Fin.cases_succ,same_spec,next_spec,
    carryOut_spec,flag_spec,←Bool.eq_iff_iff]
  constructor
  · rintro ⟨hb,hn⟩
    refine ⟨by simpa using hb ⟨0, by have := (e x).isLt; omega⟩ rfl,?_⟩
    intro i hi
    exact hn ⟨i,by omega⟩ ⟨i+1,hi⟩ rfl
  · rintro ⟨hb,hn⟩
    refine ⟨fun i hi => by simpa [hi] using hb,fun i j h => ?_⟩
    simpa [←h] using hn i.val (by rw [h];exact j.isLt)


/-- Fixed numeric constants in the ordered universe. -/
def indexNat : (n : ℕ) → {k : ℕ} → Fin k → Form k
  | 0,_,j => zeroF j
  | n+1,_,j => .ex (.conj (indexNat n 0) (nextF 0 j.succ))

theorem indexNat_correct (n : ℕ) {k U} (j : Fin k) (A : Matrix U) (e : Fin k→Fin U) :
    (indexNat n j).Holds A e ↔ (e j).val=n := by
  induction n generalizing k with
  | zero => exact zero_spec _ _ _
  | succ n ih =>
    simp only [indexNat,Form.Holds,ih,next_spec,Fin.cases_zero,Fin.cases_succ]
    constructor
    · rintro ⟨i,hn,he⟩; omega
    · intro h; exact ⟨⟨n,by have := (e j).isLt; omega⟩,rfl,h.symm⟩

private def shiftMap {k l} (σ : Fin k→Fin l) : Fin (k+1)→Fin (l+1) :=
  Fin.cases 0 (Fin.succ ∘ σ)

private theorem shiftMap_env {k l U} (σ : Fin k→Fin l) (e : Fin l→Fin U) (v : Fin U) :
    Fin.cases v e ∘ shiftMap σ = Fin.cases v (e ∘ σ) := by
  funext i; refine Fin.cases ?_ (fun i=>?_) i <;> rfl

/-- Capture-avoiding renaming, including under the majority quantifier. -/
def Form.rename : {k : ℕ} → Form k → {l : ℕ} → (Fin k→Fin l) → Form l
  | _,.eq i j,_,σ => .eq (σ i) (σ j)
  | _,.lt i j,_,σ => .lt (σ i) (σ j)
  | _,.BIT i j,_,σ => .BIT (σ i) (σ j)
  | _,.input i j,_,σ => .input (σ i) (σ j)
  | _,.neg p,_,σ => (p.rename σ).neg
  | _,.conj p q,_,σ => .conj (p.rename σ) (q.rename σ)
  | _,.disj p q,_,σ => .disj (p.rename σ) (q.rename σ)
  | _,.ex p,_,σ => .ex (p.rename (shiftMap σ))
  | _,.all p,_,σ => .all (p.rename (shiftMap σ))
  | _,.many p,_,σ => .many (p.rename (shiftMap σ))

theorem Form.rename_correct {k l U} (p : Form k) (σ : Fin k→Fin l) (A : Matrix U) (e : Fin l→Fin U) :
    (p.rename σ).Holds A e ↔ p.Holds A (e ∘ σ) := by
  induction p generalizing l with
  | eq i j | lt i j | BIT i j | input i j => rfl
  | neg p ih => simp [Form.rename,Form.Holds,ih]
  | conj p q ih jh | disj p q ih jh => simp [Form.rename,Form.Holds,ih,jh]
  | ex p ih | all p ih => simp only [Form.rename,Form.Holds,ih,shiftMap_env]
  | many p ih =>
    classical
    simp only [Form.rename,Form.Holds]
    simp_rw [ih,shiftMap_env]

/-- One source formula for the graph of numerical multiplication on finite indices.
The relation includes only products which themselves belong to the universe. -/
structure IndexMultiplication where
  formula : Form 3
  correct {U : ℕ} (A : Matrix U) (e : Fin 3→Fin U) :
    formula.Holds A e ↔ (e 0).val*(e 1).val=(e 2).val

/-- Interpret an arithmetic template in the original order/BIT source language. -/
def source (mul : IndexMultiplication) : {k : ℕ} → Template k → Form k
  | _,.atom (.eqv i j) => .eq i j
  | _,.atom (.leq i j) => .neg (.lt j i)
  | _,.atom (.add i j l) => indexAdd i j l
  | _,.atom (.mul i j l) => mul.formula.rename ![i,j,l]
  | _,.bit x j => .BIT j x
  | _,.entry x y => .input x y
  | _,.neg p => .neg (source mul p)
  | _,.conj p q => .conj (source mul p) (source mul q)
  | _,.disj p q => .disj (source mul p) (source mul q)
  | _,.ex p => .ex (source mul p)
  | _,.maj p => .many (source mul p)

theorem source_correct (mul : IndexMultiplication) {k U} (p : Template k) (A : Matrix U) (e : Fin k→Fin U) :
    (source mul p).Holds A e ↔ p.eval A e=true := by
  classical
  induction p with
  | atom a =>
    cases a with
    | eqv i j => simp [source,Form.Holds,Template.eval,Atom.eval,Fin.ext_iff]
    | leq i j =>
      change (¬ (e j).val < (e i).val) ↔ decide ((e i).val≤(e j).val)=true
      simp
    | add i j l => simp [source,indexAdd_correct,Template.eval,Atom.eval]
    | mul i j l => simp [source,Form.rename_correct,mul.correct,Template.eval,Atom.eval]
  | bit x j | entry x j => exact Iff.rfl
  | neg p ih => simp [source,Form.Holds,Template.eval,ih]
  | conj p q ih jh | disj p q ih jh => simp [source,Form.Holds,Template.eval,ih,jh]
  | ex p ih => simp only [source,Form.Holds,Tex_true,ih]
  | maj p ih =>
    simp only [source,Form.Holds,Template.eval,decide_eq_true_eq,count]
    simp_rw [ih]; omega

end DiophantineNP.HAB
