import DiophantineNP.HABGeometricDivision
import DiophantineNP.HABPowerReduction
import DiophantineNP.HABRemainderCheck
import DiophantineNP.HABShortLift
import DiophantineNP.HABShortWidth

/-! # Short modular products from an ordinary bit product of polylogarithmic length

The geometric-series quotient queries the product formula only on inputs
whose full numerical product has at most a quadratic number of bits in the
original bit length. This permits its use with a bounded-length product proof.
-/
namespace DiophantineNP.HABShortProducts
open Counting WidthFormula PrimeFormula FiniteArithmeticGap Finset HAB

/-- Uniform product-bit correctness on the indicated numerical range.
The total number of rows is the ambient universe size. -/
def BitsCorrect (N d : ℕ) (P : Template 1) : Prop := ∀ {U : ℕ}, N≤U →
  ∀ (f : ℕ→ℕ), (∀ i<U, f i<2^U) → productPrefix f U<2^(U.log2^d) → ∀ j : Fin U,
    P.eval (fun r c => (f r.val).testBit c.val) (fun _=>j) = (productPrefix f U).testBit j.val

private def mux {k} (cond yes no : Template k) : Template k :=
  .disj (.conj cond yes) (.conj (.neg cond) no)

private theorem mux_spec {k U} (cond yes no : Template k) (A : Matrix U) (e : Fin k→Fin U) :
    (mux cond yes no).eval A e=if cond.eval A e then yes.eval A e else no.eval A e := by
  cases h : cond.eval A e <;> simp [mux,Template.eval,h]

private def factors {k : ℕ} (len : Fin k) : Template (k+2) :=
  mux (fromFormula (ltF 1 len.succ.succ)) (.entry 1 0) (fromFormula (isNat 0 0))

private def table (len : ℕ) (f : ℕ→ℕ) (i : ℕ) := if i<len then f i else 1

private theorem factors_spec {k U} (len : Fin k) (A : Matrix U) (e : Fin k→Fin U) (f : ℕ→ℕ)
    (h : ∀ i j : Fin U, i.val<(e len).val → A i j=(f i.val).testBit j.val) (r c : Fin U) :
    (factors len).eval A (extend c r e) = (table (e len).val f r.val).testBit c.val := by
  rw [factors,mux_spec]
  by_cases hl : r.val<(e len).val
  · have hc : (fromFormula (ltF 1 len.succ.succ)).eval A (extend c r e)=true :=
      (fromFormula_eval .. ▸ ltF_true ..).mpr hl
    simp only [hc,if_true,table,if_pos hl,Tentry_eval]
    exact h r c hl
  · have hc : (fromFormula (ltF 1 len.succ.succ)).eval A (extend c r e)=false :=
      Bool.eq_false_iff.mpr (fun hh => hl ((fromFormula_eval .. ▸ ltF_true ..).mp hh))
    simp only [hc,if_neg Bool.false_ne_true,table,if_neg hl]
    apply Bool.eq_iff_iff.mpr
    simp only [fromFormula_eval,isNat_spec,Nat.testBit_one_eq_true_iff_self_eq_zero]
    rfl

private theorem total_eq {U len : ℕ} (h : len≤U) (f : ℕ→ℕ) :
    productPrefix (table len f) U = ∏ a∈range len,f a := by
  have hprefix (n : ℕ) : productPrefix (table len f) n=∏ a∈range n, table len f a := by
    induction n with
    | zero => simp [productPrefix]
    | succ n ih => rw [product_succ,ih,prod_range_succ]
  rw [hprefix,←prod_subset (s₁:=range len) (s₂:=range U) (f:=table len f) (range_mono h)
    (fun i _ hi => by simp [table,show ¬i<len from fun h => hi (mem_range.mpr h)])]
  exact prod_congr rfl fun i hi => if_pos (mem_range.mp hi)

private theorem product_fits {len p : ℕ} (f : ℕ→ℕ) (h : ∀ i<len, f i<p) :
    (∏ i∈range len,f i) < 2^((len+1)*(p.log2+1)+1) := by
  calc (∏ i∈range len,f i) ≤ ∏ _i∈range len, 2^(p.log2+1) :=
        prod_le_prod' (fun i hi => ((h i (mem_range.mp hi)).trans Nat.lt_log2_self).le)
    _ = 2^((p.log2+1)*len) := by simp [pow_mul]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by nlinarith)

private def value {k : ℕ} (P : Template 1) (len : Fin k) : Template (k+1) :=
  HABMatrix.bind (factors len) P Fin.succ (fun _ => 0)

private theorem value_spec {N d U k} (P : Template 1) (ok : BitsCorrect N d P) (large : N≤U)
    (len : Fin k) (A : Matrix U) (e : Fin k→Fin U) (f : ℕ→ℕ) (hU : 0<U)
    (fits : ∀ i<(e len).val,f i<2^U)
    (short : (∏ i∈range (e len).val,f i)<2^(U.log2^d))
    (h : ∀ i j : Fin U, i.val<(e len).val → A i j=(f i.val).testBit j.val) (j : Fin U) :
    (value P len).eval A (Fin.cases j e) = (∏ i∈range (e len).val,f i).testBit j.val := by
  let g := table (e len).val f
  have hf (i : ℕ) (_ : i<U) : g i<2^U := by
    dsimp [g,table]; split
    next h => exact fits i h
    next => exact Nat.one_lt_two_pow hU.ne'
  have eq := total_eq (e len).isLt.le f
  have spec := ok large g hf (eq ▸ short) j
  rw [value,HABMatrix.bind_spec]
  have mat : (fun r c => (factors len).eval A (extend c r (Fin.cases j e ∘ Fin.succ))) =
      fun r c : Fin U => (g r.val).testBit c.val :=
    funext fun r => funext fun c => factors_spec len A e f h r c
  rw [mat];simpa only [g,eq] using spec

private def atBit {k l : ℕ} (w : Template (k+1)) (j : Fin l) (env : Fin k→Fin l) : Template l :=
  rewriteMatrix (fun r c => .entry r c) w (Fin.cases j env)

private theorem atBit_spec {k l U : ℕ} (w : Template (k+1)) (j : Fin l) (env : Fin k→Fin l)
    (A : Matrix U) (e : Fin l→Fin U) :
    (atBit w j env).eval A e = w.eval A (Fin.cases (e j) (e ∘ env)) := by
  rw [atBit,rewriteMatrix_eval _ A A (by intros; rfl)]
  apply congrArg (w.eval A);funext i; refine Fin.cases rfl (fun _ => rfl) i

private def divideTable {k : ℕ} (x : Template (k+1)) (p : Fin k) : Template (k+2) :=
  mux (fromFormula (isNat 0 1)) (atBit x 0 (fun i => i.succ.succ)) (.bit p.succ.succ 0)

private noncomputable def quotient {k} (P : Template 1) (x : Template (k+1)) (p m : Fin k) : Template (k+1) :=
  HABMatrix.bind (divideTable x p) (HABGeometricDivision.divisionWith P) Fin.succ ![0,m.succ]

private theorem quotient_spec {k U X : ℕ} (P : Template 1) (x : Template (k+1)) (p m : Fin k)
    (A : Matrix U) (e : Fin k→Fin U)
    (px : X<2^((e m).val+1)) (pp : (e p).val<2^((e m).val+1))
    (pad : ((e m).val+1)^2+((e m).val+1)<U)
    (hx : ∀ j : Fin U, x.eval A (Fin.cases j e)=X.testBit j.val)
    (hP : HABGeometricDivision.ProductUpTo P U (2^((e m).val+1)^2))
    (j : Fin U) : (quotient P x p m).eval A (Fin.cases j e)=(X/(e p).val).testBit j.val := by
  let B : Matrix U := fun r c => (divideTable x p).eval A (extend c r e)
  have rc (r c : Fin U) : B r c=if r.val=0 then X.testBit c.val else (e p).val.testBit c.val := by
    dsimp only [B]
    rw [divideTable,mux_spec,atBit_spec]
    have cr : (fromFormula (isNat 0 (1 : Fin (k+2)))).eval A (extend c r e)=decide (r.val=0) := by
      apply Bool.eq_iff_iff.mpr; rw [fromFormula_eval,isNat_spec,decide_eq_true_eq];rfl
    rw [cr]
    change (if decide (r.val=0) then x.eval A (Fin.cases c e) else (e p).val.testBit c.val)=_
    simp [hx]
  have hDiv := HABGeometricDivision.divisionWith_correct (x:=X) (y:=(e p).val) P B (e m) j px pp pad
    (fun i => by rw [rc];rfl) (fun i => by rw [rc];rfl) hP
  rw [quotient,HABMatrix.bind_spec]
  have args : Fin.cases j e ∘ ![(0 : Fin (k+1)),m.succ] = ![j,e m] := by
    funext i;fin_cases i <;> rfl
  rw [args];exact hDiv

private noncomputable def check (P : Template 1) : Template 4 :=
  let x := value P (1 : Fin 4)
  HABRemainderCheck.formula x (quotient P x 2 0) 2 3

private noncomputable def modular (P : Template 1) : Template 3 :=
  .ex (.conj (HABShortWidth.formula 1 2 0) (check P))

private theorem modular_correct {U N : ℕ} (P : Template 1) (ok : BitsCorrect N 60 P)
    (large : max N (HABPolylogRange.threshold 60)≤U) (A : Matrix U) (len p b : Fin U)
    (f : ℕ→ℕ) (prime : p.val.Prime) (padding : (p.val+2)^30<U)
    (short : len.val≤(HABGroupPower.primeBound (p.val-1))^2+1) (values : ∀ i<len.val,f i<p.val)
    (bits : ∀ i j : Fin U, i.val<len.val → A i j=(f i.val).testBit j.val) :
    (modular P).eval A ![len,p,b]=true ↔ (∏ i∈range len.val,f i)%p.val=b.val := by
  let w := HABShortWidth.width len.val p.val
  let X := ∏ i∈range len.val,f i
  have hN : N≤U := (le_max_left ..).trans large
  obtain ⟨_,pad,sq,pp⟩ := HABShortWidth.bounds ((le_max_right ..).trans large) prime p.isLt short
  change (w+1)^2+(w+1)<U at pad
  change (w+1)^2<U.log2^60 at sq
  change p.val<2^(w+1) at pp
  have hw : w+1 ≤ (w+1)^2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
  have px : X<2^(w+1) := product_fits f values
  have cap : 2*p.val<U := by
    have hh : (p.val+2)^2≤(p.val+2)^30 := Nat.pow_le_pow_right (by omega) (by decide)
    nlinarith
  have hu := prime.two_le.trans p.isLt.le
  have hX : X+p.val<2^U := calc
    _ < 2^(w+1)+2^(w+1) := Nat.add_lt_add px pp
    _ = 2^(w+1+1) := (Nat.mul_two _).symm.trans (pow_succ 2 (w+1)).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have oracle : HABGeometricDivision.ProductUpTo P U (2^(w+1)^2) :=
    fun g fits bound j => ok hN g fits (bound.trans_lt (Nat.pow_lt_pow_right (by decide) sq)) j
  have ready (m : Fin U) (hm : m.val=w) :
      (check P).eval A (Fin.cases m ![len,p,b])=true ↔ X%p.val=b.val := by
    let e : Fin 4→Fin U := Fin.cases m ![len,p,b]
    let x := value P (1 : Fin 4)
    have reads (j : Fin U) : x.eval A (Fin.cases j e)=X.testBit j.val :=
      value_spec P ok hN 1 A e f (by omega)
        (fun i hi => (values i hi).trans (p.isLt.trans Nat.lt_two_pow_self))
        (px.trans_le (Nat.pow_le_pow_right (by decide) (by omega))) bits j
    have quotientReads (j : Fin U) :
        (quotient P x 2 0).eval A (Fin.cases j e)=(X/p.val).testBit j.val := by
      have eq : (e 0).val=w := hm
      exact quotient_spec P x 2 0 A e (eq ▸ px) (eq ▸ pp) (eq ▸ pad) reads (eq ▸ oracle) j
    exact HABRemainderCheck.formula_correct x _ 2 3 A e X hu prime.pos hX reads quotientReads
  have pick (m : Fin U) : (HABShortWidth.formula 1 2 0).eval A (Fin.cases m ![len,p,b])=true ↔ m.val=w :=
    HABShortWidth.formula_spec _ _ _ _ _ prime cap
  rw [modular,Tex_true]
  simp only [Tconj_true,pick]
  constructor
  · rintro ⟨m,hm,c⟩; exact (ready m hm).mp c
  · exact fun h => ⟨⟨w,by omega⟩,rfl,(ready _ rfl).mpr h⟩

/-- The polylogarithmic bit-product premise at the single fixed exponent 60
suffices for every short modular product used by the group-power reduction. -/
noncomputable def ofPolylogProduct (N : ℕ) (P : Template 1) (ok : BitsCorrect N 60 P) :
    HABPowerReduction.ShortProducts :=
  HABShortLift.toShortProducts (N:=max N (HABPolylogRange.threshold 60)) {
    formula := modular P
    correct := fun large A len p b f prime pad short values bits =>
      modular_correct P ok large A len p b f prime pad short values bits }

end DiophantineNP.HABShortProducts
