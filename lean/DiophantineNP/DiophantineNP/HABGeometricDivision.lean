import DiophantineNP.HABDivisionCorrection
import DiophantineNP.ScaleFormula
import DiophantineNP.HABCRTDot
import DiophantineNP.HABPairInterpretation
import DiophantineNP.HABProductPadding

/-! # Geometric-series division in the finite formula grammar

The geometric numerator has one row for each summand, and each row is an
iterated product of copies of the normalized divisor difference, the scale,
and the multiplicative identity. The query works over a padded domain large
enough to hold the bit positions of the scaled numerator.
-/
namespace DiophantineNP.HABGeometricDivision
open Counting WidthFormula PrimeFormula FiniteArithmeticGap Finset
open HABCRTDot

private abbrev W (n : ℕ) := Template (n+1)
private abbrev ctx {n U : ℕ} (j : Fin U) (e : Fin n→Fin U) : Fin (n+1)→Fin U := Fin.cases j e
private abbrev Reads {n U : ℕ} (w : W n) (A : HAB.Matrix U) (e : Fin n→Fin U) (x : ℕ) :=
  ∀ j : Fin U, w.eval A (ctx j e) = x.testBit j.val

private def rename {a k : ℕ} (p : Template a) (σ : Fin a → Fin k) : Template k :=
  rewriteMatrix (fun r c => .entry r c) p σ

private theorem rename_eval {a k U : ℕ} (p : Template a) (σ : Fin a → Fin k)
    (A : HAB.Matrix U) (e : Fin k→Fin U) :
    (rename p σ).eval A e = p.eval A (e ∘ σ) := rewriteMatrix_eval _ A A (by intros; rfl) _ _ _

private def mux {k : ℕ} (c a b : Template k) : Template k :=
  .disj (.conj c a) (.conj (.neg c) b)

private theorem mux_eval {k U : ℕ} (c a b : Template k) (A : HAB.Matrix U) (e : Fin k→Fin U) :
    (mux c a b).eval A e = if c.eval A e then a.eval A e else b.eval A e := by
  cases h : c.eval A e <;> simp [mux,Template.eval,h]

private def lane {k : ℕ} (r : ℕ) : W k :=
  .ex (.conj (fromFormula (isNat r 0)) (.entry 0 (0 : Fin (k+1)).succ))

private theorem lane_reads {k U : ℕ} (r : ℕ) (hr : r<U) (A : HAB.Matrix U)
    (e : Fin k→Fin U) (x : ℕ) (h : ∀ c : Fin U, A ⟨r,hr⟩ c = x.testBit c.val) :
    Reads (lane r) A e x := by
  intro j
  apply Bool.eq_iff_iff.mpr
  simp only [lane,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,Tentry_eval,Fin.cases_zero,Fin.cases_succ]
  change (∃ v : Fin U, v.val=r ∧ A v j=true) ↔ _
  exact ⟨fun ⟨v,hv,hb⟩ => h j ▸ (show v=⟨r,hr⟩ from Fin.ext hv) ▸ hb,
    fun hb => ⟨⟨r,hr⟩,rfl,(h j).trans hb⟩⟩

private def one {k : ℕ} : W k := fromFormula (isNat 0 0)
private def zero {k : ℕ} : W k := .neg (.atom (.eqv 0 0))
private def scale {k : ℕ} (d : Fin k) : W k := .atom (.eqv 0 d.succ)
private def invMask {k : ℕ} (d : Fin k) (y : W k) : W k :=
  .conj (fromFormula (ltF 0 d.succ)) (.neg y)

private theorem one_reads {k U : ℕ} (A : HAB.Matrix U) (e : Fin k→Fin U) : Reads one A e 1 := by
  intro j; apply Bool.eq_iff_iff.mpr
  rw [one,fromFormula_eval,isNat_spec,Nat.testBit_one_eq_true_iff_self_eq_zero]; rfl

private theorem zero_reads {k U : ℕ} (A : HAB.Matrix U) (e : Fin k→Fin U) : Reads zero A e 0 := by
  intro j; simp [zero,Template.eval,Atom.eval]

private theorem scale_reads {k U : ℕ} (d : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U) :
    Reads (scale d) A e (2^(e d).val) := by
  intro j; simp [scale,Template.eval,Atom.eval,Nat.testBit_two_pow,ctx,Fin.ext_iff,eq_comm]

private theorem invMask_reads {k U y : ℕ} (d : Fin k) (w : W k) (A : HAB.Matrix U)
    (e : Fin k→Fin U) (hy : Reads w A e y) (hb : y<2^(e d).val) :
    Reads (invMask d w) A e (2^(e d).val-(y+1)) := by
  intro j; apply Bool.eq_iff_iff.mpr
  rw [invMask,Tconj_true,fromFormula_eval,ltF_true,Nat.testBit_two_pow_sub_succ hb]
  change (_ ∧ (!w.eval A (ctx j e))=true) ↔ _
  rw [hy j]; simp only [Bool.and_eq_true,decide_eq_true_eq]; rfl

private def restFactor (D B m i r : ℕ) := if r < i then D else if r < m then B else 1

private theorem factor_product (D B m i V : ℕ) (hi : i≤m) (hm : m≤V) :
    productPrefix (restFactor D B m i) V = D^i*B^(m-i) := by
  have aux (v : ℕ) : productPrefix (restFactor D B m i) v =
      D^(min v i)*B^(min v m - min v i) := by
    induction v with
    | zero => simp [productPrefix]
    | succ v ih =>
      rw [product_succ,ih,restFactor]
      by_cases h : v < i
      · simp [h,Nat.min_eq_left (show v+1 ≤ i by omega),Nat.min_eq_left (show v+1≤m by omega),
          Nat.min_eq_left (show v ≤ i by omega),Nat.min_eq_left (show v≤m by omega),pow_succ]
      · by_cases h' : v < m
        · simp only [if_neg h,if_pos h',Nat.min_eq_right (show i≤v by omega),
            Nat.min_eq_right (show i≤v+1 by omega),Nat.min_eq_left (show v+1≤m by omega),
            Nat.min_eq_left h'.le,show v+1-i=(v-i)+1 by omega,pow_succ,Nat.mul_assoc]
        · simp [h,h',Nat.min_eq_right (show i≤v+1 by omega),Nat.min_eq_right (show i≤v by omega),
            Nat.min_eq_right (show m≤v+1 by omega),Nat.min_eq_right (show m≤v by omega)]
  simpa [Nat.min_eq_right (hi.trans hm),Nat.min_eq_right hm] using aux V

/-- Correctness at this universe size only, for products of a specified
maximum numerical magnitude. All other rows and widths are unrestricted. -/
def ProductUpTo (P : Template 1) (U bound : ℕ) : Prop :=
  ∀ (f : ℕ→ℕ), (∀ i<U, f i<2^U) → productPrefix f U≤bound → ∀ j : Fin U,
    P.eval (fun r c => (f r.val).testBit c.val) (fun _=>j)=(productPrefix f U).testBit j.val

private theorem ProductUpTo.mono {P U a b} (h : ProductUpTo P U b) (hab : a≤b) :
    ProductUpTo P U a := fun f hf hp j => h f hf (hp.trans hab) j

private theorem ProductUpTo.full (P : ProductTemplate) (U bound : ℕ) :
    ProductUpTo P.product U bound := fun f hf _ j => P.product_correct f hf j

private def productRows {k : ℕ} (P : Template 1) (cells : W (k+1)) : W k :=
  HABMatrix.bind cells P Fin.succ (fun _ => 0)

private theorem productRows_reads {k U bound : ℕ} (P : Template 1) (cells : W (k+1))
    (A : HAB.Matrix U) (e : Fin k → Fin U) (f : ℕ→ℕ)
    (hf : ∀ r<U, f r<2^U)
    (hP : ProductUpTo P U bound) (ht : productPrefix f U≤bound)
    (hc : ∀ r : Fin U, Reads cells A (ctx r e) (f r.val)) :
    Reads (productRows P cells) A e (productPrefix f U) := by
  intro j
  rw [productRows,HABMatrix.bind_spec]
  have h : (fun r c => cells.eval A (extend c r (ctx j e ∘ Fin.succ))) =
      fun r c : Fin U => (f r.val).testBit c.val := funext fun r => funext (hc r)
  rw [h]; exact hP f hf ht j

/-- Parameters are the product-factor index, summand index, final summand index,
and scale exponent, in that order. -/
private noncomputable def factors : W 4 :=
  mux (fromFormula (ltF 1 2)) (rowAdd (invMask 3 (lane 1)) one)
    (mux (fromFormula (ltF 1 3)) (scale 3) one)

private theorem factors_reads {U y : ℕ} (A : HAB.Matrix U) (hU : 2≤U) (e : Fin 4→Fin U)
    (hY : ∀ c : Fin U, A ⟨1,by omega⟩ c=y.testBit c.val) (hb : y<2^(e 3).val) :
    Reads factors A e (restFactor (2^(e 3).val-y) (2^(e 3).val) (e 2).val (e 1).val (e 0).val) := by
  have decideLt (c : Fin U) (a b : Fin 5) : (fromFormula (ltF a b)).eval A (ctx c e) =
      decide ((ctx c e a).val < (ctx c e b).val) := by
    apply Bool.eq_iff_iff.mpr; rw [fromFormula_eval,ltF_true,decide_eq_true_eq]
  have hd := invMask_reads 3 (lane 1) A e (lane_reads 1 (by omega) A e y hY) hb
  intro c
  simp only [factors,mux_eval,decideLt]
  change (if decide ((e 0).val < (e 1).val) then _ else if decide ((e 0).val < (e 2).val) then _ else _) = _
  by_cases h : (e 0).val < (e 1).val
  · simp only [h,decide_true,if_true,restFactor]
    simpa only [show 2^(e 3).val-(y+1)+1=2^(e 3).val-y by omega] using
      rowAdd_correct (invMask 3 (lane 1)) one A e hU hd (one_reads A e) c
  · by_cases h' : (e 0).val < (e 2).val
    · simpa only [h,h',decide_false,decide_true,if_false,if_true,restFactor] using scale_reads 3 A e c
    · simpa only [h,h',decide_false,if_false,restFactor] using one_reads A e c

private noncomputable def term (P : Template 1) : W 3 :=
  mux (.atom (.leq 1 2)) (productRows P factors) zero

private theorem term_reads {U y : ℕ} (P : Template 1) (A : HAB.Matrix U) (hU : 2≤U) (e : Fin 3→Fin U)
    (hY : ∀ c : Fin U, A ⟨1,by omega⟩ c=y.testBit c.val) (hb : y<2^(e 2).val)
    (hP : ProductUpTo P U (2^((e 2).val*(e 1).val))) :
    Reads (term P) A e (if (e 0).val≤(e 1).val then (2^(e 2).val-y)^(e 0).val *
      (2^(e 2).val)^((e 1).val-(e 0).val) else 0) := by
  intro c
  simp only [term,mux_eval,Template.eval.eq_1,Atom.eval]
  change (if decide ((e 0).val≤(e 1).val) then _ else _) = _
  by_cases h : (e 0).val≤(e 1).val
  · simp only [h,decide_true,if_true]
    let B := 2^(e 2).val
    let f := restFactor (B-y) B (e 1).val (e 0).val
    have hB : B<2^U := Nat.pow_lt_pow_right (by decide) (e 2).isLt
    have fits (r : ℕ) (_ : r<U) : f r < 2^U := by
      dsimp only [f,restFactor]
      split
      · exact (Nat.sub_le _ _).trans_lt hB
      · split
        · exact hB
        · exact Nat.one_lt_two_pow (by omega)
    have total : productPrefix f U=(B-y)^(e 0).val*B^((e 1).val-(e 0).val) :=
      factor_product (B-y) B _ _ U h (e 1).isLt.le
    have bounded : productPrefix f U≤2^((e 2).val*(e 1).val) := calc
      _ ≤ B^(e 0).val*B^((e 1).val-(e 0).val) := by
        rw [total];exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.sub_le ..) _)
      _ = B^(e 1).val := by rw [←pow_add,Nat.add_sub_of_le h]
      _ = _ := (pow_mul ..).symm
    have spec := productRows_reads P factors A e f fits hP bounded (fun r => factors_reads A hU (ctx r e) hY hb) c
    rwa [show productPrefix f U = _ from factor_product (B-y) B _ _ U h (e 1).isLt.le] at spec
  · simpa [h] using zero_reads A e c

/-- The geometric-sum word. Its outer parameters are m=n-1 and the scale exponent. -/
private noncomputable def geometricWith (P : Template 1) : W 2 := sumRows (term P)

private theorem geometricWith_correct {U y : ℕ} (P : Template 1) (A : HAB.Matrix U) (hU : 2≤U) (e : Fin 2→Fin U)
    (hY : ∀ c : Fin U, A ⟨1,by omega⟩ c=y.testBit c.val) (hb : y<2^(e 1).val)
    (hP : ProductUpTo P U (2^((e 1).val*(e 0).val))) :
    Reads (geometricWith P) A e (HABDivision.numerator y (2^(e 1).val) ((e 0).val+1)) := by
  intro c
  rw [geometricWith]
  let m := (e 0).val
  let B := 2^(e 1).val
  let f (i : ℕ) := if i≤m then (B-y)^i*B^(m-i) else 0
  have hh := sumRows_correct (term P) A e f (fun r b => term_reads P A hU (ctx r e) hY hb hP b) c
  have he : (∑ i ∈ range U, f i)=HABDivision.numerator y B (m+1) := by
    rw [HABDivision.numerator]
    simp only [Nat.add_sub_cancel]
    apply Eq.trans (sum_subset (s₁:=range (m+1)) (s₂:=range U) (f:=f)
      (range_mono (by have := (e 0).isLt; dsimp [m]; omega)) (by
        intro i _ hi; simp only [mem_range,not_lt] at hi; simp [f,show ¬i≤m by omega])).symm
    exact sum_congr rfl (fun i hi => if_pos (by have := mem_range.mp hi; omega))
  rwa [he] at hh

private noncomputable def raw (P : Template 1) : W 2 :=
  rowMul (lane 0) (geometricWith P)

/-- A single exact right shift by j*(m+1). If a queried bit is beyond the
padded word, the existential bit address has no witness. -/
private noncomputable def approxWord (P : Template 1) : W 2 :=
  .ex (.conj (fromFormula (Packing.successorFormula 2 0))
    (.ex (.conj (.atom (.mul 4 1 0))
      (.ex (.conj (.atom (.add 1 3 0)) (rename (raw P) ![0,4,5]))))))

private theorem approx_reads {U x y : ℕ} (P : Template 1) (A : HAB.Matrix U) (hU : 2≤U)
    (e : Fin 2→Fin U) (hX : ∀ c : Fin U, A ⟨0,by omega⟩ c=x.testBit c.val)
    (hY : ∀ c : Fin U, A ⟨1,by omega⟩ c=y.testBit c.val)
    (hy : 0<y) (hb : y<2^(e 1).val) (hx : x<2^((e 0).val+1))
    (hpad : (e 1).val*((e 0).val+1)+((e 0).val+1)<U)
    (hP : ProductUpTo P U (2^((e 1).val*(e 0).val))) :
    Reads (approxWord P) A e (HABDivision.estimate x y (2^(e 1).val) ((e 0).val+1)) := by
  let n := (e 0).val+1
  let d := (e 1).val*n
  let B := 2^(e 1).val
  let s := HABDivision.numerator y B n
  have sn : s≤2^d := by
    have id := HABDivision.numerator_identity hb.le n
    change s*y+_=B^n at id
    have hsy := Nat.le_mul_of_pos_right s hy
    have eq : B^n = 2^d := (pow_mul ..).symm
    omega
  have fits : x*s < 2^U := calc
    x*s ≤ x*2^d := Nat.mul_le_mul_left x sn
    _ < 2^n * 2^d := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
    _ = 2^(n+d) := (pow_add ..).symm
    _ ≤ 2^U := Nat.pow_le_pow_right (by decide) (by dsimp [d,n];omega)
  have spec := rowMul_correct (lane 0) (geometricWith P) A e hU
    (lane_reads 0 (by omega) A e x hX) (geometricWith_correct P A hU e hY hb hP)
  have shift : HABDivision.estimate x y B n=(x*s) >>> d := by
    simp [HABDivision.estimate,s,d,B,Nat.shiftRight_eq_div_pow,pow_mul]
  intro c
  apply Bool.eq_iff_iff.mpr
  rw [show HABDivision.estimate x y (2^(e 1).val) ((e 0).val+1) = (x*s) >>> d from shift,
    Nat.testBit_shiftRight]
  simp only [approxWord,Tex_true,Tconj_true,fromFormula_eval,Packing.successorFormula_true,
    Template.eval.eq_1,Atom.eval,decide_eq_true_eq,rename_eval]
  change (∃ v : Fin U, n=v.val ∧ ∃ w : Fin U, (e 1).val*v.val=w.val ∧ ∃ b : Fin U,
      w.val+c.val=b.val ∧ (raw P).eval A _=true) ↔ _
  have evalAt (v w b : Fin U) : (raw P).eval A (Fin.cases b (Fin.cases w (Fin.cases v (ctx c e))) ∘ ![0,4,5]) =
      (x*s).testBit b.val := by
    have ee : Fin.cases b (Fin.cases w (Fin.cases v (ctx c e))) ∘ ![0,4,5] = ctx b e := by
      funext i; fin_cases i <;> rfl
    rw [ee]; exact spec b
  simp_rw [evalAt]
  constructor
  · rintro ⟨v,hv,w,hw,b,he,ht⟩
    rw [←hv] at hw
    simpa only [←he,←hw] using ht
  · intro h
    have hb' : d+c.val<U := by
      by_contra! h'
      have lt := fits.trans_le (Nat.pow_le_pow_right (by decide : 0<2) h')
      simp [Nat.testBit_lt_two_pow lt] at h
    exact ⟨⟨n,by dsimp [n];omega⟩,rfl,⟨d,by omega⟩,rfl,⟨_,hb'⟩,rfl,h⟩

private noncomputable def nextWord (P : Template 1) : W 2 := rowAdd (approxWord P) one

/-- The optional correction is selected by the comparison x < (q+1)*y. -/
private noncomputable def corrected (P : Template 1) : W 2 :=
  mux (rename (wordLt (lane 0) (rowMul (nextWord P) (lane 1))) Fin.succ) (approxWord P) (nextWord P)

private theorem corrected_reads {U x y : ℕ} (P : Template 1) (A : HAB.Matrix U) (hU : 2≤U)
    (e : Fin 2→Fin U) (hX : ∀ c : Fin U, A ⟨0,by omega⟩ c=x.testBit c.val)
    (hY : ∀ c : Fin U, A ⟨1,by omega⟩ c=y.testBit c.val)
    (hy : 0<y) (hb : y<2^(e 1).val) (hby : 2^(e 1).val≤2*y) (hx : x<2^((e 0).val+1))
    (hyLen : y<2^((e 0).val+1)) (hpad : (e 1).val*((e 0).val+1)+((e 0).val+1)<U)
    (hP : ProductUpTo P U (2^((e 1).val*(e 0).val))) :
    Reads (corrected P) A e (x/y) := by
  let n := (e 0).val+1
  let B := 2^(e 1).val
  let q := HABDivision.estimate x y B n
  have hq : Reads (approxWord P) A e q := approx_reads P A hU e hX hY hy hb hx hpad hP
  have hn' : Reads (nextWord P) A e (q+1) := rowAdd_correct _ _ A e hU hq (one_reads A e)
  have xR := lane_reads 0 (by omega) A e x hX
  have yR := lane_reads 1 (by omega) A e y hY
  have hprod := rowMul_correct _ _ A e hU hn' yR
  have cap : 2^n*2≤2^U := by
    rw [←pow_succ]; apply Nat.pow_le_pow_right (by decide); dsimp [n];omega
  have ub : (q+1)*y<2^U := by
    have hqy := (Nat.le_div_iff_mul_le hy).mp (HABDivision.estimate_bounds hy hb.le hby hx).1
    change q*y≤x at hqy
    rw [Nat.add_mul,one_mul]; change y<2^n at hyLen; change x<2^n at hx;omega
  have wx := wordLt_correct (lane 0) (rowMul (nextWord P) (lane 1)) A e xR hprod
    (hx.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [n] at *;omega))) ub
  have cut := HABDivision.corrected_quotient hy hb.le hby hx
  change (if (q+1)*y≤x then q+1 else q)=x/y at cut
  intro c
  rw [corrected,mux_eval,rename_eval]
  change (if (wordLt (lane 0) (rowMul (nextWord P) (lane 1))).eval A e then _ else _) = _
  by_cases h : x<(q+1)*y
  · rw [if_pos (wx.mpr h),hq,←cut,if_neg (by omega)]
  · have hfalse : (wordLt (lane 0) (rowMul (nextWord P) (lane 1))).eval A e=false :=
      Bool.eq_false_iff.mpr (fun h' => h (wx.mp h'))
    rw [hfalse,if_neg Bool.false_ne_true,hn',←cut,if_pos (by omega)]

private noncomputable def normalized : Template 2 :=
  .conj (wordLt (lane 1) (scale 1)) (.neg (wordLt (rowAdd (lane 1) (lane 1)) (scale 1)))

private theorem normalized_spec {V y : ℕ} (A : HAB.Matrix V) (hV : 2≤V) (e : Fin 2→Fin V)
    (hY : ∀ c : Fin V, A ⟨1,by omega⟩ c=y.testBit c.val) (fits : y+y<2^V) :
    normalized.eval A e=true ↔ y<2^(e 1).val ∧ 2^(e 1).val≤2*y := by
  have yr := lane_reads 1 (by omega) A e y hY
  have yr' := rowAdd_correct (lane 1) (lane 1) A e hV yr yr
  have bs := scale_reads 1 A e
  have bf : 2^(e 1).val<2^V := Nat.pow_lt_pow_right (by decide) (e 1).isLt
  simp only [normalized,Tconj_true,Template.eval.eq_4,Bool.not_eq_true',←Bool.not_eq_true,
    wordLt_correct _ _ A e yr bs (by omega) bf,wordLt_correct _ _ A e yr' bs fits bf]
  omega

/-- Free slots are the queried bit and m, where each input has at most m+1 bits.
The matrix stores the dividend and divisor in rows zero and one. -/
noncomputable def divisionWith (P : Template 1) : Template 2 :=
  .ex (.conj (.disj (.atom (.leq 0 2)) (fromFormula (Packing.successorFormula 2 0)))
    (.conj (rename normalized ![2,0]) (rename (corrected P) ![1,2,0])))

/-- A single fixed query returns each bit of the quotient on a quadratically
padded domain. Division by zero follows the natural number convention. -/
theorem divisionWith_correct {V x y : ℕ} (P : Template 1) (A : HAB.Matrix V) (m c : Fin V)
    (hx : x<2^(m.val+1)) (hy : y<2^(m.val+1)) (pad : (m.val+1)^2+(m.val+1)<V)
    (hX : ∀ i : Fin V, A ⟨0,by omega⟩ i=x.testBit i.val)
    (hY : ∀ i : Fin V, A ⟨1,by omega⟩ i=y.testBit i.val)
    (hP : ProductUpTo P V (2^((m.val+1)^2))) :
    (divisionWith P).eval A ![c,m] = (x/y).testBit c.val := by
  let n := m.val+1
  have hV : 2≤V := by nlinarith
  have hn : n<V := by dsimp [n]; omega
  have fit : y+y < 2^V := calc
    y+y < 2^n+2^n := Nat.add_lt_add hy hy
    _ = 2^(n+1) := (Nat.mul_two _).symm.trans (pow_succ 2 n).symm
    _ ≤ 2^V := Nat.pow_le_pow_right (by decide) hn
  apply Bool.eq_iff_iff.mpr
  simp only [divisionWith,Tex_true,Tconj_true,Tdisj_true,fromFormula_eval,Packing.successorFormula_true,
    Template.eval.eq_1,Atom.eval,decide_eq_true_eq,rename_eval]
  have norm (j : Fin V) := normalized_spec A hV (![m,j] : Fin 2→Fin V) hY fit
  have vals (j : Fin V) : Fin.cases j ![c,m] ∘ ![2,0] = ![m,j] := by funext i; fin_cases i <;> rfl
  have vals' (j : Fin V) : Fin.cases j ![c,m] ∘ ![1,2,0] = ctx c (![m,j] : Fin 2→Fin V) := by
    funext i; fin_cases i <;> rfl
  simp_rw [vals,vals',norm]
  change (∃ j : Fin V, (j.val≤m.val ∨ m.val+1=j.val) ∧
    (y<2^j.val ∧ 2^j.val≤2*y) ∧ (corrected P).eval A (ctx c ![m,j])=true) ↔ _
  have spec (j : Fin V) (hj : j.val≤n) (h1 : y<2^j.val) (h2 : 2^j.val≤2*y) :
      (corrected P).eval A (ctx c ![m,j])=(x/y).testBit c.val := by
    have hpos := Nat.two_pow_pos j.val
    have cap : j.val*n+n < V := by
      have := Nat.mul_le_mul_right n hj
      change n^2+n<V at pad; rw [pow_two] at pad;omega
    exact corrected_reads P A hV ![m,j] hX hY (by omega) h1 h2 hx hy cap
      (hP.mono (Nat.pow_le_pow_right (by decide) (by
        change j.val*m.val≤n^2
        rw [pow_two]; exact Nat.mul_le_mul hj (Nat.le_succ _)))) c
  constructor
  · rintro ⟨j,hd,⟨h1,h2⟩,bit⟩
    rwa [spec j (by dsimp [n];omega) h1 h2] at bit
  · intro bit
    have ypos : y≠0 := by rintro rfl; simp at bit
    let d := Nat.log 2 y+1
    have lower : y<2^d := Nat.lt_pow_succ_log_self (by decide) y
    have upper : 2^d≤2*y := by
      dsimp [d]; rw [pow_succ,Nat.mul_comm 2 y]
      exact Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 ypos)
    have hd : d≤n := (Nat.log_lt_of_lt_pow ypos hy)
    let j : Fin V := ⟨d,hd.trans_lt hn⟩
    exact ⟨j,by change d≤m.val ∨ n=d; dsimp [n] at *;omega,⟨lower,upper⟩,
      (spec j hd lower upper).trans bit⟩

/-- The geometric-sum word for a full product template. -/
noncomputable def geometric (P : ProductTemplate) : W 2 := geometricWith P.product

theorem geometric_correct {U y : ℕ} (P : ProductTemplate) (A : HAB.Matrix U) (hU : 2≤U) (e : Fin 2→Fin U)
    (hY : ∀ c : Fin U, A ⟨1,by omega⟩ c=y.testBit c.val) (hb : y<2^(e 1).val) :
    Reads (geometric P) A e (HABDivision.numerator y (2^(e 1).val) ((e 0).val+1)) :=
  geometricWith_correct P.product A hU e hY hb (ProductUpTo.full P _ _)

/-- Specialization of the padded geometric division to a full product template. -/
noncomputable def division (P : ProductTemplate) : Template 2 := divisionWith P.product

theorem division_correct {V x y : ℕ} (P : ProductTemplate) (A : HAB.Matrix V) (m c : Fin V)
    (hx : x<2^(m.val+1)) (hy : y<2^(m.val+1)) (pad : (m.val+1)^2+(m.val+1)<V)
    (hX : ∀ i : Fin V, A ⟨0,by omega⟩ i=x.testBit i.val)
    (hY : ∀ i : Fin V, A ⟨1,by omega⟩ i=y.testBit i.val) :
    (division P).eval A ![c,m] = (x/y).testBit c.val :=
  divisionWith_correct P.product A m c hx hy pad hX hY (ProductUpTo.full P _ _)

open HABPairInterpretation HABProductPadding

private def expand {U : ℕ} (A : HAB.Matrix U) : HAB.Matrix (U*U) :=
  fun r c => (factor A r.val).testBit c.val

private def promote {U : ℕ} (hU : 2≤U) (a : Fin U) : Fin (U*U) :=
  ⟨a.val,a.isLt.trans_le (by nlinarith)⟩

private noncomputable def square {k : ℕ} (p : Template k) : Template k :=
  .ex (.conj (fromFormula (isNat 0 0)) (compileTemplate @cell p (fun _ => 0) Fin.succ))

private theorem square_spec {k U : ℕ} (p : Template k) (hU : 2≤U) (A : HAB.Matrix U)
    (e : Fin k→Fin U) :
    (square p).eval A e = p.eval (expand A) (promote hU ∘ e) := by
  apply Bool.eq_iff_iff.mpr
  simp only [square,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,Fin.cases_zero]
  have single (z : Fin U) (hz : z.val=0) :
      (compileTemplate @cell p (fun _ => 0) Fin.succ).eval A (ctx z e) =
        p.eval (expand A) (promote hU ∘ e) := by
    rw [compileTemplate_correct @cell _ _ _ A (expand A) _ (fun rh rl ch cl env => cell_spec rh rl ch cl A env)]
    apply congrArg (p.eval (expand A)); funext i; apply Fin.ext
    change (e i).val+U*z.val=(e i).val
    simp [hz]
  exact ⟨fun ⟨z,hz,h⟩ => (single z hz) ▸ h,
    fun h => ⟨⟨0,by omega⟩,rfl,(single _ rfl).trans h⟩⟩

private def lastSlot : Template 2 := .neg (.ex (fromFormula (ltF 1 0)))

/-- The division query on the original binary matrix. The virtual fourth-power
universe and its majority quantifiers are implemented by two square interpretations. -/
noncomputable def quotient (P : ProductTemplate) : Template 1 :=
  .ex (.conj lastSlot (rename (square (square (division P))) ![1,0]))

theorem quotient_correct {U : ℕ} (P : ProductTemplate) (hU : 2≤U) (A : HAB.Matrix U) (c : Fin U) :
    (quotient P).eval A (fun _=>c) =
      (HAB.rowWord (A ⟨0,by omega⟩) / HAB.rowWord (A ⟨1,by omega⟩)).testBit c.val := by
  let S := U*U
  have hS : 2≤S := by dsimp [S];nlinarith
  let B := expand A
  let C := expand B
  let m : Fin U := ⟨U-1,by omega⟩
  let E (a : Fin U) := promote hS (promote hU a)
  let x := HAB.rowWord (A ⟨0,by omega⟩)
  let y := HAB.rowWord (A ⟨1,by omega⟩)
  have hbits (r : ℕ) (hr : r<U) (i : Fin (S*S)) :
      C ⟨r,hr.trans_le (by nlinarith [Nat.le_mul_self U,Nat.le_mul_self (U*U)])⟩ i =
        (HAB.rowWord (A ⟨r,hr⟩)).testBit i.val := by
    have hrs : r < S := hr.trans_le (by dsimp [S];nlinarith)
    have Bword : HAB.rowWord (B ⟨r,hrs⟩) = HAB.rowWord (A ⟨r,hr⟩) := by
      change HAB.rowWord (fun c : Fin S => (factor A r).testBit c.val) = _
      rw [factor,dif_pos hr,HAB.rowWord_natural]
      exact (HAB.rowWord_bound _).trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [S];nlinarith))
    change (factor B r).testBit i.val = _
    simp only [factor,dif_pos (show r<U*U from hrs),Bword]
  have memb : (E m).val+1=U := by change U-1+1=U;omega
  have wide : U^2+U<S*S := by
    have hsq : 2*U ≤ U*U := Nat.mul_le_mul_right U hU
    have htw : 2 ≤ U*U := by nlinarith
    have hlarge := Nat.mul_le_mul_right (U*U) htw
    dsimp [S]; nlinarith
  have ans := division_correct (V:=S*S) (x:=x) (y:=y) P C (E m) (E c)
    (memb ▸ HAB.rowWord_bound _) (memb ▸ HAB.rowWord_bound _) (memb ▸ wide)
    (hbits 0 (by omega)) (hbits 1 (by omega))
  have test (a : Fin U) : lastSlot.eval A (ctx a (fun _ : Fin 1=>c))=true ↔ a=m := by
    simp only [lastSlot,Template.eval.eq_4,Bool.not_eq_true',←Bool.not_eq_true,Tex_true,fromFormula_eval,ltF_true,
      Fin.cases_zero,not_exists]
    change (∀ z : Fin U, ¬ a.val < z.val) ↔ a=m
    exact ⟨fun h => Fin.ext (by have := h m; have := a.isLt; dsimp [m] at *;omega),
      fun h z => by have := z.isLt; subst a;dsimp [m];omega⟩
  apply Bool.eq_iff_iff.mpr
  simp only [quotient,Tex_true,Tconj_true,rename_eval]
  change (∃ a : Fin U, lastSlot.eval A (ctx a (fun _ : Fin 1=>c))=true ∧ _) ↔ _
  simp_rw [test]
  rw [exists_eq_left]
  rw [square_spec _ hU,square_spec _ hS]
  have he : promote hS ∘ promote hU ∘ (ctx m (fun _ : Fin 1=>c)) ∘ ![1,0] = ![E c,E m] := by
    funext i; fin_cases i <;> rfl
  rw [he]; exact Bool.eq_iff_iff.mp ans

/-- Division of two arbitrary full-width binary inputs is definable in the
literal HAB vocabulary if iterated multiplication is definable there. -/
theorem division_in_FOM_of_imult (h : HAB.ImultInFOM) :
    ∃ φ : HAB.Form 1, ∀ {U : ℕ} (hU : 2≤U) (A : HAB.Matrix U) (j : Fin U),
      φ.Holds A (fun _ => j) ↔
        (HAB.rowWord (A ⟨0,by omega⟩) / HAB.rowWord (A ⟨1,by omega⟩)).testBit j.val=true := by
  let P := HAB.productTemplate_of_imult h
  exact ⟨HAB.toSource (quotient P),fun hU A j =>
    (HAB.toSource_correct _ _ _).trans (Bool.eq_iff_iff.mp (quotient_correct P hU A j))⟩

end DiophantineNP.HABGeometricDivision
