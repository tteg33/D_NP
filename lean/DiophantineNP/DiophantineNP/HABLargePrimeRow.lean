import DiophantineNP.HABIndexSum
import DiophantineNP.HABSpacePadding
import DiophantineNP.HABPowerReduction
import DiophantineNP.WidthPrimeResidue

/-! Convert a variable-width binary row to its residue modulo a represented prime.
The only arithmetic subroutine is a literal source formula for modular powering.
Padding is used to hold the ordinary sum of the bit weights. -/
namespace DiophantineNP.HABLargePrimeRow
open Counting WidthFormula FiniteArithmeticGap HAB Finset

abbrev Powers {V : ℕ} (pow : Form 4) (A : Matrix V) := ∀ a j b p : Fin V, p.val.Prime →
  (pow.Holds A ![a,j,b,p] ↔ a.val^j.val ≡ b.val [MOD p.val])

def weight {n : ℕ} (pow : Form 4) (j p b : Fin n) : Template n :=
  .ex (.conj (fromFormula (isNat 2 0)) (.conj (fromFormula (PrimeFormula.ltF b.succ p.succ))
    ((pow.rename ![0,j.succ,b.succ,p.succ]).translate)))

theorem weight_spec {n V : ℕ} (pow : Form 4) (j p b : Fin n) (A : Matrix V)
    (e : Fin n→Fin V) (ok : Powers pow A) (hp : (e p).val.Prime) :
    (weight pow j p b).eval A e=true ↔ (e b).val=2^(e j).val%(e p).val := by
  have env (two : Fin V) : Fin.cases two e ∘ (![0,j.succ,b.succ,p.succ] : Fin 4→Fin (n+1)) =
      ![two,e j,e b,e p] := by funext i; fin_cases i <;> rfl
  simp only [weight,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,PrimeFormula.ltF_true,
    Form.translate_correct,Form.rename_correct,env,ok _ _ _ _ hp,Fin.cases_zero,Fin.cases_succ]
  constructor
  · rintro ⟨two,ht,hb,hm⟩
    change two.val^(e j).val%(e p).val=(e b).val%(e p).val at hm
    rw [ht,Nat.mod_eq_of_lt hb] at hm
    exact hm.symm
  · intro h
    have h2 := hp.two_le.trans_lt (e p).isLt
    have small : (e b).val<(e p).val := h ▸ Nat.mod_lt _ hp.pos
    exact ⟨⟨2,h2⟩,rfl,small,by change 2^(e j).val%(e p).val=(e b).val%(e p).val; rw [Nat.mod_eq_of_lt small,h]⟩

private def cells {n : ℕ} (pow : Form 4) (row w p : Fin n) : Template (n+2) :=
  let enabled := Template.conj (fromFormula (PrimeFormula.ltF 1 w.succ.succ)) (.entry row.succ.succ 1)
  .disj (.conj enabled (weight pow 1 p.succ.succ 0))
    (.conj (.neg enabled) (fromFormula (isNat 0 0)))

private def term (x p i : ℕ) := if x.testBit i then 2^i%p else 0

private theorem cells_spec {n V x : ℕ} (pow : Form 4) (row w p : Fin n) (A : Matrix V) (e : Fin n→Fin V)
    (ok : Powers pow A) (hp : (e p).val.Prime)
    (bits : ∀ j : Fin V, j.val<(e w).val → A (e row) j=x.testBit j.val) (j b : Fin V) :
    (cells pow row w p).eval A (extend b j e)=true ↔
    b.val=(if j.val<(e w).val then term x (e p).val j.val else 0) := by
  let env := extend b j e
  let on : Template (n+2) := .conj (fromFormula (PrimeFormula.ltF 1 w.succ.succ)) (.entry row.succ.succ 1)
  have hon : on.eval A env=true ↔ j.val<(e w).val ∧ A (e row) j=true := by
    simp only [on,Tconj_true,fromFormula_eval,PrimeFormula.ltF_true,Tentry_eval]; rfl
  change (.disj (.conj on _) (.conj (.neg on) _) : Template _).eval A env=true ↔ _
  have hw := weight_spec pow (1 : Fin (n+2)) p.succ.succ 0 A env ok hp
  simp only [Tdisj_true,Tconj_true,hw,Template.eval.eq_4,Bool.not_eq_true',←Bool.not_eq_true,hon,fromFormula_eval,isNat_spec]
  change ((j.val<(e w).val ∧ A (e row) j=true) ∧ b.val=2^j.val%(e p).val ∨
    ¬(j.val<(e w).val ∧ A (e row) j=true) ∧ b.val=0) ↔ _
  by_cases h : j.val<(e w).val
  · cases he : x.testBit j.val <;> simp [h,bits j h,he,term]
  · simp [h]

private theorem aggregate {V w : ℕ} (x p : ℕ) (hw : w≤V) :
    (∑ i ∈ range V, if i<w then term x p i else 0) = ∑ i ∈ range w, term x p i := by
  rw [←Finset.sum_filter]
  have h : (range V).filter (fun i => i<w)=range w := by ext i; simp; omega
  rw [h]

private theorem aggregate_mod (x p w : ℕ) :
    (∑ i ∈ range w, term x p i) ≡ Readout.word x.testBit w [MOD p] := by
  induction w with
  | zero => simp [Readout.word,Readout.prefixSum,Nat.ModEq]
  | succ w ih =>
    rw [sum_range_succ]
    change _ ≡ Readout.word x.testBit w+(x.testBit w).toNat*2^w [MOD p]
    apply ih.add
    cases h : x.testBit w <;> simp [term,h,Nat.ModEq]

/-- Free arguments name the input row, its width, the prime, and the proposed residue. -/
noncomputable def formula {n : ℕ} (pow : Form 4) (row w p b : Fin n) : Template n :=
  .ex (.conj (HABIndexSum.fromGraph 0 (cells pow row.succ w.succ p.succ))
    (fromFormula (WidthPrimeResidue.remainder 0 p.succ b.succ)))

theorem formula_correct {n V x : ℕ} (pow : Form 4) (row w p b : Fin n) (A : Matrix V)
    (e : Fin n→Fin V) (ok : Powers pow A) (hp : (e p).val.Prime)
    (cap : (e w).val*(e p).val<V) (fits : x<2^(e w).val)
    (bits : ∀ j : Fin V, j.val<(e w).val → A (e row) j=x.testBit j.val) :
    (formula pow row w p b).eval A e=true ↔ (e b).val=x%(e p).val := by
  let f := fun i => if i<(e w).val then term x (e p).val i else 0
  let S := ∑ i ∈ range V,f i
  have sum_eq : S=∑ i ∈ range (e w).val, term x (e p).val i := aggregate _ _ (e w).isLt.le
  have hb : S<V := by
    rw [sum_eq]
    have h : ∑ i ∈ range (e w).val, term x (e p).val i ≤ ∑ _i ∈ range (e w).val,(e p).val := by
      apply sum_le_sum; intro i _
      unfold term
      split
      · exact (Nat.mod_lt _ hp.pos).le
      · exact Nat.zero_le _
    exact h.trans_lt (by simpa using cap)
  have residue : S%(e p).val=x%(e p).val := by
    rw [sum_eq]
    simpa only [Readout.word_native fits] using aggregate_mod x (e p).val (e w).val 
  have spec (z : Fin V) : (HABIndexSum.fromGraph 0 (cells pow row.succ w.succ p.succ)).eval A
      (Fin.cases z e)=true ↔ z.val=S := by
    let env : Fin (n+1)→Fin V := Fin.cases z e
    exact HABIndexSum.fromGraph_correct 0 (cells pow row.succ w.succ p.succ) A env f
      (cells_spec pow row.succ w.succ p.succ A env ok hp bits) hb
  have remainder (z : Fin V) : (WidthPrimeResidue.remainder 0 p.succ b.succ).eval (Fin.cases z e)=true ↔
      (e b).val=z.val%(e p).val := by
    let env : Fin (n+1)→Fin V := Fin.cases z e
    exact WidthPrimeResidue.rem_true 0 p.succ b.succ env hp.pos
  simp only [formula,Tex_true,Tconj_true,spec,fromFormula_eval,remainder]
  exact ⟨fun ⟨z,hz,h⟩ => (hz ▸ h).trans residue,fun h => ⟨⟨S,hb⟩,rfl,h.trans residue.symm⟩⟩

/-- The short-products interface is sufficient to instantiate the only subroutine. -/
noncomputable def fromShortProducts {n : ℕ} (prod : HABPowerReduction.ShortProducts)
    (row w p b : Fin n) : Template n := formula (HABPowerReduction.primePOW prod) row w p b

theorem fromShortProducts_correct {n V x : ℕ} (prod : HABPowerReduction.ShortProducts)
    (row w p b : Fin n) (A : Matrix V) (e : Fin n→Fin V) (hp : (e p).val.Prime)
    (cap : (e w).val*(e p).val<V) (fits : x<2^(e w).val)
    (bits : ∀ j : Fin V, j.val<(e w).val → A (e row) j=x.testBit j.val) :
    (fromShortProducts prod row w p b).eval A e=true ↔ (e b).val=x%(e p).val :=
  formula_correct _ row w p b A e (HABPowerReduction.primePOW_correct prod A) hp cap fits bits

private def largest {n : ℕ} (m : Fin n) : Template n :=
  .neg (.ex (fromFormula (PrimeFormula.ltF m.succ 0)))

private theorem largest_spec {n U : ℕ} (m : Fin n) (A : Matrix U) (e : Fin n→Fin U) :
    (largest m).eval A e=true ↔ (e m).val+1=U := by
  simp only [largest,Template.eval.eq_4,Bool.not_eq_true',←Bool.not_eq_true,Tex_true,
    fromFormula_eval,PrimeFormula.ltF_true,Fin.cases_zero,Fin.cases_succ,not_exists,not_lt]
  have fit := (e m).isLt
  exact ⟨fun h => by have := h ⟨U-1,by omega⟩; dsimp at this; omega,
    fun h i => by have := i.isLt; omega⟩

private def successor {n : ℕ} (x y : Fin n) : Template n :=
  .ex (.conj (fromFormula (isNat 1 0)) (.atom (.add x.succ 0 y.succ)))

private theorem successor_spec {n U : ℕ} (x y : Fin n) (A : Matrix U) (e : Fin n→Fin U) :
    (successor x y).eval A e=true ↔ (e x).val+1=(e y).val := by
  simp only [successor,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,Fin.cases_zero,
    Template.eval.eq_1,Atom.eval,Fin.cases_succ,decide_eq_true_eq]
  exact ⟨fun ⟨i,h,eq⟩ => by omega,fun h => ⟨⟨1,by have := (e y).isLt;omega⟩,rfl,h⟩⟩

private noncomputable def widenRow {n : ℕ} (prod : HABPowerReduction.ShortProducts)
    (row m p b : Fin n) : Template n :=
  .ex (.conj (successor m.succ 0) (fromShortProducts prod row.succ 0 p.succ b.succ))

/-- The original U-bit row and an arbitrary prime below U, in the HAB source
grammar. The polynomial padding and the choice of the width are internal. -/
noncomputable def fullRow {n : ℕ} (prod : HABPowerReduction.ShortProducts) (row p b : Fin n) : Form n :=
  toSource (.ex (.conj (largest 0) (HABSpacePadding.pad 1 (widenRow prod row.succ 0 p.succ b.succ))))

theorem fullRow_correct {n U : ℕ} (prod : HABPowerReduction.ShortProducts) (row p b : Fin n)
    (A : Matrix U) (e : Fin n→Fin U) (hp : (e p).val.Prime) :
    (fullRow prod row p b).Holds A e ↔ (e b).val=rowWord (A (e row))%(e p).val := by
  let V := HABSpacePadding.size U 1
  let B := HABSpacePadding.matrix A 1
  have hU := hp.two_le.trans_lt (e p).isLt
  have fit : U<V := by change U<U*U; nlinarith
  have budget : U*(e p).val<V := by
    change U*(e p).val<U*U
    exact Nat.mul_lt_mul_of_pos_left (e p).isLt (by omega)
  let x := rowWord (A (e row))
  have bits (j : Fin V) (hj : j.val<U) :
      B (HABSpacePadding.index (e row) 1) j=x.testBit j.val := by
    rw [show x.testBit j.val=A (e row) ⟨j.val,hj⟩ from rowWord_bit _ ⟨j.val,hj⟩]
    apply Bool.eq_iff_iff.mpr
    rw [HABSpacePadding.matrix_true]
    simp only [HABSpacePadding.index_val]
    exact ⟨fun ⟨r,c,⟨hr,hc⟩,bit⟩ => by rwa [Fin.ext hr,show c=⟨j.val,hj⟩ from Fin.ext hc] at bit,
      fun bit => ⟨e row,⟨j.val,hj⟩,⟨rfl,rfl⟩,bit⟩⟩
  have outer (m : Fin U) (hm : m.val+1=U) :
      (HABSpacePadding.pad 1 (widenRow prod row.succ 0 p.succ b.succ)).eval A (Fin.cases m e)=true ↔
      (e b).val=x%(e p).val := by
    rw [HABSpacePadding.pad_correct _ _ _ _ (by omega)]
    let f : Fin (n+1)→Fin V := fun i => HABSpacePadding.index (Fin.cases m e i) 1
    have val (v : Fin U) : (HABSpacePadding.index v 1).val=v.val := HABSpacePadding.index_val v 1
    have use (w : Fin V) (hw : w.val=U) :
        (fromShortProducts prod row.succ.succ 0 p.succ.succ b.succ.succ).eval B (Fin.cases w f)=true ↔
        (e b).val=x%(e p).val := by
      let g : Fin (n+2)→Fin V := Fin.cases w f
      have gp : (g p.succ.succ).val=(e p).val := val _
      have gb : (g b.succ.succ).val=(e b).val := val _
      have gw : (g 0).val=U := hw
      rw [←gb,←gp]
      exact fromShortProducts_correct prod _ 0 _ _ B g (gp ▸ hp) (by rw [gw,gp]; exact budget)
        (by rw [gw]; exact rowWord_bound _)
        (fun j hj => bits j (by rwa [gw] at hj))
    change (widenRow prod row.succ 0 p.succ b.succ).eval B f=true ↔ _
    simp only [widenRow,Tex_true,Tconj_true,successor_spec,Fin.cases_succ,Fin.cases_zero]
    have high : (f 0).val+1=U := (val m) ▸ hm
    constructor
    · rintro ⟨w,hw,h⟩; exact (use w (hw ▸ high)).mp h
    · intro h; exact ⟨⟨U,fit⟩,high,(use ⟨U,fit⟩ rfl).mpr h⟩
  simp only [fullRow,toSource_correct,Tex_true,Tconj_true,largest_spec,Fin.cases_zero]
  constructor
  · rintro ⟨m,hm,h⟩; exact (outer m hm).mp h
  · intro h
    let m : Fin U := ⟨U-1,by omega⟩
    have hm : m.val+1=U := by dsimp [m]; omega
    exact ⟨m,hm,(outer m hm).mpr h⟩

end DiophantineNP.HABLargePrimeRow
