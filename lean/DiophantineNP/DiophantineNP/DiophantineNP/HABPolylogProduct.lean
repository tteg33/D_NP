import DiophantineNP.HABShortLength
import DiophantineNP.HABCRTBitDecision

/-! # Iterated products with polylogarithmic output length

The fixed template for each d reads the original binary matrix. It internally
chooses the block length and precision, builds the CRT numerator, divides it
by the auxiliary blocks, and corrects the last bit. No modular-power or
iterated-product formula is supplied as input.
-/
namespace DiophantineNP.HABPolylogProduct
open Counting WidthFormula FiniteArithmeticGap PrimeFormula HABShortLength

def threshold (d : ℕ) := max 4 (HABPolylogRange.threshold (4*(2*d+2)+9))
private def last {k} (v : Fin k) : Template k := .neg (.ex (fromFormula (ltF v.succ 0)))

private theorem last_spec {k U} (v : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U) :
    (last v).eval A e=true ↔ (e v).val=U-1 := by
  simp only [last,Template.eval.eq_4,Bool.not_eq_true',←Bool.not_eq_true,Tex_true,
    fromFormula_eval,ltF_true,Fin.cases_succ,Fin.cases_zero,not_exists,not_lt]
  constructor
  · intro h; have hu := (e v).isLt
    have h' := h ⟨U-1,by omega⟩
    change U-1≤(e v).val at h'; omega
  · intro h i; have := i.isLt; omega

/-- k and L are quantified once. The requested bit index is the only free variable. -/
noncomputable def formula (d : ℕ) : Template 1 :=
  .ex (.conj (parameter d 0) (.conj (fromFormula (ltF 1 0))
    (.ex (.conj (last 0) (HABCRTBitDecision.matrixBit 1 2 0)))))

theorem matrix_correct (d : ℕ) {U : ℕ} (hu : threshold d≤U) (A : HAB.Matrix U) (j : Fin U)
    (hp : (∏ r : Fin U, HAB.rowWord (A r))<2^(U.log2^d)) :
    (formula d).eval A (fun _=>j) = (∏ r : Fin U, HAB.rowWord (A r)).testBit j.val := by
  let x := ∏ r : Fin U, HAB.rowWord (A r)
  have h4 := (le_max_left 4 _).trans hu
  have large := (le_max_right 4 _).trans hu
  obtain ⟨lo,hi,kfit,wfit⟩ := parameters d large h4
  let k : Fin U := ⟨HABShortLength.bits d U,kfit⟩
  let prec : Fin U := ⟨U-1,by omega⟩
  have test (hk : j.val<k.val) := by
    let K := HABPolylogRange.tableBits (4*(2*d+2)+9) U
    obtain ⟨hK,_,cap⟩ := HABPolylogRange.range_covered (p:=0) large (Nat.zero_le _)
    have room : x+2^j.val<HABCRTShift.block k.val 0 := by
      have hpos : 1≤k.val := by change 1≤HABShortLength.bits d U; omega
      have he : k.val-1+1=k.val := by omega
      have a : x<2^(k.val-1) := hp.trans_le (Nat.pow_le_pow_right (by decide) (by change _≤HABShortLength.bits d U-1; omega))
      calc
        _ < 2^(k.val-1)+2^(k.val-1) := Nat.add_lt_add_of_lt_of_le a (Nat.pow_le_pow_right (by decide) (by omega))
        _ = 2^k.val := by rw [←he] at ⊢; simp [pow_succ,Nat.mul_two]
        _ ≤ _ := HABCRTShift.block_lower ..
    have small (t : ℕ) (ht : t≤j.val) (p : ℕ) (hm : p∈HABPrimeBlocks.primeSet k.val t) :
        p≤2^K := by
      obtain ⟨c,hc,rfl⟩ := HABPrimeBlocks.mem_primeSet.mp hm
      exact (HABPolylogRange.block_covered (s:=j.val) large hi (hk.le.trans hi) ht hc).2.1
    exact HABCRTBitDecision.matrixBit_correct (1 : Fin 3) 2 0 A
      (extend prec k (fun _ : Fin 1 => j)) hK cap rfl small room
  apply Bool.eq_iff_iff.mpr
  simp only [formula,Tex_true,Tconj_true,parameter_correct _ _ _ _ (by omega : 3≤U) wfit,
    fromFormula_eval,ltF_true,last_spec,Fin.cases_zero]
  change (∃ b : Fin U, b.val=HABShortLength.bits d U ∧ j.val<b.val ∧ ∃ L : Fin U, L.val=U-1 ∧
    (HABCRTBitDecision.matrixBit 1 2 0).eval A (extend L b (fun _ : Fin 1=>j))=true) ↔ x.testBit j.val=true
  constructor
  · rintro ⟨b,hb,hj,L,hL,H⟩
    obtain rfl : b=k := Fin.ext hb
    obtain rfl : L=prec := Fin.ext hL
    rwa [test hj] at H
  · intro H
    have hj : j.val<k.val := by
      by_contra! h
      have le : U.log2^d≤j.val := by change HABShortLength.bits d U≤_ at h; omega
      exact Bool.noConfusion (H.symm.trans (Nat.testBit_lt_two_pow (hp.trans_le (Nat.pow_le_pow_right (by decide) le))))
    exact ⟨k,rfl,hj,prec,rfl,(test hj).trans H⟩

/-- The low-bit interface used to discharge the short product calls in §6. -/
theorem formula_correct (d : ℕ) {U : ℕ} (hu : threshold d≤U) (f : ℕ→ℕ)
    (fits : ∀ i<U, f i<2^U) (hp : productPrefix f U<2^(U.log2^d)) (j : Fin U) :
    (formula d).eval (fun r c=> (f r.val).testBit c.val) (fun _=>j) = (productPrefix f U).testBit j.val := by
  let A : HAB.Matrix U := fun r c => (f r.val).testBit c.val
  have hf (r : Fin U) : HAB.rowWord (A r)=f r.val := HAB.rowWord_natural (fits r.val r.isLt)
  have finprod (n : ℕ) : (∏ r : Fin n, f r.val)=productPrefix f n := by
    induction n with
    | zero => simp [productPrefix]
    | succ n ih => rw [Fin.prod_univ_castSucc,product_succ,←ih]; rfl
  have eq : (∏ r : Fin U,HAB.rowWord (A r))=productPrefix f U := by simp only [hf,finprod]
  rw [←eq] at hp ⊢
  exact matrix_correct d hu A j hp

end DiophantineNP.HABPolylogProduct
