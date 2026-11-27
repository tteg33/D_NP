import DiophantineNP.HABProductEquivalence
import DiophantineNP.HABCRTDot

/-! Verify a supplied binary quotient by exact inequalities in the literal
HAB language. The three free variables select arbitrary input rows. -/
namespace DiophantineNP.HABDivisionGraph
open Counting WidthFormula FiniteArithmeticGap HAB HABPairInterpretation HABProductPadding
attribute [local irreducible] HABCRTDot.rowMul HABCRTDot.rowAdd HABCRTDot.wordLt

private def row (r : Fin 3) : Template 4 := .entry r.succ 0

private noncomputable def test : Template 3 :=
  let m := HABCRTDot.rowMul (row 2) (row 1)
  .conj (.neg (HABCRTDot.wordLt (row 0) m))
    (HABCRTDot.wordLt (row 0) (HABCRTDot.rowAdd m (row 1)))

private theorem exact_test (x y q : ℕ) :
    (¬ x<q*y) ∧ x<q*y+y ↔ 0<y ∧ q=x/y := by
  constructor
  · rintro ⟨lo,hi⟩
    have hy : 0<y := by by_contra! h; simp [show y=0 by omega] at hi
    refine ⟨hy,Nat.le_antisymm ((Nat.le_div_iff_mul_le hy).mpr (by omega)) ?_⟩
    have : x/y<q+1 := (Nat.div_lt_iff_lt_mul hy).mpr (by simpa [Nat.add_mul] using hi)
    omega
  · rintro ⟨hy,rfl⟩
    exact ⟨(Nat.div_mul_le_self x y).not_gt,by
      simpa [Nat.mul_add,Nat.add_mul,Nat.mul_comm y] using Nat.lt_mul_div_succ x hy⟩

private theorem test_spec {V : ℕ} (A : Matrix V) (e : Fin 3→Fin V)
    (x y q : ℕ) (hV : 2≤V)
    (hx : ∀ j : Fin V, A (e 0) j = x.testBit j.val)
    (hy : ∀ j : Fin V, A (e 1) j = y.testBit j.val)
    (hq : ∀ j : Fin V, A (e 2) j = q.testBit j.val)
    (hf : x<2^V) (hg : q*y+y<2^V) :
    test.eval A e = true ↔ 0<y ∧ q=x/y := by
  let m := HABCRTDot.rowMul (row 2) (row 1)
  have prodBit (j : Fin V) : m.eval A (Fin.cases j e) = (q*y).testBit j.val :=
    HABCRTDot.rowMul_correct (row 2) (row 1) A e hV hq hy j
  have plusBit (j : Fin V) : (HABCRTDot.rowAdd m (row 1)).eval A (Fin.cases j e) =
      (q*y+y).testBit j.val := HABCRTDot.rowAdd_correct m (row 1) A e hV prodBit hy j
  change (Template.conj _ _).eval A e=true ↔ _
  rw [Tconj_true]
  change (Bool.not ((HABCRTDot.wordLt (row 0) m).eval A e) = true ∧ _) ↔ _
  rw [Bool.not_eq_true',← Bool.not_eq_true,
    HABCRTDot.wordLt_correct (row 0) m A e hx prodBit hf (by omega),
    HABCRTDot.wordLt_correct (row 0) (HABCRTDot.rowAdd m (row 1)) A e hx plusBit hf hg]
  exact exact_test .. 

private noncomputable def padded : Form 3 :=
  .ex (.conj (indexNat 0 0)
    (toSource (compile @cell (toSource test) (fun _ => 0) Fin.succ)))

private theorem padded_spec {U : ℕ} (hU : 2≤U) (A : Matrix U) (e : Fin 3→Fin U) :
    padded.Holds A e ↔ 0<rowWord (A (e 1)) ∧ rowWord (A (e 2))=rowWord (A (e 0))/rowWord (A (e 1)) := by
  let B : Matrix (U*U) := fun r c => (factor A r.val).testBit c.val
  let z : Fin U := ⟨0,by omega⟩
  let ev : Fin 3→Fin (U*U) := fun i => code z (e i)
  have bits (i : Fin 3) (j : Fin (U*U)) : B (ev i) j=(rowWord (A (e i))).testBit j.val := by
    change (factor A ((e i).val+U*0)).testBit j.val=_
    simp [factor,(e i).isLt]
  have hx := rowWord_bound (A (e 0))
  have hy := rowWord_bound (A (e 1))
  have hq := rowWord_bound (A (e 2))
  have wide : 2*U≤U*U := Nat.mul_le_mul_right U hU
  have big : 2^U*2^U≤2^(U*U) := by
    rw [←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have bound : rowWord (A (e 2))*rowWord (A (e 1))+rowWord (A (e 1))<2^(U*U) := calc
    _ = (rowWord (A (e 2))+1)*rowWord (A (e 1)) := by ring
    _ ≤ 2^U*rowWord (A (e 1)) := Nat.mul_le_mul_right _ hq
    _ < 2^U*2^U := Nat.mul_lt_mul_of_pos_left hy (Nat.two_pow_pos _)
    _ ≤ _ := big
  have checked := test_spec B ev _ _ _ (by nlinarith) (bits 0) (bits 1) (bits 2)
    (hx.trans_le (Nat.pow_le_pow_right (by decide) (by omega))) bound
  have single (s : Fin U) (hs : s.val=0) :
      (toSource (compile @cell (toSource test) (fun _ => 0) Fin.succ)).Holds A (Fin.cases s e) ↔
      test.eval B ev=true := by
    obtain rfl : s=z := Fin.ext hs
    rw [toSource_correct,compile_correct @cell _ _ _ A B _ (fun rh rl ch cl env => cell_spec rh rl ch cl A env)]
    exact toSource_correct test B ev
  change (∃ s : Fin U, (indexNat 0 0).Holds A (Fin.cases s e) ∧ _) ↔ _
  simp only [indexNat_correct,Fin.cases_zero]
  constructor
  · rintro ⟨s,hs,h⟩; exact checked.mp ((single s hs).mp h)
  · intro h; exact ⟨z,rfl,(single z rfl).mpr (checked.mpr h)⟩

private def tiny : Form 3 := .neg (.ex (indexNat 1 0))

private theorem tiny_spec {U : ℕ} (A : Matrix U) (e : Fin 3→Fin U) : tiny.Holds A e ↔ U≤1 := by
  change ¬ (∃ s : Fin U, (indexNat 1 0).Holds A (Fin.cases s e)) ↔ _
  simp only [indexNat_correct,Fin.cases_zero,not_exists]
  exact ⟨fun h => by by_contra! hh; exact h ⟨1,by omega⟩ rfl,
    fun h i he => by have := i.isLt; omega⟩

/-- Free slots select the dividend, positive divisor and candidate quotient, respectively. -/
noncomputable def formula : Form 3 :=
  .disj (.conj tiny (.input 0 0)) (.conj (.neg tiny) padded)

theorem formula_correct {U : ℕ} (A : Matrix U) (e : Fin 3→Fin U) :
    formula.Holds A e ↔ 0<rowWord (A (e 1)) ∧
      rowWord (A (e 2)) = rowWord (A (e 0)) / rowWord (A (e 1)) := by
  change (tiny.Holds A e ∧ A (e 0) (e 0)=true ∨ ¬tiny.Holds A e ∧ padded.Holds A e) ↔ _
  rw [tiny_spec]
  by_cases h : 2≤U
  · simpa [show ¬U≤1 by omega] using padded_spec h A e
  · have positive := (e 0).pos
    obtain rfl : U=1 := by omega
    have he (i : Fin 3) : e i = 0 := Subsingleton.elim _ _
    simp only [he,le_refl,true_and,not_true_eq_false,false_and,or_false]
    cases eq : A 0 0 <;> simp [rowWord,eq]

end DiophantineNP.HABDivisionGraph
