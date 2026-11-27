import DiophantineNP.HABCRTDot

/-! Verify a proposed represented remainder from binary digits of a dividend
and of its floor quotient. -/
namespace DiophantineNP.HABRemainderCheck
open Counting WidthFormula FiniteArithmeticGap HAB HABCRTDot

private def idx {k : ℕ} (p : Fin k) : Template (k+1) := .bit p.succ 0

private noncomputable def combination {k : ℕ} (q : Template (k+1)) (p b : Fin k) : Template (k+1) :=
  rowAdd (rowMul q (idx p)) (idx b)

attribute [local irreducible] rowAdd rowMul wordLt

/-- A remainder is less than its positive divisor and satisfies Euclidean division. -/
noncomputable def formula {k : ℕ} (x q : Template (k+1)) (p b : Fin k) : Template k :=
  let total := combination q p b
  .conj (fromFormula (PrimeFormula.ltF b p))
    (.neg (.disj (wordLt x total) (wordLt total x)))

theorem formula_correct {k U : ℕ} (x q : Template (k+1)) (p b : Fin k)
    (A : Matrix U) (e : Fin k→Fin U) (X : ℕ) (hU : 2≤U) (hp : 0<(e p).val)
    (hX : X+(e p).val<2^U)
    (hxReads : ∀ i : Fin U, x.eval A (Fin.cases i e)=X.testBit i.val)
    (hqReads : ∀ i : Fin U, q.eval A (Fin.cases i e)=(X/(e p).val).testBit i.val) :
    (formula x q p b).eval A e=true ↔ X%(e p).val=(e b).val := by
  let Y := X/(e p).val*(e p).val+(e b).val
  have bit (i : Fin k) (j : Fin U) : (idx i).eval A (Fin.cases j e)=(e i).val.testBit j.val := rfl
  have prodBit (j : Fin U) : (rowMul q (idx p)).eval A (Fin.cases j e) =
      (X/(e p).val*(e p).val).testBit j.val := rowMul_correct q (idx p) A e hU hqReads (bit p) j
  have totalBit (j : Fin U) : (combination q p b).eval A (Fin.cases j e)=Y.testBit j.val :=
    rowAdd_correct _ (idx b) A e hU prodBit (bit b) j
  simp only [formula,Tconj_true,fromFormula_eval,PrimeFormula.ltF_true,Template.eval.eq_4,
    Bool.not_eq_true',←Bool.not_eq_true,Tdisj_true]
  by_cases hb : (e b).val<(e p).val
  · have hprod := Nat.div_mul_le_self X (e p).val
    have hd := Nat.div_add_mod X (e p).val
    rw [Nat.mul_comm (e p).val] at hd
    have hY : Y<2^U := by dsimp [Y]; omega
    rw [wordLt_correct _ _ A e hxReads totalBit (by omega) hY,
      wordLt_correct _ _ A e totalBit hxReads hY (by omega)]
    dsimp [Y]; omega
  · have small := Nat.mod_lt X hp
    simp only [hb,false_and,false_iff]; omega

end DiophantineNP.HABRemainderCheck
