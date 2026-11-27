import DiophantineNP.HABTranslation

/-! Expand U rows of U bits to a square universe of U² rows of U² bits.
Zero extension preserves each original row and every added row represents the
multiplicative identity. -/
namespace DiophantineNP.HABProductPadding
open Counting WidthFormula FiniteArithmeticGap HAB

/-- The padded word at row r. -/
def factor {U : ℕ} (A : Matrix U) (r : ℕ) : ℕ :=
  if h : r<U then rowWord (A ⟨r,h⟩) else 1

theorem factor_fits {U : ℕ} (hU : 2≤U) (A : Matrix U) (r : ℕ) :
    factor A r < 2^(U*U) := by
  have h : U≤U*U := by nlinarith
  unfold factor
  split
  · exact (rowWord_bound _).trans_le (Nat.pow_le_pow_right (by decide) h)
  · exact Nat.one_lt_pow (by omega) (by decide)

theorem product_factor {U : ℕ} (hU : 2≤U) (A : Matrix U) :
    productPrefix (factor A) (U*U) = ∏ r : Fin U, rowWord (A r) := by
  have base (n : ℕ) (hn : n≤U) :
      productPrefix (factor A) n =
      ∏ r : Fin n, rowWord (A ⟨r.val,r.isLt.trans_le hn⟩) := by
    induction n with
    | zero => simp [productPrefix]
    | succ n ih =>
      rw [product_succ,Fin.prod_univ_castSucc,ih (by omega)]
      simp [factor,show n<U by omega]
  have stable (n : ℕ) (hn : U≤n) :
      productPrefix (factor A) n = productPrefix (factor A) U := by
    induction n,hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => simp [product_succ,ih,factor,hn.not_gt]
  exact (stable _ (by nlinarith)).trans (base U le_rfl)

private def zero {k : ℕ} (x : Fin k) : Template k := fromFormula (isNat 0 x)

/-- Digits of the virtual row and column are supplied in major/minor order. -/
def cell {k : ℕ} (rh rl ch cl : Fin k) : Template k :=
  .conj (zero ch)
    (.disj (.conj (zero rh) (.entry rl cl))
      (.conj (.neg (zero rh)) (zero cl)))

theorem cell_spec {k U : ℕ} (rh rl ch cl : Fin k) (A : Matrix U) (e : Fin k → Fin U) :
    (cell rh rl ch cl).eval A e = (factor A (finProdFinEquiv (e rh,e rl)).val).testBit
      (finProdFinEquiv (e ch,e cl)).val := by
  apply Bool.eq_iff_iff.mpr
  simp only [cell,Tconj_true,Tdisj_true,zero,fromFormula_eval,isNat_spec,
    Template.eval.eq_4,Bool.not_eq_true',← Bool.not_eq_true,Tentry_eval,finProdFinEquiv_apply_val]
  have gap (h l : Fin U) (hh : h.val ≠ 0) : U≤l.val+U*h.val := by
    have := Nat.mul_le_mul_left U (show 1≤h.val by omega)
    omega
  by_cases hr : (e rh).val=0
  · simp only [hr,Nat.mul_zero,Nat.add_zero,factor,dif_pos (e rl).isLt,
      true_and,not_true_eq_false,false_and,or_false]
    by_cases hc : (e ch).val=0
    · simp [hc,rowWord_bit]
    · have bound := (rowWord_bound (A (e rl))).trans_le
          (Nat.pow_le_pow_right (by decide) (gap (e ch) (e cl) hc))
      simp [hc,Nat.testBit_lt_two_pow bound]
  · have hgap := gap (e rh) (e rl) hr
    simp only [hr,false_and,not_false_eq_true,true_and,false_or,factor,dif_neg hgap.not_gt,
      Nat.testBit_one_eq_true_iff_self_eq_zero]
    have hu : 0<U := (e rh).pos
    simp [hu.ne',and_comm]

end DiophantineNP.HABProductPadding
