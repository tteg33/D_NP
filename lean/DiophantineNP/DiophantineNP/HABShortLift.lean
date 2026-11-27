import DiophantineNP.HABPowerReduction
import DiophantineNP.HABSpacePadding

/-! # Eliminating a fixed size threshold on short modular products

A fixed number of square interpretations supplies the threshold. The finite
matrix is zero-extended in both dimensions, so the indicated prefix of input
words retains its numerical values.
-/
namespace DiophantineNP.HABShortLift
open WidthFormula FiniteArithmeticGap HABGroupPower HABSpacePadding

/-- The short-product interface with an additional fixed lower bound on size. -/
structure LargeShortProducts (N : ℕ) where
  formula : Template 3
  correct {U : ℕ} (large : N≤U) (A : HAB.Matrix U) (len p b : Fin U) (f : ℕ→ℕ)
    (prime : p.val.Prime) (padding : (p.val+2)^30<U)
    (small : len.val≤(primeBound (p.val-1))^2+1)
    (values : ∀ i<len.val, f i<p.val)
    (bits : ∀ i j : Fin U, i.val<len.val → A i j=(f i.val).testBit j.val) :
    formula.eval A ![len,p,b]=true ↔ (∏ i ∈ Finset.range len.val,f i)%p.val=b.val

private def depth (N : ℕ) := Nat.clog 2 (Nat.clog 2 N)

private theorem meets {U : ℕ} (N : ℕ) (hU : 2≤U) : N≤size U (depth N) := by
  rw [size_eq]
  exact (Nat.le_pow_clog (by decide) N).trans ((Nat.pow_le_pow_right (by decide : 0<2)
    (Nat.le_pow_clog (by decide : 1<2) (Nat.clog 2 N))).trans (Nat.pow_le_pow_left hU _))

private theorem expanded_bits {U : ℕ} (d : ℕ) (A : HAB.Matrix U) (len p : Fin U) (f : ℕ→ℕ)
    (values : ∀ i<len.val, f i<p.val)
    (bits : ∀ i j : Fin U, i.val<len.val → A i j=(f i.val).testBit j.val)
    (i j : Fin (size U d)) (hi : i.val<len.val) : matrix A d i j = (f i.val).testBit j.val := by
  apply Bool.eq_iff_iff.mpr
  rw [matrix_true]
  constructor
  · rintro ⟨r,c,⟨hr,hc⟩,h⟩
    rw [bits r c (hr ▸ hi),hr,hc] at h;exact h
  · intro h
    by_cases hj : j.val<U
    · exact ⟨⟨_,hi.trans len.isLt⟩,⟨_,hj⟩,⟨rfl,rfl⟩,(bits _ _ hi).trans h⟩
    · have hf := (values _ hi).trans p.isLt
      have nbit := Nat.testBit_lt_two_pow (hf.trans_le ((Nat.lt_two_pow_self (n:=U)).le.trans
        (Nat.pow_le_pow_right (by decide) (by omega : U≤j.val))))
      rw [nbit] at h;contradiction

/-- Run the size-qualified syntax on an interpreted polynomial-size domain. -/
noncomputable def toShortProducts {N : ℕ} (large : LargeShortProducts N) : HABPowerReduction.ShortProducts where
  formula := pad (depth N) large.formula
  correct {U} A len p b f pr hp hs hv hb := by
    let d := depth N
    have hu := p.isLt
    have hU := pr.two_le.trans hu.le
    let e : Fin 3→Fin U := ![len,p,b]
    rw [pad_correct _ _ A e p.pos]
    have env : (fun j : Fin 3 => index (e j) d) = ![index len d,index p d,index b d] := by
      funext j;fin_cases j <;> rfl
    change large.formula.eval (matrix A d) (fun j => index (e j) d)=true ↔ _
    rw [env]
    have base : U≤size U d := by
      rw [size_eq]; simpa using (Nat.pow_le_pow_right (n:=U) (by omega : 0<U) (Nat.one_le_two_pow (n:=d)))
    simpa only [index_val] using large.correct (meets N hU) (matrix A d) (index len d) (index p d) (index b d) f
      (by simpa only [index_val] using pr) (by simpa only [index_val] using hp.trans_le base)
      (by simpa only [index_val] using hs) (by simpa only [index_val] using hv)
      (by simpa only [index_val] using expanded_bits d A len p f hv hb)

end DiophantineNP.HABShortLift
