import DiophantineNP.WidthFormulaProduct

/-! Conditional construction of the two formulas in Lemma 2.2.
The single hypothesis is `Arithmetic`, the finite-arithmetic syntax
transformers and native BIT predicate. All intermediate bit words, shifts,
the skipped-factor product, and padding are verified in this file and its imports. -/
namespace DiophantineNP.WidthFormula
open Counting PrimeFormula WidthData Packing

private noncomputable def coeff (n i : ℕ) := widthFactor n i / 2^(n+2-i)

private theorem coeff_identity {n i : ℕ} (hi : i<n) :
    widthFactor n i * 2^i / scale n = coeff n i := by
  have he : n+2 = i+(n+2-i) := by omega
  unfold scale coeff
  conv_lhs => rw [he, pow_add, Nat.mul_comm (widthFactor n i) (2^i), Nat.mul_div_mul_left _ _ (Nat.two_pow_pos i)]

/-- A shifted bit position is computed in the universe with three additions.
If the shifted index is unavailable, the formula returns false. -/
def coeffBit (A : ProductArithmetic) {k : ℕ} (j i x : Fin k) : Formula k :=
  .ex (.ex (.ex (.ex (andF (isNat 2 (up3 (0:Fin (k+1))))
    (andF (addF (up4 x) (up3 (0:Fin (k+1))) (up2 (0:Fin (k+2))))
    (andF (addF (up4 i) (0:Fin (k+3)).succ (up2 (0:Fin (k+2))))
    (andF (addF (up4 j) (0:Fin (k+3)).succ 0) (factorBit A 0 (up4 i) (up4 x)))))))))

theorem coeffBit_spec (A : ProductArithmetic) {k n : ℕ} (j i x : Fin k)
    (env : Fin k → Fin (universeSize n)) (hx : (env x).val=n) (hi : (env i).val<n) :
    (coeffBit A j i x).eval env = (coeff n (env i).val).testBit (env j).val := by
  let U := universeSize n
  let r := n+2-(env i).val
  let h := (env j).val+r
  have hd : widthFactor n (env i).val < 2^U := (factor_le hi).trans_lt (widthD_fits n)
  have h2 : n+2 < U := by have := exponent_fits n; dsimp [U]; omega
  apply Bool.eq_iff_iff.mpr
  simp only [coeffBit, exists_true, andF_spec, isNat_spec, addF_spec,
    up2, up3, up4, Fin.cases_zero, Fin.cases_succ, hx]
  rw [coeff, Nat.testBit_div_two_pow]
  constructor
  · rintro ⟨two,cap,gap,pos,hTwo,hCap,hGap,hPos,hBit⟩
    rw [factorBit_spec (n := n) A 0 (up4 i) (up4 x) (extend pos gap (extend cap two env)) hx hi] at hBit
    change (widthFactor n (env i).val).testBit pos.val = true at hBit
    have eqPos : (env j).val+(n+2-(env i).val) = pos.val := by omega
    rwa [eqPos]
  · intro bit
    have hp : h < U := by
      have he := Nat.ge_two_pow_of_testBit bit
      change 2^h ≤ widthFactor n (env i).val at he
      exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (he.trans_lt hd)
    let two : Fin U := ⟨2,by omega⟩
    let cap : Fin U := ⟨n+2,h2⟩
    let gap : Fin U := ⟨r,by dsimp [r]; omega⟩
    let pos : Fin U := ⟨h,hp⟩
    refine ⟨two,cap,gap,pos,rfl,rfl,?_,rfl,?_⟩
    · dsimp [cap,gap,r]; omega
    · rw [factorBit_spec (n := n) A 0 (up4 i) (up4 x) (extend pos gap (extend cap two env)) hx hi]
      exact bit

/-- Compute a two-word product by feeding its factors to slots zero and one. -/
def termBit (A : ProductArithmetic) {k : ℕ} (j i x : Fin k) : Formula k :=
  A.product j (branch (atLeast 2 (0:Fin (k+1)).succ) (oneBit 0)
    (branch (isNat 0 (0:Fin (k+1)).succ) (coeffBit A 0 (up2 i) (up2 x))
      (productBit A 0 (up2 x) (some (up2 i)))))

noncomputable def term (n i : ℕ) := coeff n i * (widthD n / widthFactor n i)

private theorem term_le {n i : ℕ} (hi : i<n) : term n i ≤ widthD n := by
  have h := (frame n (by omega)).factor hi
  exact (Nat.mul_le_mul_right _ (Nat.div_le_self (widthFactor n i) _)).trans_eq h

theorem termBit_spec (A : ProductArithmetic) {k n : ℕ} (j i x : Fin k)
    (env : Fin k → Fin (universeSize n)) (hx : (env x).val=n) (hi : (env i).val<n) :
    (termBit A j i x).eval env = (term n (env i).val).testBit (env j).val := by
  let c := coeff n (env i).val
  let q := widthD n / widthFactor n (env i).val
  let g := fun t : ℕ => if t=0 then c else q
  let f := fun t : ℕ => if t<2 then g t else 1
  have hU := exponent_fits n
  have hc : c < 2^(universeSize n) := (Nat.div_le_self _ _).trans_lt ((factor_le hi).trans_lt (widthD_fits n))
  have hq : q < 2^(universeSize n) := (Nat.div_le_self _ _).trans_lt (widthD_fits n)
  have ho : 1 < 2^(universeSize n) := Nat.one_lt_two_pow (by omega)
  have fits (t : ℕ) (_ : t<universeSize n) : f t < 2^(universeSize n) := by
    dsimp [f,g]; split
    · split <;> assumption
    · exact ho
  unfold termBit
  apply Eq.trans (A.product_spec _ _ env f fits ?_)
  · rw [show productPrefix f (universeSize n) = productPrefix g 2 from product_pad g (by omega)]
    have htwo : productPrefix g 2 = (1*c)*q := by
      rw [product_succ, product_succ]
      rfl
    rw [htwo, one_mul]
    rfl
  · intro b t
    rw [branch_eval]
    simp only [atLeast_true, oneBit_spec, extend, Fin.cases_succ, Fin.cases_zero]
    by_cases h : 2 ≤ t.val
    · rw [if_pos h, show f t.val = 1 from if_neg (Nat.not_lt.mpr h)]
    · rw [if_neg h, branch_eval]
      simp only [isNat_spec, extend, Fin.cases_succ, Fin.cases_zero]
      rw [coeffBit_spec A 0 (up2 i) (up2 x) (extend b t env) hx hi, complement_spec A 0 (up2 x) (up2 i) (extend b t env) hx hi]
      change (if t.val=0 then c.testBit b.val else q.testBit b.val) = _
      rw [show f t.val = g t.val from if_pos (Nat.lt_of_not_ge h)]
      dsimp only [g]
      split <;> rfl

/-- Bit query for a padded row of the sum defining the CRT multiplier. -/
def JRow (A : ProductArithmetic) {k : ℕ} (x : Fin k) : Formula (k+2) :=
  branch (ltF (0:Fin (k+1)).succ (up2 x)) (termBit A 0 (0:Fin (k+1)).succ (up2 x)) (zeroBit 0)

def JBit (A : Arithmetic) {k : ℕ} (j x : Fin k) : Formula k := A.sum j (JRow A x)

theorem sum_terms {n : ℕ} : Readout.prefixSum (term n) n = widthJ n := by
  have gen {s : ℕ} (hs : s ≤ n) :
      Readout.prefixSum (term n) s = Readout.prefixSum
        (Readout.weight (widthFactor n) (fun i => widthD n / widthFactor n i) (scale n)) s := by
    induction s with
    | zero => rfl
    | succ s ih => simp [Readout.prefixSum, ih (by omega), term, Readout.weight, coeff_identity (by omega : s<n)]
  exact gen le_rfl

noncomputable def paddedJRow (n t : ℕ) : ℕ := if t<n then term n t else 0

theorem JRow_spec (A : ProductArithmetic) {k n : ℕ} (x : Fin k)
    (env : Fin k → Fin (universeSize n)) (hx : (env x).val=n) :
    ∀ b t : Fin (universeSize n), (JRow A x).eval (extend b t env) =
      (paddedJRow n t.val).testBit b.val := by
  unfold JRow
  intro b t
  rw [branch_eval]
  simp only [ltF_true, extend, up2, Fin.cases_zero, Fin.cases_succ, hx]
  by_cases ht : t.val<n
  · rw [if_pos ht, termBit_spec A 0 (0:Fin (k+1)).succ (up2 x) (extend b t env) hx ht]
    rw [paddedJRow, if_pos ht]; rfl
  · rw [if_neg ht, zeroBit_spec]
    rw [paddedJRow, if_neg ht]; rfl


theorem paddedJ_sum (n : ℕ) : Readout.prefixSum (paddedJRow n) (universeSize n) = widthJ n :=
  (sum_pad (term n) (width_parameter_fits n).le).trans sum_terms

theorem JBit_spec (A : Arithmetic) {k n : ℕ} (j x : Fin k)
    (env : Fin k → Fin (universeSize n)) (hx : (env x).val=n) :
    (JBit A j x).eval env = (widthJ n).testBit (env j).val := by
  let f := fun t : ℕ => if t<n then term n t else 0
  have fits (t : ℕ) (_ : t<universeSize n) : f t < 2^(universeSize n) := by
    dsimp [f]; split
    · next h => exact (term_le h).trans_lt (widthD_fits n)
    · exact Nat.two_pow_pos _
  exact (A.sum_spec j (JRow A x) env f fits (JRow_spec A x env hx)).trans
    (congrArg (fun v : ℕ => v.testBit (env j).val) (paddedJ_sum n))

/-- Lemma 2.2 as an actual construction from its two published finite-arithmetic inputs. -/
theorem widthDescriptions (A : Arithmetic) : Packing.WidthDescriptions := by
  constructor
  · refine ⟨productBit A 0 1 none, ?_⟩
    intro n _ j
    exact fullProduct_spec A 0 1 (Fin.cases j (widthParam n)) rfl
  · refine ⟨JBit A 0 1, ?_⟩
    intro n _ j
    exact JBit_spec A 0 1 (Fin.cases j (widthParam n)) rfl

end DiophantineNP.WidthFormula
