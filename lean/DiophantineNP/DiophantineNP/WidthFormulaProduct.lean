import DiophantineNP.WidthFormulaTools

namespace DiophantineNP.WidthFormula
open Counting PrimeFormula WidthData

theorem search_limit_fits (n : ℕ) : 32*(n+2)^2 < universeSize n := by
  have hx : 2 ≤ n+2 := by omega
  have h : 32 < (n+2)^6 := lt_of_lt_of_le (by decide : 32 < 2^6) (Nat.pow_le_pow_left hx _)
  have hs := Nat.mul_lt_mul_of_pos_right h (show 0 < (n+2)^2 by positivity)
  rw [← pow_add] at hs
  exact hs.trans_le (Nat.pow_le_pow_right (by omega) (by decide))

private theorem one_fits (n : ℕ) : 1 < 2^(universeSize n) :=
  Nat.one_lt_two_pow (by have := exponent_fits n; omega)

theorem factor_le {n i : ℕ} (hi : i<n) : widthFactor n i ≤ widthD n := by
  have h := (frame n (by omega)).D_pos
  exact Nat.le_of_dvd h (List.dvd_prod (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))

/-- Look up the numerical prime, then query its bit in the finite structure. -/
def primeBit (A : ProductArithmetic) {k : ℕ} (j i : Fin k) : Formula k :=
  .ex (andF (oddPrimeAtVars 0 i.succ) (A.bit 0 j.succ))

theorem primeBit_spec (A : ProductArithmetic) {k n : ℕ} (j i : Fin k)
    (env : Fin k → Fin (universeSize n)) (hi : (env i).val<n) :
    (primeBit A j i).eval env = (Nat.nth Nat.Prime ((env i).val+1)).testBit (env j).val := by
  apply Bool.eq_iff_iff.mpr
  rw [primeBit, exists_true]
  simp only [andF_spec, A.bit_spec, Fin.cases_zero, Fin.cases_succ]
  have ht (p : Fin (universeSize n)) :
      (oddPrimeAtVars 0 i.succ).eval (Fin.cases p env) = true ↔ p.val = Nat.nth Nat.Prime ((env i).val+1) := by
    let e : Fin (k+1) → Fin (universeSize n) := Fin.cases p env
    have hi' : (e i.succ).val<n := by change (env i).val<n; exact hi
    exact width_prime_vars (k := k+1) (n := n) (0:Fin (k+1)) i.succ e hi' 
  simp_rw [ht]
  constructor
  · rintro ⟨p,hp,h⟩; rw [← hp]; exact h
  · intro h
    exact ⟨⟨_, (oddPrime_lt_search_limit hi).trans (search_limit_fits n)⟩,rfl,h⟩

/-- Padded iterated product giving the bit of the i-th prime power. -/
def factorBit (A : ProductArithmetic) {k : ℕ} (j i n : Fin k) : Formula k :=
  A.product j (branch (belowExp (0:Fin (k+1)).succ (up2 n))
    (primeBit A 0 (up2 i)) (oneBit 0))

theorem factorBit_spec (A : ProductArithmetic) {k n : ℕ} (j i x : Fin k)
    (env : Fin k → Fin (universeSize n)) (hx : (env x).val=n) (hi : (env i).val<n) :
    (factorBit A j i x).eval env = (widthFactor n (env i).val).testBit (env j).val := by
  let p := Nat.nth Nat.Prime ((env i).val+1)
  let f := fun t : ℕ => if t<4*n+10 then p else 1
  have hp : p < 2^(universeSize n) :=
    (oddPrime_lt_search_limit hi).trans ((search_limit_fits n).trans Nat.lt_two_pow_self)
  have fits (t : ℕ) (_ : t<universeSize n) : f t < 2^(universeSize n) := by
    dsimp [f]; split <;> first | exact hp | exact one_fits n
  have correct (b t : Fin (universeSize n)) :
      (branch (belowExp (0:Fin (k+1)).succ (up2 x)) (primeBit A 0 (up2 i)) (oneBit 0)).eval
      (extend b t env) = (f t.val).testBit b.val := by
    rw [branch_eval]
    simp only [belowExp_spec _ _ _ (show ((extend b t env) (up2 x)).val=n from hx),
      primeBit_spec _ _ _ _ (show ((extend b t env) (up2 i)).val<n from hi), oneBit_spec,
      extend, up2, Fin.cases_zero, Fin.cases_succ, f, p]
    split <;> rfl
  unfold factorBit
  rw [A.product_spec _ _ env f fits correct]
  rw [show productPrefix f (universeSize n) = p^(4*n+10) by
    exact (product_pad (fun _ => p) (exponent_fits n).le).trans (product_constant p _)]
  rfl

private def skip {k : ℕ} (s : Option (Fin k)) (slot : Fin (k+2)) : Formula (k+2) :=
  match s with
  | none => zeroBit slot
  | some i => eqF slot (up2 i)

private def skipValue {k U : ℕ} (s : Option (Fin k)) (env : Fin k → Fin U) (t : ℕ) : Bool :=
  match s with
  | none => false
  | some i => decide (t = (env i).val)

private theorem skip_spec {k U : ℕ} (s : Option (Fin k)) (env : Fin k → Fin U) (b t : Fin U) :
    (skip s (0:Fin (k+1)).succ).eval (extend b t env) = skipValue s env t.val := by
  cases s <;> apply Bool.eq_iff_iff.mpr
  · simp [skip, skipValue, zeroBit_spec]
  · simp only [skip, skipValue, eqF_spec, extend, up2, Fin.cases_succ, Fin.cases_zero, decide_eq_true_eq]

/-- Optional omission supplies the complementary product D/dᵢ without division. -/
def productBit (A : ProductArithmetic) {k : ℕ} (j n : Fin k) (excluded : Option (Fin k)) : Formula k :=
  A.product j (branch (ltF (0:Fin (k+1)).succ (up2 n))
    (branch (skip excluded (0:Fin (k+1)).succ) (oneBit 0)
      (factorBit A 0 (0:Fin (k+1)).succ (up2 n))) (oneBit 0))

private theorem productBit_general (A : ProductArithmetic) {k n : ℕ} (j x : Fin k) (excluded : Option (Fin k))
    (env : Fin k → Fin (universeSize n)) (hx : (env x).val=n) :
    (productBit A j x excluded).eval env = (productPrefix
      (fun t => if skipValue excluded env t then 1 else widthFactor n t) n).testBit (env j).val := by
  let g := fun t => if skipValue excluded env t then 1 else widthFactor n t
  let f := fun t => if t<n then g t else 1
  have fits (t : ℕ) (_ : t<universeSize n) : f t < 2^(universeSize n) := by
    dsimp [f,g]; split
    · next ht => split
                 · exact one_fits n
                 · exact (factor_le ht).trans_lt (widthD_fits n)
    · exact one_fits n
  unfold productBit
  apply Eq.trans (A.product_spec _ _ env f fits ?_)
  · rw [show productPrefix f (universeSize n) = productPrefix g n from
      product_pad g (width_parameter_fits n).le]
  · intro b t
    rw [branch_eval]
    simp only [ltF_true, extend, up2, Fin.cases_zero, Fin.cases_succ, hx]
    by_cases ht : t.val<n
    · rw [if_pos ht, branch_eval]
      rw [skip_spec, oneBit_spec, factorBit_spec A 0 (0:Fin (k+1)).succ (up2 x) (extend b t env) hx ht]
      change (if skipValue excluded env t.val then (1:ℕ).testBit b.val else
        (widthFactor n t.val).testBit b.val) = (f t.val).testBit b.val
      rw [show f t.val=g t.val from if_pos ht]
      dsimp only [g]
      split <;> rfl
    · rw [if_neg ht, oneBit_spec]
      change (1:ℕ).testBit b.val = (f t.val).testBit b.val
      rw [show f t.val=1 from if_neg ht]

theorem fullProduct_spec (A : ProductArithmetic) {k n : ℕ} (j x : Fin k)
    (env : Fin k → Fin (universeSize n)) (hx : (env x).val=n) :
    (productBit A j x none).eval env = (widthD n).testBit (env j).val := by
  rw [productBit_general A j x none env hx]
  rfl

theorem complement_spec (A : ProductArithmetic) {k n : ℕ} (j x i : Fin k)
    (env : Fin k → Fin (universeSize n)) (hx : (env x).val=n) (hi : (env i).val<n) :
    (productBit A j x (some i)).eval env = (widthD n / widthFactor n (env i).val).testBit (env j).val := by
  rw [productBit_general A _ _ _ _ hx]
  congr 1
  simp only [skipValue, decide_eq_true_eq]
  have h := omitted_product hi (widthFactor n)
  have hp : 0 < widthFactor n (env i).val := by
    exact pow_pos (Nat.prime_nth_prime _).pos _
  change _ * widthFactor n (env i).val = widthD n at h
  rw [← h, Nat.mul_div_cancel _ hp]

end DiophantineNP.WidthFormula
