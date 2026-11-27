import DiophantineNP.HABProductBlocks
import DiophantineNP.HABCRTShift

/-! # Polylogarithmic range of the packed modular powers

A fixed power of the logarithm of the universe is inside the range of the
repeated-squaring table, with an explicit threshold. Applied to the prime
blocks used in the Chinese remainder construction, this suffices to distinguish
all integers of polylogarithmic bit length. -/

namespace DiophantineNP.HABPolylogRange

def threshold (d : ℕ) := 2^(2^(8*(d+2)^2+10))

def tableBits (d U : ℕ) := (d+2)*(U.log2.log2+1)

private theorem cubic_le (j : ℕ) (hj : 10≤j) : j^3≤2^j := by
  induction j,hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    rw [pow_succ 2]
    have h1 := Nat.mul_le_mul_right (j^2) hj
    have h2 := Nat.le_mul_of_pos_right j (by omega : 0<j)
    nlinarith

private theorem threshold_log {U d : ℕ} (hU : threshold d≤U) :
    8*(d+2)^2+10≤U.log2.log2 ∧ 2≤U.log2 ∧ U≠0 := by
  have hu0 : U≠0 := (lt_of_lt_of_le (Nat.two_pow_pos _) hU).ne'
  have hg := (Nat.le_log2 hu0).mpr hU
  have hl0 : U.log2≠0 := (lt_of_lt_of_le (Nat.two_pow_pos _) hg).ne'
  have hj := (Nat.le_log2 hl0).mpr hg
  have hgt : 1<2^(8*(d+2)^2+10) := Nat.one_lt_two_pow (by omega)
  exact ⟨hj,hgt.trans_le hg,hu0⟩

/-- All values bounded by a fixed power of log₂ U fit one common table width. -/
theorem range_covered {U d p : ℕ} (hU : threshold d≤U) (hp : p≤U.log2^d) :
    let K := tableBits d U
    2≤K ∧ p≤2^K ∧ 2^((K+1)*K)<U := by
  obtain ⟨hj,hl,hu0⟩ := threshold_log hU
  let j := U.log2.log2
  let a := d+2
  change 8*a^2+10≤j at hj
  change 2≤a*(j+1) ∧ p≤2^(a*(j+1)) ∧ 2^((a*(j+1)+1)*(a*(j+1)))<U
  have ha : 2≤a := by dsimp [a]; omega
  have hmul := Nat.mul_le_mul_left a (by omega : 2≤j)
  have hK : a*(j+1)+1≤2*a*j := by nlinarith
  have hjpos : 0<j := by omega
  have hlt : (a*(j+1)+1)*(a*(j+1)) < j^3 := calc
    _ ≤ (2*a*j)*(2*a*j) := Nat.mul_le_mul hK (by omega)
    _ = (4*a^2)*j^2 := by ring
    _ < j*j^2 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    _ = j^3 := by ring
  have hc := (hlt.trans_le (cubic_le j (by omega))).trans_le (Nat.log2_self_le (by omega : U.log2≠0))
  refine ⟨by nlinarith,?_,(Nat.pow_lt_pow_right (by decide : 1<2) hc).trans_le (Nat.log2_self_le hu0)⟩
  calc
    p ≤ U.log2^d := hp
    _ ≤ (2^(j+1))^d := Nat.pow_le_pow_left Nat.lt_log2_self.le d
    _ = 2^(d*(j+1)) := by rw [Nat.mul_comm d, pow_mul]
    _ ≤ 2^(a*(j+1)) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by dsimp [a]; omega))

/-- The fixed raw-matrix product query works at every prime in the
polylogarithmic range, uniformly over the input and output residue. -/
theorem binaryProduct_polylog {U d k : ℕ} (p b : Fin k) (v : Fin k → Fin U)
    (A : HAB.Matrix U) (hU : threshold d ≤ U)
    (hp : (v p).val.Prime) (hbound : (v p).val≤U.log2^d) :
    (HABProductBlocks.binaryProduct p b).eval A v = true ↔
      (v b).val=(∏ r : Fin U, HAB.rowWord (A r))%(v p).val := by
  obtain ⟨hK,hpk,hcap⟩ := range_covered hU hbound
  exact HABProductBlocks.binaryProduct_spec p b v A hp hK hpk hcap

/-- Every prime in every required block is covered when both block width
and shift distance are polylogarithmic in U. -/
theorem block_covered {U d k s t j : ℕ} (hU : threshold (4*d+9)≤U)
    (hk : k≤U.log2^d) (hs : s≤U.log2^d) (ht : t≤s) (hj : j<k) :
    let K := tableBits (4*d+9) U
    2≤K ∧ HABCRTShift.primeAt (t*k+j)≤2^K ∧ 2^((K+1)*K)<U := by
  apply range_covered hU
  let L := U.log2
  let m := L^d
  have hL : 2≤L := (threshold_log hU).2.1
  have hm : 1≤m := Nat.one_le_pow _ _ (by omega : 0<L)
  have hs' : s+1≤m+1 := Nat.succ_le_succ hs
  have hi : (s+1)*k+2 ≤ 4*m^2 := by
    have h : (s+1)*k≤(m+1)*m := Nat.mul_le_mul hs' hk
    have hsq := Nat.mul_le_mul_left m hm
    nlinarith
  calc
    HABCRTShift.primeAt (t*k+j) ≤ 32*((s+1)*k+2)^2 := (HABCRTShift.prime_bound ht hj).le
    _ ≤ 32*(4*m^2)^2 := Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left hi 2)
    _ = 2^9*(L^d)^4 := by dsimp [m]; ring
    _ ≤ L^9*(L^d)^4 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hL 9)
    _ = L^(4*d+9) := by rw [Nat.add_comm, pow_add, Nat.mul_comm 4 d, pow_mul]

/-- Agreement on the first k odd primes distinguishes k-bit integers. -/
theorem first_block_unique {k x y : ℕ} (hx : x<2^k) (hy : y<2^k)
    (h : ∀ j<k, x % HABCRTShift.primeAt j = y % HABCRTShift.primeAt j) : x=y := by
  have agg (n : ℕ) (hn : n≤k) :
      x ≡ y [MOD ∏ j ∈ Finset.range n, HABCRTShift.primeAt j] := by
    induction n with
    | zero => simpa using Nat.modEq_one (a:=x) (b:=y)
    | succ n ih =>
      rw [Finset.prod_range_succ]
      apply (Nat.modEq_and_modEq_iff_modEq_mul ?_).mp ⟨ih (by omega),h n (by omega)⟩
      apply Nat.coprime_prod_left_iff.mpr
      intro j hj
      apply (Nat.coprime_primes (Nat.prime_nth_prime _) (Nat.prime_nth_prime _)).mpr
      intro e
      have := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective e
      have := Finset.mem_range.mp hj
      omega
  have hab := agg k le_rfl
  have hbig : 2^k ≤ ∏ j ∈ Finset.range k, HABCRTShift.primeAt j :=
    by simpa [HABCRTShift.block] using HABCRTShift.block_lower k 0
  exact hab.eq_of_lt_of_lt (hx.trans_le hbig) (hy.trans_le hbig)

end DiophantineNP.HABPolylogRange
