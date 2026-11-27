import DiophantineNP.HABPrimeBlocks
import DiophantineNP.HABCRTRecovery
import DiophantineNP.HABPolylogRange

/-! # Capacity of the rescaling and correction in the HAB binary readout

The uncorrected shift Q can overshoot by one. For the actual U-by-U input,
the modulus of the first U²+1 primes already contains both arguments of
the corrective comparison, even for the largest output position.
-/
namespace DiophantineNP.HABCRTSize
open Finset HABCRTShift HABPrimeBlocks HABCRTRecovery

private theorem positive_product {bs : List ℕ} (h : ∀ a∈bs, 0<a) : 0<bs.prod := by
  induction bs with
  | nil => simp
  | cons x xs ih =>
    exact Nat.mul_pos (h x List.mem_cons_self) (ih (fun a ha => h a (List.mem_cons_of_mem _ ha)))

theorem halves_le {bs : List ℕ} (h : ∀ a∈bs, 0<a) : halves bs≤bs.prod := by
  induction bs with
  | nil => simp [halves]
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    exact Nat.mul_le_mul (show (x+1)/2≤x by omega)
      (ih (fun a ha => h a (List.mem_cons_of_mem _ ha)))

/-- The numerator before exact division by the auxiliary product is
strictly inside the combined CRT interval. -/
theorem numerator_fits {M x : ℕ} {bs : List ℕ} (hx : x<M) (pos : ∀ a∈bs, 0<a) :
    x*halves bs < M*bs.prod :=
  (Nat.mul_le_mul_left _ (halves_le pos)).trans_lt
    (Nat.mul_lt_mul_of_pos_right hx (positive_product pos))

/-- A single extra bit of headroom suffices to compare x with Q·2^s after
the integer division. All inequalities are strict where CRT comparison needs them. -/
theorem comparison_fits {M x : ℕ} {bs : List ℕ} (large : ∀ a∈bs, x<a)
    (odd : ∀ a∈bs, a%2=1) (room : x+2^bs.length<M) :
    estimate x bs*2^bs.length<M := by
  obtain ⟨_,h⟩ := estimate_bounds large odd
  calc estimate x bs*2^bs.length ≤ (x/2^bs.length+1)*2^bs.length := Nat.mul_le_mul_right _ h
       _ = x/2^bs.length*2^bs.length+2^bs.length := Nat.succ_mul ..
       _ ≤ x+2^bs.length := Nat.add_le_add_right (Nat.div_mul_le_self ..) _
       _ < M := room

/-- Any w-bit upper bound and an index below w give a first CRT block with
enough headroom. This also applies when w is only polylogarithmic in U. -/
theorem block_ranges {x w s : ℕ} (hprod : x≤2^w) (hs : s<w) :
    let k := w+1
    let bs := blocks k s
    let M := block k 0
    x<M ∧ x*halves bs<M*bs.prod ∧ estimate x bs*2^s<M := by
  let k := w+1
  let bs := blocks k s
  have length : bs.length=s := by simp [bs,blocks]
  have room : x+2^s<block k 0 := calc
    x+2^s < 2^w+2^w := Nat.add_lt_add_of_le_of_lt hprod (Nat.pow_lt_pow_right (by decide) hs)
    _ = 2^k := by dsimp [k];rw [pow_succ,Nat.mul_two]
    _ ≤ _ := block_lower ..
  have hx : x<block k 0 := (Nat.le_add_right ..).trans_lt room
  have hg (a : ℕ) (ha : a∈bs) : x<a := by
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp ha
    exact hx.trans_le (block_mono k (Nat.zero_le _))
  have ho (a : ℕ) (ha : a∈bs) : a%2=1 := by
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp ha
    exact block_odd ..
  refine ⟨hx,numerator_fits hx (fun a ha => (Nat.zero_le _).trans_lt (hg a ha)),?_⟩
  simpa only [length] using comparison_fits hg ho (by simpa only [length] using room)

/-- Both large encoded integers needed in the final shift fit their respective
bases. In particular the residue test for Q·2^s>X uses just the original block. -/
theorem matrix_ranges {U : ℕ} (A : HAB.Matrix U) (hi lo : Fin U) :
    let x := ∏ r : Fin U,HAB.rowWord (A r)
    let s := hi.val*U+lo.val
    let k := U*U+1
    let bs := blocks k s
    let M := block k 0
    x < M ∧ x*halves bs < M*bs.prod ∧ estimate x bs*2^s < M := by
  apply block_ranges
  · calc (∏ r : Fin U,HAB.rowWord (A r)) ≤ ∏ _r : Fin U, 2^U :=
          Finset.prod_le_prod' (fun i _ => (HAB.rowWord_bound (A i)).le)
         _ = _ := by simp [pow_mul]
  · calc hi.val*U+lo.val < hi.val*U+U := Nat.add_lt_add_left lo.isLt _
         _ = (hi.val+1)*U := (Nat.succ_mul ..).symm
         _ ≤ U*U := Nat.mul_le_mul_right _ hi.isLt

/-- One precision exponent for every sub-basis of at most N primes, even
after insertion of the additional prime used by a basis extension. -/
theorem precision_with_insert {s : Finset ℕ} {q K N : ℕ} (hs : s.card≤N)
    (small : ∀ p∈insert q s, p≤2^K) :
    modulus (insert q s)*budget (insert q s) < 2^((K+1)*(N+2)) := by
  have card : (insert q s).card≤N+1 := (card_insert_le ..).trans (by omega)
  have h := Nat.mul_le_mul_left K card
  apply (precision small).trans_le (Nat.pow_le_pow_right (by decide) ?_)
  nlinarith

/-- The maximum ambient index is an adequate precision exponent for every
set of supported primes, including sub-bases extended by an additional prime. -/
theorem precision_max {s : Finset ℕ} {U K : ℕ} (hK : 2≤K)
    (cap : 2^((K+1)*K)<U) (small : ∀ p∈s, p≤2^K) :
    modulus s*budget s<2^(U-1) := by
  have subset : s ⊆ range (2^K+1) := fun p hp => mem_range.mpr (Nat.lt_succ_of_le (small p hp))
  have card : s.card≤2^K+1 := (card_le_card subset).trans_eq (card_range _)
  have hpow : 2≤2^K := Nat.one_lt_two_pow (by omega)
  have smallExp : K*s.card+K+s.card+1≤2^((K+1)*K) := calc
    _ = (K+1)*(s.card+1) := by ring
    _ ≤ 2^K*(2^K*2) := Nat.mul_le_mul Nat.lt_two_pow_self (by omega)
    _ = 2^(K+(K+1)) := by rw [pow_add,pow_succ]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith [Nat.mul_self_le_mul_self hK])
  exact (precision small).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

/-- A common width and the concrete precision U−1 work for the original
block, every auxiliary block, their unions, and the extra parity prime 2.
The exponent d bounds both the block length k and the shift position s. -/
theorem polylog_budgets {U d k s : ℕ} (hU : HABPolylogRange.threshold (4*d+9)≤U)
    (hk : k≤U.log2^d) (hs : s≤U.log2^d) :
    let K := HABPolylogRange.tableBits (4*d+9) U
    2≤K ∧ 2^((K+1)*K)<U ∧
    ∀ T : Finset ℕ, (∀ p∈T, p=2 ∨ ∃ t≤s, p∈primeSet k t) →
      (∀ p∈T, p≤2^K) ∧ modulus T*budget T<2^(U-1) := by
  let K := HABPolylogRange.tableBits (4*d+9) U
  obtain ⟨hK,_,cap⟩ := HABPolylogRange.range_covered (p:=0) hU (Nat.zero_le _)
  refine ⟨hK,cap,?_⟩
  intro T members
  have small (p : ℕ) (hp : p∈T) : p≤2^K := by
    obtain rfl|⟨t,ht,hm⟩ := members p hp
    · exact Nat.one_lt_two_pow (by change 2≤K at hK; omega)
    · obtain ⟨j,hj,rfl⟩ := mem_primeSet.mp hm
      exact (HABPolylogRange.block_covered hU hk hs ht hj).2.1
  exact ⟨small,precision_max hK cap small⟩

end DiophantineNP.HABCRTSize
