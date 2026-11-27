import DiophantineNP.HABTranslation
import DiophantineNP.WidthData
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # The final shift in HAB's conversion from residues to binary

Theorem 4.1 of Hesse, Allender and Barrington uses a list of disjoint
odd prime-products strictly larger than the integer being recovered.
Only oddness and the lower bound are needed in the rounding argument.
This module treats the arithmetic independently of how the residue
basis is extended or its subproducts are divided out. -/

namespace DiophantineNP.HABCRTShift

def halves (bs : List ℕ) : ℕ := (bs.map (fun a => (a+1)/2)).prod

def successors (bs : List ℕ) : ℕ := (bs.map (fun a => a+1)).prod

private theorem prod_pos {bs : List ℕ} (pos : ∀ a ∈ bs, 0<a) : 0 < bs.prod := by
  induction bs with
  | nil => simp
  | cons a bs ih =>
    exact Nat.mul_pos (pos a List.mem_cons_self) (ih (fun b hb => pos b (List.mem_cons_of_mem _ hb)))

theorem half_identity {bs : List ℕ} (odd : ∀ a ∈ bs, a%2=1) :
    2^bs.length * halves bs = successors bs := by
  induction bs with
  | nil => simp [halves,successors]
  | cons a bs ih =>
    have e : 2*((a+1)/2) = a+1 := by have := odd a List.mem_cons_self; omega
    have t := ih (fun b hb => odd b (List.mem_cons_of_mem _ hb))
    change 2^(bs.length+1) * (((a+1)/2)*halves bs) = (a+1)*successors bs
    calc 2^(bs.length+1) * (((a+1)/2)*halves bs)
           = (2*((a+1)/2)) * (2^bs.length*halves bs) := by rw [pow_succ]; ring
         _ = _ := by rw [e,t]

private theorem prod_le_successors (bs : List ℕ) : bs.prod ≤ successors bs := by
  induction bs with
  | nil => simp [successors]
  | cons a bs ih => exact Nat.mul_le_mul (Nat.le_succ _) ih

/-- This integral error estimate holds at all lengths; in particular it
does not need logarithms, a minimum basis size or an asymptotic side condition. -/
theorem enclosure {x : ℕ} {bs : List ℕ} (large : ∀ a ∈ bs, x<a) :
    (x+1)*successors bs ≤ (x+2^bs.length)*bs.prod := by
  induction bs with
  | nil => simp [successors]
  | cons a bs ih =>
    let d := 2^bs.length
    have h := ih (fun b hb => large b (List.mem_cons_of_mem _ hb))
    have ha := large a List.mem_cons_self
    have hd : 1≤d := Nat.one_le_two_pow
    have factor : x+d ≤ d*a := calc
      x+d ≤ d*x+d := Nat.add_le_add_right (by simpa using Nat.mul_le_mul_right x hd) d
      _ = d*(x+1) := by ring
      _ ≤ d*a := Nat.mul_le_mul_left _ ha
    change (x+1)*((a+1)*successors bs) ≤ (x+2^(bs.length+1))*(a*bs.prod)
    calc (x+1)*((a+1)*successors bs) = (a+1)*((x+1)*successors bs) := by ring
         _ ≤ (a+1)*((x+d)*bs.prod) := Nat.mul_le_mul_left _ h
         _ = ((x+d)*a+(x+d))*bs.prod := by ring
         _ ≤ ((x+d)*a+d*a)*bs.prod := Nat.mul_le_mul_right _ (Nat.add_le_add_left factor _)
         _ = (x+2^(bs.length+1))*(a*bs.prod) := by dsimp [d]; rw [pow_succ]; ring

def estimate (x : ℕ) (bs : List ℕ) : ℕ := x*halves bs / bs.prod

theorem estimate_bounds {x : ℕ} {bs : List ℕ} (large : ∀ a ∈ bs, x<a)
    (odd : ∀ a ∈ bs, a%2=1) :
    x / 2^bs.length ≤ estimate x bs ∧ estimate x bs ≤ x / 2^bs.length + 1 := by
  let b := bs.prod
  let d := 2^bs.length
  let q := x / d
  have hb : 0<b := prod_pos (fun a h => (Nat.zero_le x).trans_lt (large a h))
  have hd : 0<d := Nat.two_pow_pos _
  have hqlo : q*d ≤ x := Nat.div_mul_le_self .. 
  have hqhi : x < (q+1)*d := by simpa [Nat.mul_comm (q+1) d] using Nat.lt_mul_div_succ x hd
  have he : d*halves bs = successors bs := half_identity odd
  have hs : 0 < successors bs := hb.trans_le (prod_le_successors bs)
  have error : x*successors bs < (x+d)*b := by
    exact (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hs).trans_le (enclosure large)
  constructor
  · apply (Nat.le_div_iff_mul_le hb).mpr
    apply Nat.le_of_mul_le_mul_right (c := d) _ hd
    calc q*b*d = (q*d)*b := by ring
         _ ≤ x*b := Nat.mul_le_mul_right _ hqlo
         _ ≤ x*successors bs := Nat.mul_le_mul_left _ (prod_le_successors bs)
         _ = x*halves bs*d := by rw [←he]; ring
  · apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    apply Nat.lt_of_mul_lt_mul_right (a:=d)
    calc x*halves bs*d = x*successors bs := by rw [←he]; ring
         _ < (x+d)*b := error
         _ ≤ ((q+1)*d+d)*b := Nat.mul_le_mul_right _ (Nat.add_le_add_right hqhi.le _)
         _ = (q+1+1)*b*d := by ring

/-- The correction can be selected using a comparison in CRT representation. -/
def quotient (x : ℕ) (bs : List ℕ) : ℕ :=
  let q := estimate x bs
  if q*2^bs.length ≤ x then q else q-1

theorem quotient_spec {x : ℕ} {bs : List ℕ} (large : ∀ a ∈ bs, x<a)
    (odd : ∀ a ∈ bs, a%2=1) : quotient x bs = x/2^bs.length := by
  obtain ⟨lo,hi⟩ := estimate_bounds large odd
  simp only [quotient]
  split <;> rename_i h
  · exact Nat.le_antisymm ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr h) lo
  · have hn : ¬ estimate x bs ≤ x/2^bs.length :=
      fun hle => h ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mp hle)
    rw [Nat.le_antisymm hi (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)), Nat.add_sub_cancel]

theorem bit_spec {x : ℕ} {bs : List ℕ} (large : ∀ a ∈ bs, x<a)
    (odd : ∀ a ∈ bs, a%2=1) :
    (quotient x bs).testBit 0 = x.testBit bs.length := by
  rw [quotient_spec large odd,Nat.testBit_div_two_pow,Nat.zero_add]

/-- Consecutive blocks of k distinct odd primes. Block zero gives the
original CRT modulus and each later block supplies an odd auxiliary factor. -/
noncomputable def primeAt (i : ℕ) : ℕ := Nat.nth Nat.Prime (i+1)
noncomputable def block (k t : ℕ) : ℕ := ∏ j ∈ Finset.range k, primeAt (t*k+j)
noncomputable def blocks (k s : ℕ) : List ℕ := (List.range s).map (fun t => block k (t+1))

private theorem at_odd (i : ℕ) : primeAt i % 2 = 1 := by
  have h := Nat.add_two_le_nth_prime (i+1)
  exact Nat.odd_iff.mp ((Nat.prime_nth_prime (i+1)).odd_of_ne_two (by omega))

theorem block_odd (k t : ℕ) : block k t % 2 = 1 := by
  let f := fun j => primeAt (t*k+j)
  change (∏ j ∈ Finset.range k, f j) % 2 = 1
  suffices ∀ s : Finset ℕ, (∏ j ∈ s,f j) % 2 = 1 from this _
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj,Nat.mul_mod,ih,show f j % 2=1 from at_odd _,Nat.mul_one]

theorem block_lower (k t : ℕ) : 2^k ≤ block k t := by
  simpa [block] using (Finset.prod_le_prod' (s:=Finset.range k) (f:=fun _ => 2)
    (g:=fun j => primeAt (t*k+j)) (fun j _ => (Nat.prime_nth_prime (t*k+j+1)).two_le))

theorem block_mono (k : ℕ) : Monotone (block k) := by
  intro i j hij
  apply Finset.prod_le_prod'
  intro a _
  apply Nat.nth_monotone Nat.infinite_setOf_prime
  have := Nat.mul_le_mul_right k hij
  omega

theorem blocks_coprime {k i j : ℕ} (hne : i≠j) : (block k i).Coprime (block k j) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro a ha
  apply Nat.coprime_prod_right_iff.mpr
  intro b hb
  apply (Nat.coprime_primes (Nat.prime_nth_prime _) (Nat.prime_nth_prime _)).mpr
  intro e
  have e' := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective e
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  rcases lt_or_gt_of_ne hne with h|h
  · have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this; omega
  · have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this; omega

/-- Explicit polynomial bound on every prime used by the base and the
first s auxiliary blocks. The proof uses the project's elementary bound
on the n-th prime. -/
theorem prime_bound {k s t j : ℕ} (ht : t≤s) (hj : j<k) :
    primeAt (t*k+j) < 32*((s+1)*k+2)^2 := by
  apply WidthData.oddPrime_lt_search_limit
  rw [Nat.succ_mul]; have := Nat.mul_le_mul_right k ht; omega

theorem prime_blocks_bit {x k : ℕ} (hx : x<block k 0) (s : ℕ) :
    (quotient x (blocks k s)).testBit 0 = x.testBit s := by
  have hs : (blocks k s).length = s := by simp [blocks]
  rw [← hs,← bit_spec (bs:=blocks k s)]
  · rw [hs]
  · intro a ha
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp ha
    exact hx.trans_le (block_mono k (Nat.zero_le _))
  · intro a ha
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp ha
    exact block_odd .. 

/-- The exact product bit from the source-level HAB predicate, specialized to
concrete disjoint prime blocks. The identity gives the numerical readout that the
finite-logic construction implements. -/
theorem matrix_product_bit {U : ℕ} (A : HAB.Matrix U) (hi lo : Fin U) :
    let x := ∏ r : Fin U, HAB.rowWord (A r)
    let s := hi.val*U+lo.val
    (quotient x (blocks (U*U+1) s)).testBit 0 = x.testBit s := by
  apply prime_blocks_bit
  calc (∏ r : Fin U, HAB.rowWord (A r)) ≤ ∏ _r : Fin U, 2^U :=
          Finset.prod_le_prod' (fun i _ => (HAB.rowWord_bound (A i)).le)
       _ = 2^(U*U) := by simp [pow_mul]
       _ < 2^(U*U+1) := Nat.pow_lt_pow_right (by decide) (by omega)
       _ ≤ _ := block_lower ..

end DiophantineNP.HABCRTShift
