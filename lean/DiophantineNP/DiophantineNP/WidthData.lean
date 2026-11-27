import DiophantineNP.ReadoutBits
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-! The actual width words of §2, and explicit bounds on their prime search range. -/
namespace DiophantineNP.WidthData

noncomputable def widthFactor (n i : ℕ) : ℕ := (Nat.nth Nat.Prime (i+1))^(4*n+10)
noncomputable def widthD (n : ℕ) : ℕ := ((List.range n).map (widthFactor n)).prod
def scale (n : ℕ) := 2^(n+2)
noncomputable def widthJ (n : ℕ) : ℕ :=
  Readout.prefixSum (Readout.weight (widthFactor n) (fun i => widthD n / widthFactor n i)
    (scale n)) n
def universeSize (n : ℕ) : ℕ := (n+2)^20

private theorem two_pow_le_centralBinom (v : ℕ) : 2^v ≤ v.centralBinom := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ]
    refine (Nat.mul_le_mul_right 2 ih).trans ?_
    apply Nat.le_of_mul_le_mul_left (c := v+1) _ (by omega)
    calc
      (v+1) * (v.centralBinom * 2) ≤ 2 * (2*v+1) * v.centralBinom := by
        nlinarith [Nat.zero_le (v * v.centralBinom)]
      _ = _ := (Nat.succ_mul_centralBinom_succ v).symm

/-- Integral form of the binomial prime-count lower bound used in §2. -/
theorem prime_count_bound {v : ℕ} (hv : 0 < v) :
    2^v ≤ (2*v) ^ (2*v).primeCounting := by
  let primes := (Finset.range (2*v+1)).filter Nat.Prime
  let f := fun p => p ^ v.centralBinom.factorization p
  have heq : ∏ p ∈ primes, f p = ∏ p ∈ Finset.range (2*v+1), f p := by
    apply Finset.prod_filter_of_ne
    intro p _ hn
    contrapose! hn
    simp [f, Nat.factorization_eq_zero_of_non_prime _ hn]
  have hcard : primes.card = (2*v).primeCounting := by
    exact (Nat.count_eq_card_filter_range Nat.Prime _).symm
  calc
    2^v ≤ v.centralBinom := two_pow_le_centralBinom v
    _ = ∏ p ∈ primes, f p := by
      rw [heq]; exact (Nat.prod_pow_factorization_centralBinom v).symm
    _ ≤ ∏ _p ∈ primes, (2*v) :=
      Finset.prod_le_prod' (fun _ _ => Nat.pow_factorization_choose_le (by omega : 0 < 2*v))
    _ = _ := by rw [Finset.prod_const, hcard]

private theorem search_cap {x : ℕ} (hx : 2 ≤ x) : 32*x^2 ≤ 2^(4*x) := by
  induction x, hx using Nat.le_induction with
  | base => decide
  | succ x hx ih =>
    rw [show 4*(x+1) = 4*x+4 by omega, pow_add]
    calc
      32*(x+1)^2 ≤ 32*x^2 * 2^4 := by nlinarith [Nat.mul_self_le_mul_self hx]
      _ ≤ _ := Nat.mul_le_mul_right _ ih

/-- The (i+1)-st zero-indexed prime lies within the finite search universe. -/
theorem oddPrime_lt_search_limit {n i : ℕ} (hi : i < n) :
    Nat.nth Nat.Prime (i+1) < 32*(n+2)^2 := by
  let x := n+2
  let v := 16*x^2
  let K := 2*v
  have hx : 2 ≤ x := by dsimp [x]; omega
  have hv : 0 < v := by dsimp [v]; positivity
  have hk : K = 32*x^2 := by dsimp [K, v]; ring
  have hpow : 2^v ≤ 2^(4*x*K.primeCounting) := calc
    2^v ≤ K^K.primeCounting := prime_count_bound hv
    _ ≤ (2^(4*x))^K.primeCounting :=
      Nat.pow_le_pow_left (hk ▸ search_cap hx) _
    _ = _ := (pow_mul _ _ _).symm
  have hexp : v ≤ 4*x*K.primeCounting := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  have hnum : i+1 < K.primeCounting := by
    by_contra! hc
    have hle := Nat.mul_le_mul_left (4*x) hc
    have hi' : i+1 ≤ x := by dsimp [x]; omega
    have hle' := Nat.mul_le_mul_left (4*x) hi'
    dsimp [v] at hexp
    nlinarith
  have hbound : Nat.nth Nat.Prime (i+1) < K+1 := Nat.nth_lt_of_lt_count hnum
  have hne : Nat.nth Nat.Prime (i+1) ≠ K := by
    intro he
    have hprime := Nat.prime_nth_prime (i+1)
    rw [he] at hprime
    have htwo : 2 ∣ K := ⟨v, rfl⟩
    rcases (Nat.dvd_prime hprime).mp htwo with h | h
    · omega
    · have : 2 < K := by dsimp [K,v]; nlinarith [Nat.mul_self_le_mul_self hx]
      omega
  change Nat.nth Nat.Prime (i+1) < 32*x^2
  omega

/-- An explicit cubic bound for the logarithm of the full CRT modulus. -/
theorem widthD_bound (n : ℕ) : widthD n ≤ 2^(20*(n+2)^3) := by
  let x := n + 2
  have hx : 2 ≤ x := by dsimp [x]; omega
  let B := 2^(4*x*(4*n+10))
  have hb : ∀ i ∈ List.range n, widthFactor n i ≤ B := by
    intro i hi
    have h := (oddPrime_lt_search_limit (List.mem_range.mp hi)).le.trans (search_cap hx)
    exact (Nat.pow_le_pow_left h (4*n+10)).trans_eq (pow_mul _ _ _).symm
  have hproduct := List.prod_le_pow_card ((List.range n).map (widthFactor n)) B (by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact hb i hi)
  rw [List.length_map, List.length_range] at hproduct
  change widthD n ≤ B^n at hproduct
  refine hproduct.trans ?_
  dsimp [B]
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  dsimp [x]
  nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^2)]

theorem widthD_fits (n : ℕ) : widthD n < 2^(universeSize n) := by
  let x := n+2
  have hx : 2 ≤ x := by dsimp [x]; omega
  have hi : 20 < x^5 := lt_of_lt_of_le (by decide : 20 < 2^5) (Nat.pow_le_pow_left hx _)
  have h : 20*x^3 < x^20 := calc
    20*x^3 < x^5*x^3 := Nat.mul_lt_mul_of_pos_right hi (by positivity)
    _ = x^8 := (pow_add x 5 3).symm
    _ ≤ x^20 := Nat.pow_le_pow_right (by omega) (by decide)
  exact (widthD_bound n).trans_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr h)

theorem width_parameter_fits (n : ℕ) : n < universeSize n := by
  have h : (n+2)^1 ≤ (n+2)^20 := Nat.pow_le_pow_right (by omega) (by decide)
  simpa [universeSize] using (lt_of_lt_of_le (show n < (n+2)^1 by simp) h)

end DiophantineNP.WidthData
