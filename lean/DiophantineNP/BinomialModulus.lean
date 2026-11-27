import DiophantineNP.MultipleReadout
import DiophantineNP.TailRadix
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Bounds

/-! # A coefficient-extractable modulus for native binary readout

The prime divisors of one central binomial coefficient supply enough distinct
slots. All of them are retained. A single ordinary power of that coefficient
is a common multiple of the required prime powers, so the modulus itself
has a bounded integer expression with no iterated product.
-/
namespace DiophantineNP.BinomialModulus
open scoped BigOperators

def half (n : ℕ) := 16*(n+2)^2
def central (n : ℕ) := (half n).centralBinom
def primes (n : ℕ) := (central n).primeFactors
def countSlots (n : ℕ) := (primes n).card
def exponent (n : ℕ) := 8*half n+10
def modulus (n : ℕ) := (central n)^(exponent n)

private theorem central_lower (v : ℕ) : 2^v ≤ v.centralBinom := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ]
    refine (Nat.mul_le_mul_right 2 ih).trans ?_
    apply Nat.le_of_mul_le_mul_left (c:=v+1) _ (by omega)
    calc (v+1)*(v.centralBinom*2) ≤ 2*(2*v+1)*v.centralBinom := by
          nlinarith [Nat.zero_le (v*v.centralBinom)]
      _ = _ := (Nat.succ_mul_centralBinom_succ v).symm

private theorem cap {x : ℕ} (h : 2 ≤ x) : 32*x^2 ≤ 2^(4*x) := by
  induction x,h using Nat.le_induction with
  | base => decide
  | succ x hx ih =>
    rw [show 4*(x+1)=4*x+4 by omega,pow_add]
    exact (show 32*(x+1)^2 ≤ 32*x^2*2^4 by nlinarith [Nat.mul_self_le_mul_self hx]).trans (Nat.mul_le_mul_right _ ih)

theorem slots_lower (n : ℕ) : n+1 ≤ countSlots n := by
  let v := half n
  let s := primes n
  have hv : 0 < v := by dsimp [v,half]; positivity
  have fac : ∏ p ∈ s, p^v.centralBinom.factorization p = v.centralBinom :=
    Nat.factorization_prod_pow_eq_self (Nat.centralBinom_ne_zero v)
  have top : 2*v ≤ 2^(4*(n+2)) := by simpa [v,half,← Nat.mul_assoc] using cap (x:=n+2) (by omega)
  have h : 2^v ≤ 2^(4*(n+2)*s.card) := calc
    _ ≤ v.centralBinom := central_lower _
    _ = _ := fac.symm
    _ ≤ ∏ _p ∈ s, 2*v := Finset.prod_le_prod' (fun _ _ => Nat.pow_factorization_choose_le (by omega : 0<2*v))
    _ = (2*v)^s.card := by simp
    _ ≤ (2^(4*(n+2)))^s.card := Nat.pow_le_pow_left top _
    _ = _ := (pow_mul ..).symm
  have h' := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h
  by_contra! bad
  have hs : s.card ≤ n := Nat.le_of_lt_succ bad
  have := Nat.mul_le_mul_left (4*(n+2)) hs
  dsimp [v,half] at h'
  nlinarith

theorem slots_upper (n : ℕ) : countSlots n ≤ 2*half n := by
  have h : 2^(primes n).card ≤ central n := calc
    _ = ∏ _p ∈ primes n, 2 := by simp
    _ ≤ ∏ p ∈ primes n, p := Finset.prod_le_prod' (fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le)
    _ ≤ central n := Nat.le_of_dvd (Nat.centralBinom_pos _) (Nat.prod_primeFactors_dvd _)
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (h.trans (Nat.choose_le_two_pow _ _))

noncomputable def base (n i : ℕ) := if h : i < countSlots n then
  ((primes n).orderIsoOfFin rfl ⟨i,h⟩).val else 2

private theorem base_mem (n i : ℕ) (h : i<countSlots n) : base n i ∈ primes n := by
  simp only [base,dif_pos h]; exact ((primes n).orderIsoOfFin rfl ⟨i,h⟩).property

noncomputable def frame (n : ℕ) : Readout.Frame where
  n := countSlots n
  m := 2^(countSlots n+2)
  d i := (base n i)^(exponent n)
  width_pos := (Nat.succ_pos n).trans_le (slots_lower n)
  scale := Nat.pow_le_pow_right (by decide) (by omega)
  size i hi := by
    have hb := (Nat.mem_primeFactors.mp (base_mem n i hi)).1.two_le
    calc countSlots n*2^(countSlots n+2) ≤ 2^(countSlots n)*2^(countSlots n+2) :=
          Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
      _ = 2^(countSlots n+(countSlots n+2)) := (pow_add ..).symm
      _ < 2^(exponent n) := Nat.pow_lt_pow_right (by decide) (by have := slots_upper n; unfold exponent; omega)
      _ ≤ _ := Nat.pow_le_pow_left hb _
  primePower i hi := (isPrimePow_nat_iff _).mpr ⟨_,_,(Nat.mem_primeFactors.mp (base_mem n i hi)).1,
    by unfold exponent; omega,rfl⟩
  coprime := by
    apply List.Nodup.pairwise_of_forall_ne List.nodup_range
    intro i hi j hj hne
    apply Nat.coprime_pow_primes _ _ (Nat.mem_primeFactors.mp (base_mem _ _ (List.mem_range.mp hi))).1
      (Nat.mem_primeFactors.mp (base_mem _ _ (List.mem_range.mp hj))).1
    simp only [base,dif_pos (List.mem_range.mp hi),dif_pos (List.mem_range.mp hj)]
    intro he
    have eqn := ((primes n).orderIsoOfFin rfl).injective (Subtype.ext he)
    exact hne (congrArg Fin.val eqn)

theorem frame_D_dvd (n : ℕ) : (frame n).D ∣ modulus n := by
  have he : (((List.range (countSlots n)).map (fun i => (base n i)^(exponent n))).prod) =
      (∏ p ∈ primes n, p)^(exponent n) := by
    rw [← List.prod_toFinset _ List.nodup_range,List.toFinset_range,Finset.prod_pow,
      ← Fin.prod_univ_eq_prod_range]
    congr 1
    let g := (primes n).orderIsoOfFin rfl
    have hh : (∏ i : Fin (countSlots n), base n i.val) = ∏ j : primes n, j.val :=
      Fintype.prod_equiv g.toEquiv _ _ (by intro i; simp [base,g])
    exact hh.trans (Finset.prod_attach (primes n) id)
  change ((List.range (countSlots n)).map (fun i => (base n i)^(exponent n))).prod ∣ _
  rw [he]; exact pow_dvd_pow_of_dvd (Nat.prod_primeFactors_dvd _) _

/-- The ordinary modulus has polynomial bit length, before any multiplier is
computed. Both input words fit the resulting native width. -/
theorem modulus_bound (n : ℕ) : modulus n ≤ 2^(2*half n*exponent n) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.choose_le_two_pow ..) _

set_option maxHeartbeats 1200000 in
/-- A uniform positive multiple of the frame modulus can be recovered from
one binomial value and one scalar power. The multiplier remains explicit. -/
theorem native_readout (n a b : ℕ) (ha : a<2^n) (hb : b<2^n) :
    Readout.modulusCertificate (modulus n) ((modulus n/(frame n).D)*(frame n).J) (frame n).m a b ↔
      ∀ i, a.testBit i = true → b.testBit i = true := by
  let D := (frame n).D
  have e : (modulus n / D)*D = modulus n := Nat.div_mul_cancel (frame_D_dvd n)
  have hp : 0 < modulus n := pow_pos (Nat.centralBinom_pos _) _
  have hh : 0 < modulus n / D := by by_contra! he; have := Nat.eq_zero_of_le_zero he; rw [this,zero_mul] at e; omega
  have hn : 2^n ≤ 2^(frame n).n := Nat.pow_le_pow_right (by decide) ((Nat.le_succ n).trans (slots_lower n))
  have hy := (frame n).multiple_certificate_iff (modulus n / D) a b hh (ha.trans_le hn) (hb.trans_le hn)
  change Readout.modulusCertificate ((modulus n / D)*D) _ _ a b ↔ _ at hy
  rwa [e] at hy

/-- A closed expression for the modulus involving three powers, one quotient,
and one remainder. No list of primes is an input to this expression. -/
theorem modulus_closed (n : ℕ) :
    let v := half n
    let R := (2:ℤ)^(2*v+1)
    ((((1+R)^(2*v)) / R^v) % R)^(exponent n) = (modulus n:ℤ) := by
  have e := TailRadix.choose_from_power (2*half n) (half n) (by omega)
  simp only at e ⊢
  rw [e,modulus,Nat.cast_pow]; rfl

end DiophantineNP.BinomialModulus
