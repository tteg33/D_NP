import DiophantineNP.WidthData
import DiophantineNP.ShortResidue
import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.ChineseRemainder

/-! # Short exponents for powers in finite groups

This is the arithmetic and group-theoretic part of Hesse, Allender and
Barrington, §6.1, Lemma 6.1. A CRT basis gives an exact factorization of a
power. Each auxiliary group element is singled out by a small power test.
The argument uses integer remainders throughout, including the estimate
for the final correction. -/
namespace DiophantineNP.HABGroupPower
open Finset

def modulus (s : Finset ℕ) : ℕ := ∏ d ∈ s, d

def cofactor (s : Finset ℕ) (d : ℕ) : ℕ := modulus (s.erase d)

private theorem factor_eq {s : Finset ℕ} {d : ℕ} (hd : d ∈ s) :
    cofactor s d * d = modulus s := s.prod_erase_mul id hd

private theorem prime_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ≠ q) : p.Coprime q := by
  apply hp.coprime_iff_not_dvd.mpr
  intro dv
  rcases (Nat.dvd_prime hq).mp dv with eq | eq
  · exact hp.ne_one eq
  · exact h eq

private theorem modEq_modulus {s : Finset ℕ} {a b : ℕ}
    (prime : ∀ d ∈ s, Nat.Prime d) (h : ∀ d ∈ s, a ≡ b [MOD d]) :
    a ≡ b [MOD modulus s] := by
  induction s using Finset.induction_on with
  | empty => exact Nat.modEq_one
  | @insert d s hd ih =>
    simp only [modulus, Finset.prod_insert hd]
    have cop : d.Coprime (modulus s) := Nat.coprime_prod_right_iff.mpr fun j hj =>
      prime_coprime (prime _ (mem_insert_self ..)) (prime _ (mem_insert_of_mem hj))
        (fun e => hd (e ▸ hj))
    exact (Nat.modEq_and_modEq_iff_modEq_mul cop).mp
      ⟨h d (mem_insert_self ..),ih (fun j hj => prime _ (mem_insert_of_mem hj))
        (fun j hj => h _ (mem_insert_of_mem hj))⟩

/-- CRT weights can be chosen strictly smaller than the corresponding primes. -/
theorem crt_weights_with_local (s : Finset ℕ) (prime : ∀ d ∈ s, Nat.Prime d) (f : ℕ) :
    ∃ u : ℕ → ℕ, (∀ d ∈ s, u d < d ∧ u d * cofactor s d ≡ f [MOD d]) ∧
      (∑ d ∈ s, u d * cofactor s d) ≡ f [MOD modulus s] := by
  classical
  have localWeight (d : ℕ) (hd : d ∈ s) :
      ∃ z < d, z * cofactor s d ≡ f [MOD d] := by
    have cop : (cofactor s d).Coprime d :=
      Nat.coprime_prod_left_iff.mpr fun j hj =>
        prime_coprime (prime _ (mem_erase.mp hj).2) (prime _ hd) (mem_erase.mp hj).1
    obtain ⟨a,ha⟩ := Nat.exists_mul_emod_eq_one_of_coprime cop (prime _ hd).one_lt
    have inv : a * cofactor s d ≡ 1 [MOD d] := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt (prime _ hd).one_lt, Nat.mul_comm] using ha
    refine ⟨(f*a)%d, Nat.mod_lt _ (prime _ hd).pos, ?_⟩
    apply ((Nat.mod_modEq (f*a) d).mul_right _).trans
    simpa only [Nat.mul_assoc,Nat.mul_one] using inv.mul_left f
  let u d := if hd : d ∈ s then (localWeight d hd).choose else 0
  have spec {d} (hd : d ∈ s) : u d < d ∧ u d * cofactor s d ≡ f [MOD d] := by
    simpa only [u, dif_pos hd] using (localWeight d hd).choose_spec
  refine ⟨u,fun _ hd => spec hd,modEq_modulus prime ?_⟩
  intro d hd
  have rest : d ∣ ∑ j ∈ s.erase d, u j * cofactor s j := by
    apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id
      (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1.symm,hd⟩)) _
  rw [← s.sum_erase_add (fun j => u j * cofactor s j) hd]
  simpa only [Nat.zero_add] using (Nat.modEq_zero_iff_dvd.mpr rest).add (spec hd).2

theorem crt_weights (s : Finset ℕ) (prime : ∀ d ∈ s, Nat.Prime d) (f : ℕ) :
    ∃ u : ℕ → ℕ, (∀ d ∈ s, u d < d) ∧
      (∑ d ∈ s, u d * cofactor s d) ≡ f [MOD modulus s] := by
  obtain ⟨u,localWeights,congr⟩ := crt_weights_with_local s prime f
  exact ⟨u,fun d hd => (localWeights d hd).1,congr⟩

/-- The scaled CRT approximation leaves a small nonnegative correction.
The modulus is larger than the group order and the input exponent is reduced. -/
theorem exponent_factorization_with_local {s : Finset ℕ} (prime : ∀ d ∈ s, Nat.Prime d)
    {n r : ℕ} (hr : r < n) (hn : n < modulus s) :
    ∃ (u : ℕ → ℕ) (c : ℕ),
      (∀ d ∈ s, u d < d ∧ u d*(modulus s/d) ≡ (r*modulus s/n) [MOD d]) ∧ c ≤ ∑ d ∈ s, u d ∧
      (c + ∑ d ∈ s, u d * (n/d)) ≡ r [MOD n] := by
  let D := modulus s
  let f := r*D/n
  have npos : 0<n := by omega
  have Dpos : 0<D := by dsimp [D]; omega
  have f_lt : f < D := (Nat.div_lt_iff_lt_mul npos).mpr (by
    have := Nat.mul_lt_mul_of_pos_right hr Dpos
    simpa [Nat.mul_comm] using this)
  obtain ⟨u,hu,hcrt⟩ := crt_weights_with_local s prime f
  let W := ∑ d ∈ s, u d * cofactor s d
  let m := W/D
  let T := ∑ d ∈ s, u d * (n/d)
  let E := ∑ d ∈ s, u d * cofactor s d * (n%d)
  have hm : W = f + m*D := by
    have eq : W%D = f%D := hcrt
    rw [Nat.mod_eq_of_lt f_lt] at eq
    have := Nat.mod_add_div W D
    rw [eq, Nat.mul_comm D] at this
    exact this.symm
  have sumId : T*D + E = W*n := by
    simp only [T,E,W,Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have fac : cofactor s d * d = D := factor_eq hd
    calc
      _ = (u d * cofactor s d) * (d * (n/d) + n%d) := by rw [←fac]; ring
      _ = _ := by rw [Nat.div_add_mod]
  have estimate : E ≤ (∑ d ∈ s, u d)*D := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d hd
    calc
      u d * cofactor s d * (n%d) ≤ u d * cofactor s d * d :=
        Nat.mul_le_mul_left _ (Nat.mod_lt _ (prime _ hd).pos).le
      _ = u d * D := by rw [Nat.mul_assoc, factor_eq hd]
  have eq : (r+m*n)*D = T*D + E + (r*D%n) := by
    calc
      (r+m*n)*D = n*f + r*D%n + m*n*D := by rw [show n*f+r*D%n=r*D from Nat.div_add_mod ..]; ring
      _ = W*n + r*D%n := by rw [hm]; ring
      _ = _ := by rw [sumId]
  have lo : T ≤ r+m*n := Nat.le_of_mul_le_mul_right (by rw [eq]; omega) Dpos
  let c := r+m*n-T
  have hc : c+T=r+m*n := Nat.sub_add_cancel lo
  have small : c ≤ ∑ d ∈ s, u d := by
    have rem : r*D%n < D := (Nat.mod_lt _ npos).trans hn
    have e : c*D + T*D = T*D+E+(r*D%n) := by rw [←Nat.add_mul,hc,eq]
    apply Nat.le_of_lt_succ
    apply Nat.lt_of_mul_lt_mul_right (a := D)
    rw [Nat.succ_mul]
    omega
  refine ⟨u,c,fun d hd => ?_,small,?_⟩
  · have cf : cofactor s d = modulus s/d :=
      Nat.eq_div_of_mul_eq_left (prime d hd).ne_zero (factor_eq hd)
    simpa only [←cf] using hu d hd
  · change (c+T)%n = r%n
    rw [hc,Nat.mul_comm m, Nat.add_mul_mod_self_left]

theorem exponent_factorization {s : Finset ℕ} (prime : ∀ d ∈ s, Nat.Prime d)
    {n r : ℕ} (hr : r < n) (hn : n < modulus s) :
    ∃ (u : ℕ → ℕ) (c : ℕ), (∀ d ∈ s, u d < d) ∧ c ≤ ∑ d ∈ s, u d ∧
      (c + ∑ d ∈ s, u d * (n/d)) ≡ r [MOD n] := by
  obtain ⟨u,c,localWeights,size,congr⟩ := exponent_factorization_with_local prime hr hn
  exact ⟨u,c,fun d hd => (localWeights d hd).1,size,congr⟩

/-- Each basis element is uniquely identifiable by powering only to exponents
below or equal to its associated CRT modulus. The group may be nonabelian. -/
theorem root_test {G : Type*} [Group G] (a x : G) {d : ℕ}
    (cop : (Nat.card G).Coprime d) :
    x^d = (a^(Nat.card G % d))⁻¹ ↔ x = a^(Nat.card G/d) := by
  have h : (a^(Nat.card G/d))^d = (a^(Nat.card G%d))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [←pow_mul,←pow_add,Nat.mul_comm (Nat.card G/d) d,Nat.div_add_mod,pow_card_eq_one']
  exact ⟨fun e => cop.pow_left_bijective.injective (e.trans h.symm),fun e => e ▸ h⟩


private theorem pow_card_le_modulus (s : Finset ℕ) (hp : ∀ p ∈ s, Nat.Prime p) :
    2^s.card ≤ modulus s := by
  simpa [modulus] using Finset.prod_le_prod' (fun p hp' => (hp p hp').two_le)

private theorem trim {n K : ℕ} (hn : 0<n) (s : Finset ℕ) :
    (∀ p ∈ s, p ≤ K) → n < modulus s →
    ∃ t ⊆ s, n < modulus t ∧ modulus t ≤ n*K := by
  classical
  induction s using Finset.strongInductionOn
  rename_i s ih
  intro bound large
  by_cases cut : ∃ p ∈ s, n < modulus (s.erase p)
  · obtain ⟨p,hp,h⟩ := cut
    obtain ⟨t,ht,lo,hi⟩ := ih _ (s.erase_ssubset hp) (fun q hq => bound q (s.erase_subset _ hq)) h
    exact ⟨t,ht.trans (s.erase_subset _),lo,hi⟩
  · have nonempty : s.Nonempty := by
      apply nonempty_iff_ne_empty.mpr
      rintro rfl
      simp [modulus] at large
      omega
    obtain ⟨p,hp⟩ := nonempty
    have le : modulus (s.erase p) ≤ n := Nat.le_of_not_gt (fun h => cut ⟨p,hp,h⟩)
    refine ⟨s,Subset.rfl,large,?_⟩
    rw [←factor_eq hp]
    exact Nat.mul_le_mul le (bound p hp)

/-- An elementary bound for the size of a CRT prime. It is quadratic in the
binary length of the group order. -/
def primeBound (n : ℕ) : ℕ := 32 * (2 * (n.log2+1) + 2)^2

/-- A basis of at most one prime per exponent bit. The whole product fits
in a polynomial-size numerical domain, although its factors are polylogarithmic. -/
theorem basis_exists (n : ℕ) (hn : 0<n) :
    ∃ s : Finset ℕ, s.card ≤ n.log2+1 ∧ n < modulus s ∧ modulus s ≤ n * primeBound n ∧
      ∀ p ∈ s, p.Prime ∧ n.Coprime p ∧ p < primeBound n := by
  classical
  let L := n.log2+1
  let pool := (range (2*L)).image (fun i => Nat.nth Nat.Prime (i+1))
  have poolSize : pool.card = 2*L := by
    exact (card_image_of_injective _ (fun i j h => Nat.succ.inj
      (Nat.nth_injective Nat.infinite_setOf_prime h))).trans (card_range _)
  have poolSpec {p} (hp : p ∈ pool) : p.Prime ∧ p < primeBound n := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact ⟨Nat.prime_nth_prime _,WidthData.oddPrime_lt_search_limit (mem_range.mp hi)⟩
  have badSize : n.primeFactors.card ≤ n.log2 := (Nat.le_log2 hn.ne').mpr
    ((pow_card_le_modulus n.primeFactors (fun _ h => (Nat.mem_primeFactors.mp h).1)).trans
      (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd _)))
  have enough : L ≤ (pool \ n.primeFactors).card := by
    have h := Finset.card_le_card_sdiff_add_card (s := pool) (t := n.primeFactors)
    rw [poolSize] at h
    dsimp [L] at h ⊢
    omega
  obtain ⟨v,hsub,hlen⟩ := Finset.exists_subset_card_eq enough
  have spec {p} (hp : p ∈ v) : p.Prime ∧ n.Coprime p ∧ p < primeBound n := by
    obtain ⟨hpool,hbad⟩ := mem_sdiff.mp (hsub hp)
    obtain ⟨prime,small⟩ := poolSpec hpool
    exact ⟨prime,(prime.coprime_iff_not_dvd.mpr (fun h => hbad
      (Nat.mem_primeFactors.mpr ⟨prime,h,hn.ne'⟩))).symm,small⟩
  have large : n < modulus v := by
    have h := pow_card_le_modulus v (fun _ h => (spec h).1)
    rw [hlen] at h
    exact Nat.lt_log2_self.trans_le h
  obtain ⟨s,hs,lo,hi⟩ := trim hn v (fun _ h => (spec h).2.2.le) large
  exact ⟨s,(card_le_card hs).trans hlen.le,lo,hi,fun _ h => spec (hs h)⟩

private theorem prod_powers {G : Type*} [Monoid G] (a : G) (s : List ℕ) (p : ℕ → ℕ) :
    (s.map (fun d => a^(p d))).prod = a^(s.map p).sum := by
  induction s with
  | nil => simp
  | cons d s ih => simp [ih,pow_add]

private theorem factor_value {G : Type*} [Group G] (a : G) (r c : ℕ)
    (s : Finset ℕ) (u : ℕ → ℕ) (x : ℕ → G)
    (cop : ∀ d ∈ s, (Nat.card G).Coprime d)
    (congr : (c+∑ d ∈ s, u d*(Nat.card G/d)) ≡ r [MOD Nat.card G])
    (hx : ∀ d ∈ s, (x d)^d = (a^(Nat.card G%d))⁻¹) :
    a^r = a^c * (s.toList.map (fun d => (x d)^(u d))).prod := by
  let n := Nat.card G
  have he : s.toList.map (fun d => (x d)^(u d)) =
      s.toList.map (fun d => a^(u d*(n/d))) := by
    apply List.map_congr_left
    intro d hd
    have mem : d ∈ s := by simpa using hd
    rw [(root_test a _ (cop d mem)).mp (hx d mem),←pow_mul,Nat.mul_comm]
  rw [he,prod_powers, Finset.sum_map_toList, ←pow_add]
  calc
    a^r = a^(r%n) := (pow_mod_natCard ..).symm
    _ = _ := by rw [←congr]; apply pow_mod_natCard

/-- The small-root tests uniquely determine the factors for each basis prime.
The correction exponent is bounded by a cubic polynomial in the order's bit
length. The product formula uses any fixed list ordering, including for a
noncommutative group. An arbitrary natural exponent is accepted. -/
theorem group_factorization {G : Type*} [Group G] [Finite G] (a : G) (r : ℕ) :
    let n := Nat.card G
    ∃ (s : Finset ℕ) (u : ℕ → ℕ) (c : ℕ),
      s.card ≤ n.log2+1 ∧ n < modulus s ∧ modulus s ≤ n * primeBound n ∧
      (∀ d ∈ s, d.Prime ∧ n.Coprime d ∧ u d < d ∧ d < primeBound n) ∧
      c ≤ (n.log2+1) * primeBound n ∧
      (c+∑ d ∈ s, u d*(n/d)) ≡ r [MOD n] ∧
      ∀ x : ℕ → G, (∀ d ∈ s, (x d)^d = (a^(n%d))⁻¹) →
        a^r = a^c * (s.toList.map (fun d => (x d)^(u d))).prod := by
  dsimp only
  let n := Nat.card G
  have hn : 0<n := Nat.card_pos
  obtain ⟨s,hcard,hlo,hhi,hs⟩ := basis_exists n hn
  obtain ⟨u,c,hu,hc,hcong⟩ := exponent_factorization (fun d h => (hs d h).1)
    (Nat.mod_lt r hn) hlo
  have cub : c ≤ (n.log2+1) * primeBound n := calc
    c ≤ ∑ d ∈ s, u d := hc
    _ ≤ ∑ _d ∈ s, primeBound n := sum_le_sum fun d hd =>
      ((hu d hd).trans (hs d hd).2.2).le
    _ = s.card * primeBound n := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hcard
  refine ⟨s,u,c,hcard,hlo,hhi,fun d hd => ⟨(hs _ hd).1,(hs _ hd).2.1,hu _ hd,(hs _ hd).2.2⟩,
    cub,hcong.trans (Nat.mod_modEq r n),?_⟩
  exact fun x hx => factor_value a r c s u x (fun d hd => (hs d hd).2.1)
    (hcong.trans (Nat.mod_modEq r n)) hx

/-- A group oracle receives a list of identical entries. -/
def copies {G : Type*} [Monoid G] (a : G) (k : ℕ) : G := (List.replicate k a).prod

/-- Ordinary integer computations on short numbers and group products on
polylogarithmically many entries. This is a mathematical specification of the
certificate. Its functions over the basis have not been bound in a finite
first-order formula. -/
def ShortCertificate {G : Type*} [Group G] (a b : G) (r : ℕ) : Prop :=
  let n := Nat.card G
  ∃ (s : Finset ℕ) (u : ℕ → ℕ) (c : ℕ) (x : ℕ → G),
    s.card ≤ n.log2+1 ∧ n < modulus s ∧ modulus s ≤ n*primeBound n ∧
    (∀ d ∈ s, d.Prime ∧ n.Coprime d ∧ u d < d ∧ d < primeBound n) ∧
    c ≤ (n.log2+1)*primeBound n ∧
    (c+∑ d ∈ s, u d*(n/d)) ≡ r [MOD n] ∧
    (∀ d ∈ s, copies (x d) d = (copies a (n%d))⁻¹) ∧
    b = copies a c * (s.toList.map (fun d => copies (x d) (u d))).prod

/-- Both completeness and soundness of the short group product checks. -/
theorem shortCertificate_iff {G : Type*} [Group G] [Finite G] (a b : G) (r : ℕ) :
    ShortCertificate a b r ↔ b = a^r := by
  constructor
  · rintro ⟨s,u,c,x,_,_,_,hs,_,congr,tests,hb⟩
    simp only [copies,List.prod_replicate] at tests hb
    exact hb.trans (factor_value a r c s u x (fun d hd => (hs d hd).2.1) congr tests).symm
  · rintro rfl
    obtain ⟨s,u,c,hk,hlo,hhi,hs,hc,congr,h⟩ := group_factorization a r
    let x (d : ℕ) := a^(Nat.card G/d)
    have test (d) (hd : d ∈ s) :
        (x d)^d = (a^(Nat.card G%d))⁻¹ := (root_test a _ (hs d hd).2.1).2 rfl
    refine ⟨s,u,c,x,hk,hlo,hhi,hs,hc,congr,?_,?_⟩
    · simpa only [copies,List.prod_replicate] using test
    · simpa only [copies,List.prod_replicate] using h x test

/-- HAB §6.2, at the level of the exact numerical predicate. A prime modular
power is equivalent to short product checks in the unit group, plus the zero
case. No unrestricted power occurs in the checks. -/
theorem prime_power_iff {p a : ℕ} (prime : p.Prime) (ha : a<p) (r b : ℕ) :
    a^r%p = b ↔ (a=0 ∧ b=if r=0 then 1 else 0) ∨
      ∃ g h : (ZMod p)ˣ, (g : ZMod p).val = a ∧ (h : ZMod p).val = b ∧
        ShortCertificate g h r := by
  letI : Fact p.Prime := ⟨prime⟩
  have zero : (0:ℕ)^r%p = (if r=0 then 1 else 0) := by
    cases r <;> simp [Nat.mod_eq_of_lt prime.one_lt]
  constructor
  · intro value
    by_cases h0 : a=0
    · exact Or.inl ⟨h0,by subst a; exact value.symm.trans zero⟩
    · right
      have nonzero : (a : ZMod p) ≠ 0 := by
        intro h
        exact h0 ((ZMod.val_natCast_of_lt ha).symm.trans ((ZMod.val_eq_zero _).2 h))
      let g := Units.mk0 (a : ZMod p) nonzero
      refine ⟨g,g^r,ZMod.val_natCast_of_lt ha,?_,(shortCertificate_iff ..).2 rfl⟩
      change ((a : ZMod p)^r).val = b
      rwa [←Nat.cast_pow, ZMod.val_natCast]
  · rintro (⟨rfl,hb⟩|⟨g,h,hg,hh,check⟩)
    · exact zero.trans hb.symm
    · have cast_eq : (a : ZMod p) = (g : ZMod p) := by rw [←hg,ZMod.natCast_zmod_val]
      rw [←ZMod.val_natCast, Nat.cast_pow, cast_eq,←Units.val_pow_eq_pow_val,
        ←(shortCertificate_iff ..).1 check,hh]


/-- The selected basis can be transmitted by its single product. Its members
are exactly the primes dividing that number. -/
theorem basis_code {s : Finset ℕ} (hp : ∀ d ∈ s, Nat.Prime d) :
    (modulus s).primeFactors = s := Nat.primeFactors_prod hp

/-- Inside a finite universe, a prime and a witness for its cofactor identify
membership in the basis whose code is the supplied integer. -/
def basisMember {k : ℕ} (p D : Fin k) : Counting.Formula k :=
  WidthFormula.andF (PrimeFormula.prime p) (.ex (WidthFormula.mulF p.succ 0 D.succ))

theorem basisMember_spec {k U : ℕ} (p D : Fin k) (e : Fin k → Fin U) (pos : 0<(e D).val) :
    (basisMember p D).eval e = true ↔ (e p).val ∈ (e D).val.primeFactors := by
  simp only [basisMember, WidthFormula.andF_spec,PrimeFormula.prime_true,
    PrimeFormula.exists_true,WidthFormula.mulF_spec, Fin.cases_zero,Fin.cases_succ,Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp,q,h⟩; exact ⟨hp,⟨q,h.symm⟩,pos.ne'⟩
  · rintro ⟨hp,⟨q,h⟩,_⟩
    have le := Nat.le_mul_of_pos_left q hp.pos
    rw [←h] at le
    exact ⟨hp,⟨q,le.trans_lt (e D).isLt⟩,h.symm⟩

open ShortResidue (Predicate)

/-- Variables 0 through 3 denote the code D, a prime divisor d, the scaled
target f, and the coefficient w. Formula construction uses no powering. -/
private def weightProgram : Predicate :=
  (Predicate.lt 3 1).both <| Predicate.ex 4 <| (Predicate.mul 4 1 0).both <|
  Predicate.ex 5 <| (Predicate.mul 3 4 5).both <| Predicate.ex 6 <| Predicate.ex 7 <|
    (Predicate.mul 1 6 7).both ((Predicate.add 5 7 2).either (Predicate.add 2 7 5))

private theorem shift_iff {U d t f : ℕ} (h : 0<d) (ht : t<U) (hf : f<U) :
    (∃ a<U, ∃ b<U, d*a=b ∧ (t+b=f ∨ f+b=t)) ↔ t ≡ f [MOD d] := by
  constructor
  · rintro ⟨a,_,b,_,rfl,ha|ha⟩
    · rw [←ha,Nat.ModEq,Nat.add_mul_mod_self_left]
    · rw [←ha,Nat.ModEq,Nat.add_mul_mod_self_left]
  · intro congr
    have ordered {x y : ℕ} (le : x≤y) (bound : y<U) (eq : x ≡ y [MOD d]) :
        ∃ a<U, ∃ b<U, d*a=b ∧ x+b=y := by
      obtain ⟨a,ha⟩ := (Nat.modEq_iff_dvd' le).mp eq
      have := Nat.le_mul_of_pos_left a h
      exact ⟨a,by omega,y-x,by omega,ha.symm,by omega⟩
    rcases le_total t f with le|le
    · obtain ⟨a,ha,b,hb,eq,hv⟩ := ordered le hf congr
      exact ⟨a,ha,b,hb,eq,Or.inl hv⟩
    · obtain ⟨a,ha,b,hb,eq,hv⟩ := ordered le ht congr.symm
      exact ⟨a,ha,b,hb,eq,Or.inr hv⟩

private theorem weightProgram_spec (U : ℕ) (t : ℕ → ℕ → Bool) (e : ℕ → ℕ)
    (bound : ∀ i, e i < U) (hd : 0<e 1) (divides : e 1 ∣ e 0) :
    weightProgram.holds U t e ↔ e 3 < e 1 ∧ e 3 * (e 0/e 1) ≡ e 2 [MOD e 1] := by
  simp only [weightProgram,ShortResidue.Predicate.both,ShortResidue.Predicate.either,
    ShortResidue.Predicate.ex,ShortResidue.Predicate.mul,ShortResidue.Predicate.add,
    ShortResidue.Predicate.lt]
  norm_num [Function.update]
  intro hw
  constructor
  · rintro ⟨q,_,hq,v,hv,he,more⟩
    have qeq := Nat.eq_div_of_mul_eq_left hd.ne' hq
    subst v
    rw [←qeq]
    exact (shift_iff hd hv (bound 2)).mp more
  · intro congr
    let q := e 0 / e 1
    have eq : q*e 1 = e 0 := Nat.div_mul_cancel divides
    have vb : e 3*q < U := calc
      e 3*q ≤ q*e 1 := by simpa [Nat.mul_comm] using Nat.mul_le_mul_right q hw.le
      _ < U := eq ▸ bound 0
    exact ⟨q,(Nat.div_le_self ..).trans_lt (bound 0),eq,e 3*q,vb,rfl,
      (shift_iff hd vb (bound 2)).mpr congr⟩

/-- A fixed formula for the CRT coefficient in exponent space. -/
def weightFormula {k : ℕ} (D d f w : Fin k) : WidthFormula.Template k :=
  weightProgram.syntaxF (fun i => if i=0 then D else if i=1 then d else if i=2 then f else w)

theorem weightFormula_spec {U k : ℕ} (D d f w : Fin k) (e : Fin k → Fin U)
    (A : ℕ → ℕ → Bool) (hd : 0<(e d).val) (divides : (e d).val ∣ (e D).val) :
    (weightFormula D d f w).eval (fun i j => A i.val j.val) e = true ↔
      (e w).val < (e d).val ∧ (e w).val * ((e D).val / (e d).val) ≡ (e f).val [MOD (e d).val] := by
  let σ (i : ℕ) : Fin k := if i=0 then D else if i=1 then d else if i=2 then f else w
  rw [weightFormula,weightProgram.valid]
  exact weightProgram_spec U A (fun i => (e (σ i)).val) (fun i => Fin.isLt _) hd divides

/-- The finite formula recognizes exactly one coefficient whenever D comes
from a prime basis. Its quantifiers never need a value beyond D or f. -/
theorem unique_weight {s : Finset ℕ} (prime : ∀ p ∈ s, Nat.Prime p)
    {d : ℕ} (hd : d ∈ s) (f : ℕ) :
    ∃! w : ℕ, w<d ∧ w*(modulus s/d) ≡ f [MOD d] := by
  have cof : cofactor s d = modulus s/d :=
    Nat.eq_div_of_mul_eq_left (prime _ hd).ne_zero (factor_eq hd)
  have cop : (cofactor s d).Coprime d := Nat.coprime_prod_left_iff.mpr fun j hj =>
    prime_coprime (prime _ (mem_erase.mp hj).2) (prime _ hd) (mem_erase.mp hj).1
  obtain ⟨a,ha⟩ := Nat.exists_mul_emod_eq_one_of_coprime cop (prime _ hd).one_lt
  have inv : a * cofactor s d ≡ 1 [MOD d] := by
    simpa [Nat.ModEq,Nat.mod_eq_of_lt (prime _ hd).one_lt,Nat.mul_comm] using ha
  have h : ((f*a)%d)*(cofactor s d) ≡ f [MOD d] := by
    apply ((Nat.mod_modEq (f*a) d).mul_right _).trans
    simpa only [Nat.mul_assoc,Nat.mul_one] using inv.mul_left f
  rw [←cof]
  refine ⟨_,⟨Nat.mod_lt _ (prime _ hd).pos,h⟩,fun w hw => ?_⟩
  exact (Nat.ModEq.cancel_right_of_coprime cop.symm.gcd_eq_one
    (hw.2.trans h.symm)).eq_of_lt_of_lt hw.1 (Nat.mod_lt _ (prime _ hd).pos)

private def dividesF {k : ℕ} (p n : Fin k) : Counting.Formula k :=
  .ex (WidthFormula.mulF p.succ 0 n.succ)

private theorem dividesF_spec {k U : ℕ} (p n : Fin k) (e : Fin k → Fin U)
    (hp : 0<(e p).val) : (dividesF p n).eval e = true ↔ (e p).val ∣ (e n).val := by
  simp only [dividesF,PrimeFormula.exists_true,WidthFormula.mulF_spec,Fin.cases_succ,Fin.cases_zero]
  constructor
  · rintro ⟨q,hq⟩; exact ⟨q,hq.symm⟩
  · rintro ⟨q,hq⟩
    have h := Nat.le_mul_of_pos_left q hp
    rw [←hq] at h
    exact ⟨⟨q,h.trans_lt (e n).isLt⟩,hq.symm⟩

private def repeatedFactor {k : ℕ} (p D : Fin k) : Counting.Formula k :=
  .ex (WidthFormula.andF (WidthFormula.mulF p.succ 0 D.succ) (dividesF p.succ 0))

private theorem repeatedFactor_spec {k U : ℕ} (p D : Fin k) (e : Fin k → Fin U)
    (hp : 0<(e p).val) :
    (repeatedFactor p D).eval e = true ↔ (e p).val*(e p).val ∣ (e D).val := by
  simp only [repeatedFactor, dividesF, PrimeFormula.exists_true,WidthFormula.andF_spec,
    WidthFormula.mulF_spec,Fin.cases_succ,Fin.cases_zero]
  constructor
  · rintro ⟨q,he,z,hz⟩
    exact ⟨z,by rw [←he,←hz,Nat.mul_assoc]⟩
  · rintro ⟨z,hz⟩
    let q := (e p).val*z
    have eq : (e p).val*q = (e D).val := by rw [hz,Nat.mul_assoc]
    have h : q < U := (Nat.le_mul_of_pos_left q hp).trans_lt (eq ▸ (e D).isLt)
    exact ⟨⟨q,h⟩,eq,⟨z,(Nat.le_mul_of_pos_left z hp).trans_lt h⟩,rfl⟩

/-- A numeral D codes an admissible basis if it exceeds the group order and
every prime factor is small, is coprime to the order, and occurs only once. -/
def basisFormula {k : ℕ} (n D K : Fin k) : Counting.Formula k :=
  WidthFormula.andF (PrimeFormula.ltF n D) <| WidthFormula.notF (.ex (WidthFormula.andF (basisMember 0 D.succ)
    (WidthFormula.notF (WidthFormula.andF (PrimeFormula.ltF 0 K.succ)
      (WidthFormula.andF (WidthFormula.notF (dividesF 0 n.succ)) (WidthFormula.notF (repeatedFactor 0 D.succ)))))))

/-- Correctness of the single fixed formula identifying the integer basis code. -/
theorem basisFormula_spec {k U : ℕ} (n D K : Fin k) (e : Fin k → Fin U) :
    (basisFormula n D K).eval e = true ↔
    (e n).val < (e D).val ∧ Squarefree (e D).val ∧
      ∀ p ∈ (e D).val.primeFactors, (e n).val.Coprime p ∧ p<(e K).val := by
  simp only [basisFormula,WidthFormula.andF_spec,PrimeFormula.ltF_true,WidthFormula.notF_spec,
    PrimeFormula.exists_true,Fin.cases_zero,Fin.cases_succ]
  apply and_congr_right
  intro large
  have pos : 0<(e D).val := by omega
  have member (p : Fin U) :
      (basisMember 0 D.succ).eval (Fin.cases p e) = true ↔ p.val ∈ (e D).val.primeFactors := by
    apply basisMember_spec
    simpa only [Fin.cases_succ] using pos
  simp only [member,not_exists,not_and,not_not]
  let good (p : Fin U) := p.val < (e K).val ∧ (¬ p.val ∣ (e n).val) ∧ ¬ p.val*p.val ∣ (e D).val
  have aux (p : Fin U) (mem : p.val ∈ (e D).val.primeFactors) :
      ((p.val < (e K).val ∧ ¬(dividesF 0 n.succ).eval (Fin.cases p e) = true ∧
        (¬(repeatedFactor 0 D.succ).eval (Fin.cases p e) = true))) ↔ good p := by
    have prime := (Nat.mem_primeFactors.mp mem).1
    let en : Fin (k+1) → Fin U := Fin.cases p e
    have posp : 0<(en 0).val := prime.pos
    change (_ ∧ (¬(dividesF 0 n.succ).eval en = true) ∧ ¬(repeatedFactor 0 D.succ).eval en = true) ↔ _
    rw [dividesF_spec 0 n.succ en posp,repeatedFactor_spec 0 D.succ en posp]
    rfl
  constructor
  · intro h
    have allGood (p : ℕ) (mem : p ∈ (e D).val.primeFactors) :
        p < (e K).val ∧ (¬ p ∣ (e n).val) ∧ ¬ p*p ∣ (e D).val := by
      have small := (Nat.le_of_dvd pos (Nat.mem_primeFactors.mp mem).2.1).trans_lt (e D).isLt
      apply (aux ⟨p,small⟩ mem).mp
      have ready := h ⟨p,small⟩ mem
      tauto
    constructor
    · apply Nat.squarefree_iff_prime_squarefree.mpr
      intro p prime dv
      exact (allGood p (Nat.mem_primeFactors.mpr ⟨prime,dvd_trans (dvd_mul_right p p) dv,pos.ne'⟩)).2.2 dv
    · intro p mem
      obtain ⟨small,nodvd,_⟩ := allGood p mem
      exact ⟨((Nat.mem_primeFactors.mp mem).1.coprime_iff_not_dvd.mpr nodvd).symm,small⟩
  · rintro ⟨square,hs⟩ p mem
    have prime := (Nat.mem_primeFactors.mp mem).1
    have ready := (aux p mem).mpr ⟨(hs _ mem).2,prime.coprime_iff_not_dvd.mp (hs _ mem).1.symm,
      Nat.squarefree_iff_prime_squarefree.mp square _ prime⟩
    tauto

/-- The integer basis formula has a witness in a polynomial-size universe.
The witness uses a single domain element and decodes to at most one prime
for each binary digit of the group order. -/
theorem basisFormula_exists {n U : ℕ} (hn : 0<n) (fits : n*primeBound n < U) :
    ∃ e : Fin 3 → Fin U, (e 0).val = n ∧ (e 2).val = primeBound n ∧
      (basisFormula 0 1 2).eval e = true ∧ (e 1).val.primeFactors.card ≤ n.log2+1 := by
  obtain ⟨s,card,lo,hi,hs⟩ := basis_exists n hn
  have hp (p) (mem : p ∈ s) := (hs p mem).1
  have square : Squarefree (modulus s) := Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p mem q hq ne => Nat.coprime_iff_isRelPrime.mp (prime_coprime (hp p mem) (hp q hq) ne))
    (fun p mem => (hp p mem).squarefree)
  let K := primeBound n
  let e : Fin 3 → Fin U := ![⟨n,lo.trans (hi.trans_lt fits)⟩,⟨modulus s,hi.trans_lt fits⟩,
    ⟨K,(Nat.le_mul_of_pos_left K hn).trans_lt fits⟩]
  have primes : (e 1).val.primeFactors = s := basis_code hp
  refine ⟨e,rfl,rfl,(basisFormula_spec 0 1 2 e).mpr ⟨lo,square,?_⟩,primes ▸ card⟩
  intro p mem
  exact (hs p (primes ▸ mem)).2

/-- For a prime in a coded basis, a finite-domain query returns the unique
weight even when the intermediate product f times a modular inverse is too
large for the domain. -/
theorem weightFormula_existsUnique {U D : ℕ} (code : Squarefree D) (fits : D<U)
    (d f : Fin U) (mem : d.val ∈ D.primeFactors) (A : ℕ → ℕ → Bool) :
    ∃! w : Fin U, (weightFormula 0 1 2 3).eval (fun i j => A i.val j.val)
      (![⟨D,fits⟩,d,f,w] : Fin 4 → Fin U) = true := by
  have decodes : modulus D.primeFactors = D := Nat.prod_primeFactors_of_squarefree code
  have ⟨w,valid,unique⟩ := unique_weight
    (fun p (hp : p ∈ D.primeFactors) => (Nat.mem_primeFactors.mp hp).1) mem f.val
  rw [decodes] at valid unique
  have hd := Nat.mem_primeFactors.mp mem
  let e (z : Fin U) : Fin 4 → Fin U := ![⟨D,fits⟩,d,f,z]
  have spec (z : Fin U) := weightFormula_spec 0 1 2 3 (e z) A hd.1.pos hd.2.1
  exact ⟨⟨w,valid.1.trans d.isLt⟩,(spec _).mpr valid,
    fun z hz => Fin.ext (unique z.val ((spec z).mp hz))⟩

end DiophantineNP.HABGroupPower
