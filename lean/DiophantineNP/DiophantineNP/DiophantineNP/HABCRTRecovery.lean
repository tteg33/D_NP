import DiophantineNP.ShortResidue
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.FieldTheory.Finite.Basic

/-! # Comparing Chinese remainder representations by truncated reciprocals

Hesse, Allender and Barrington, §§4.2–4.5. A common upward correction
makes the fractional-part comparison valid even at zero and at dyadic
boundaries. The comparison word uses short CRT coefficients and bits of
the reciprocals. The long product of the moduli occurs in its proof only.
-/

namespace DiophantineNP.HABCRTRecovery
open scoped BigOperators

def modulus (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

def cofactor (s : Finset ℕ) (p : ℕ) : ℕ := modulus (s.erase p)

theorem factor_modulus {s : Finset ℕ} {p : ℕ} (hp : p ∈ s) :
    p * cofactor s p = modulus s :=
  Finset.mul_prod_erase s (fun i => i) hp

/-- The scaled sum uses just truncated reciprocals, with no full-modulus product. -/
def approx (s : Finset ℕ) (d : ℕ) (c : ℕ → ℕ) : ℕ :=
  ∑ p ∈ s, c p * (d/p)

def exactSum (s : Finset ℕ) (c : ℕ → ℕ) : ℕ :=
  ∑ p ∈ s, c p * cofactor s p

/-- When d=2^L, this is the low L bits of the corrected sum. -/
def word (s : Finset ℕ) (d h : ℕ) (c : ℕ → ℕ) : ℕ :=
  (approx s d c + h) % d

private theorem enclosure {s : Finset ℕ} {d : ℕ} {c : ℕ → ℕ} (pos : ∀ p ∈ s, 0<p) :
    approx s d c * modulus s ≤ exactSum s c * d ∧
    exactSum s c * d ≤ (approx s d c + ∑ p ∈ s,c p) * modulus s := by
  constructor
  · unfold approx exactSum
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    rw [← factor_modulus hp]
    calc c p * (d/p) * (p * cofactor s p)
        = c p * cofactor s p * ((d/p) * p) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.div_mul_le_self ..)
  · unfold approx exactSum
    rw [← Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    rw [← factor_modulus hp]
    calc c p * cofactor s p * d
        ≤ c p * cofactor s p * (p * (d/p+1)) :=
            Nat.mul_le_mul_left _ (Nat.lt_mul_div_succ d (pos p hp)).le
      _ = _ := by ring

/-- An exact integer readout from a common precision, including when the
canonical result is zero. It applies to any family of coefficients. -/
theorem word_readout {s : Finset ℕ} {d h : ℕ} {c : ℕ → ℕ}
    (pos : ∀ p ∈ s, 0<p) (hs : ∑ p ∈ s,c p ≤ h) (hd : modulus s * h < d) :
    word s d h c * modulus s / d = exactSum s c % modulus s := by
  let a := approx s d c
  let t := exactSum s c
  let m := modulus s
  have dm : 0 < d := Nat.zero_le _ |>.trans_lt hd
  have hm : 0 < m := Finset.prod_pos pos
  obtain ⟨lo,hi⟩ := enclosure (d:=d) (c:=c) pos
  have lower : t*d ≤ (a+h)*m := hi.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_left hs _))
  have upper : (a+h)*m < (t+1)*d := by
    calc (a+h)*m = a*m+m*h := by ring
         _ < t*d+d := Nat.add_lt_add_of_le_of_lt lo hd
         _ = _ := by ring
  have e : (a+h)*m/d = t := Nat.le_antisymm ((Nat.div_lt_iff_lt_mul dm).mpr upper |> Nat.le_of_lt_succ)
    ((Nat.le_div_iff_mul_le dm).mpr lower)
  have hdiv : (a+h)%d*m/d < m := (Nat.div_lt_iff_lt_mul dm).mpr (by
    rw [Nat.mul_comm m]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ dm) hm)
  have decomp : (a+h)*m = ((a+h)%d)*m + d*((a+h)/d*m) := by
    conv_lhs => rw [← Nat.mod_add_div (a+h) d]
    ring
  change (a+h)%d*m/d = t % m
  rw [←e, decomp, Nat.add_mul_div_left _ _ dm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hdiv]

/-- The standard CRT coefficients, reduced at each modulus. -/
def coeff (inv : ℕ → ℕ) (x p : ℕ) : ℕ := (x%p * inv p)%p

private theorem eq_at_factor {s : Finset ℕ} {x : ℕ} {inv : ℕ → ℕ}
    (hinv : ∀ p ∈ s, cofactor s p * inv p ≡ 1 [MOD p]) {p : ℕ} (hp : p ∈ s) :
    exactSum s (coeff inv x) ≡ x [MOD p] := by
  rw [exactSum,← Finset.add_sum_erase _ _ hp]
  have htail : p ∣ ∑ q ∈ s.erase p, coeff inv x q * cofactor s q := by
    apply Finset.dvd_sum
    intro q hq
    apply dvd_mul_of_dvd_right
    exact Finset.dvd_prod_of_mem (fun i => i) (Finset.mem_erase.mpr
      ⟨(Finset.ne_of_mem_erase hq).symm,hp⟩ : p ∈ s.erase q)
  have good : coeff inv x p * cofactor s p ≡ x [MOD p] := by
    unfold coeff
    calc
      (x%p * inv p)%p * cofactor s p ≡ x * inv p * cofactor s p [MOD p] :=
        ((Nat.mod_modEq ..).trans ((Nat.mod_modEq ..).mul_right _)).mul_right _
      _ = x * (cofactor s p * inv p) := by ring
      _ ≡ x * 1 [MOD p] := (hinv p hp).mul_left x
      _ = x := Nat.mul_one _
  simpa using good.add (Nat.modEq_zero_iff_dvd.mpr htail)

private theorem eq_at_product {s : Finset ℕ} {a b : ℕ} (primes : ∀ p ∈ s, Nat.Prime p)
    (localEq : ∀ p ∈ s, a ≡ b [MOD p]) : a ≡ b [MOD modulus s] := by
  induction s using Finset.induction_on with
  | empty => simp [modulus, Nat.modEq_one]
  | @insert p s hp ih =>
    have hs : ∀ q ∈ s, Nat.Prime q := fun _ h => primes _ (Finset.mem_insert_of_mem h)
    have pp := primes p (Finset.mem_insert_self ..)
    have hc : p.Coprime (modulus s) := Nat.coprime_prod_right_iff.mpr (by
      intro q hq
      exact (Nat.coprime_primes pp (hs q hq)).mpr (by rintro rfl; exact hp hq))
    rw [modulus, Finset.prod_insert hp]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hc).mp
      ⟨localEq p (Finset.mem_insert_self ..),ih hs (fun _ h => localEq _ (Finset.mem_insert_of_mem h))⟩

/-- Uniform precision bound for all residue vectors on this basis. -/
def budget (s : Finset ℕ) : ℕ := ∑ p ∈ s,p

theorem crt_readout {s : Finset ℕ} {inv : ℕ → ℕ} {x d : ℕ}
    (primes : ∀ p ∈ s, Nat.Prime p)
    (hinv : ∀ p ∈ s, cofactor s p * inv p ≡ 1 [MOD p])
    (hx : x < modulus s) (hd : modulus s * budget s < d) :
    word s d (budget s) (coeff inv x) * modulus s / d = x := by
  have cap : ∑ p ∈ s, coeff inv x p ≤ budget s :=
    Finset.sum_le_sum (fun p hp => (Nat.mod_lt _ (primes p hp).pos).le)
  rw [word_readout (fun p hp => (primes p hp).pos) cap hd]
  calc exactSum s (coeff inv x) % modulus s = x % modulus s :=
         eq_at_product primes (fun _ hp => eq_at_factor hinv hp)
       _ = x := Nat.mod_eq_of_lt hx

/-- Comparing two integers in the basis requires only comparing their low
bits of the corrected sums. No multiplication by the full modulus is used
in the word being compared. -/
theorem compare_crt {s : Finset ℕ} {inv : ℕ → ℕ} {x y d : ℕ}
    (primes : ∀ p ∈ s, Nat.Prime p)
    (hinv : ∀ p ∈ s, cofactor s p * inv p ≡ 1 [MOD p])
    (hx : x < modulus s) (hy : y < modulus s) (hd : modulus s * budget s < d) :
    x < y ↔ word s d (budget s) (coeff inv x) < word s d (budget s) (coeff inv y) := by
  have mono {i j : ℕ} (hi : i < modulus s) (hj : j < modulus s)
      (h : word s d (budget s) (coeff inv i) ≤ word s d (budget s) (coeff inv j)) : i ≤ j := by
    rw [← crt_readout primes hinv hi hd, ← crt_readout primes hinv hj hd]
    exact Nat.div_le_div_right (Nat.mul_le_mul_right _ h)
  constructor
  · intro h; by_contra! h'; exact h.not_ge (mono hy hx h')
  · intro h
    by_contra! h'
    have he := Nat.le_antisymm (mono hx hy h.le) h'
    subst y
    exact lt_irrefl _ h

/-- The local inverse exists and has a canonical short representative. -/
def inverse (s : Finset ℕ) (p : ℕ) : ℕ := (cofactor s p % p)^(p-2)%p

theorem inverse_spec {s : Finset ℕ} (primes : ∀ p ∈ s, Nat.Prime p) {p : ℕ} (hp : p ∈ s) :
    cofactor s p * inverse s p ≡ 1 [MOD p] := by
  have pp := primes p hp
  have hcop : (cofactor s p).Coprime p := Nat.coprime_prod_left_iff.mpr (by
    intro q hq
    exact (Nat.coprime_primes (primes q (Finset.mem_of_mem_erase hq)) pp).mpr
      (Finset.ne_of_mem_erase hq))
  have e := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime pp,show p-1=p-2+1 by have := pp.two_le; omega,pow_succ'] at e
  exact (((Nat.mod_modEq ..).trans ((Nat.mod_modEq ..).pow (p-2))).mul_left _).trans e

/-- A precision exponent polynomial in the number of moduli and their bit bound. -/
theorem precision {s : Finset ℕ} {b : ℕ} (small : ∀ p ∈ s, p ≤ 2^b) :
    modulus s * budget s < 2^(b*s.card+b+s.card+1) := by
  have hm : modulus s ≤ (2^b)^s.card := by
    simpa [modulus] using Finset.prod_le_prod' small
  have hh : budget s ≤ s.card * 2^b := by
    simpa [budget] using Finset.sum_le_sum small
  have hc : s.card ≤ 2^s.card := (Nat.lt_two_pow_self).le
  calc modulus s * budget s ≤ (2^b)^s.card * (2^s.card * 2^b) :=
        Nat.mul_le_mul hm (hh.trans (Nat.mul_le_mul_right _ hc))
       _ = 2^(b*s.card+b+s.card) := by rw [pow_add,pow_add,pow_mul]; ring
       _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

theorem compare_with_precision {s : Finset ℕ} {x y b : ℕ}
    (primes : ∀ p ∈ s, Nat.Prime p) (small : ∀ p ∈ s, p ≤ 2^b)
    (hx : x < modulus s) (hy : y < modulus s) :
    let d := 2^(b*s.card+b+s.card+1)
    let approxWord (v : ℕ) := word s d (budget s) (coeff (inverse s) v)
    x < y ↔ approxWord x < approxWord y :=
  compare_crt primes (fun _ hp => inverse_spec primes hp) hx hy (precision small)

/-- A comparison word expressed purely in terms of a vector of residues. -/
def residueWord (s : Finset ℕ) (d : ℕ) (inv residues : ℕ → ℕ) : ℕ :=
  word s d (budget s) (fun p => (residues p * inv p)%p)

private theorem agree_word {s : Finset ℕ} {r inv : ℕ → ℕ} {x d : ℕ}
    (h : ∀ p ∈ s, r p = x%p) :
    residueWord s d inv r = word s d (budget s) (coeff inv x) := by
  unfold residueWord word approx
  congr 2
  exact Finset.sum_congr rfl (fun p hp => by simp only [h p hp,coeff])

/-- On an enlarged CRT basis compare each proposed new residue with
the boundary M. Exactly the true candidate is below it (HAB Lemma 4.4).
The boundary has zero residues on the old primes and residue M mod q
at the new prime. Both comparison inputs consist of these short fields. -/
theorem extend_basis {s : Finset ℕ} {q x d t : ℕ} {input inv : ℕ → ℕ}
    (primes : ∀ p ∈ s, Nat.Prime p) (hq : q.Prime) (fresh : q ∉ s)
    (hx : x<modulus s) (ht : t<q) (hinput : ∀ p ∈ s, input p=x%p)
    (hinv : ∀ p ∈ insert q s, cofactor (insert q s) p * inv p ≡ 1 [MOD p])
    (hd : modulus (insert q s)*budget (insert q s)<d) :
    residueWord (insert q s) d inv (fun p => if p=q then t else input p) <
      residueWord (insert q s) d inv (fun p => if p=q then modulus s%q else 0) ↔ t=x%q := by
  let m := modulus s
  have hc : m.Coprime q := Nat.coprime_prod_left_iff.mpr (by
    intro p hp; exact (Nat.coprime_primes (primes p hp) hq).mpr (by rintro rfl; exact fresh hp))
  have hm : 0<m := Finset.prod_pos (fun p hp => (primes p hp).pos)
  have hpr : ∀ p ∈ insert q s, Nat.Prime p := by simpa using And.intro hq primes
  have big : modulus (insert q s) = m*q := by rw [modulus,Finset.prod_insert fresh,Nat.mul_comm]; rfl
  let z := Nat.chineseRemainder hc x t
  have hz : z.val < modulus (insert q s) := big ▸ Nat.chineseRemainder_lt_mul hc x t hm.ne' hq.ne_zero
  have hboundary : m < modulus (insert q s) := by
    rw [big]; simpa using Nat.mul_lt_mul_of_pos_left hq.one_lt hm
  have candidate : ∀ p ∈ insert q s, (if p=q then t else input p) = z.val%p := by
    intro p hp
    by_cases e : p=q
    · subst p; rw [if_pos rfl]; exact (Nat.mod_eq_of_lt ht).symm.trans (show t%q=z.val%q from z.property.2.symm)
    · have hp' := (Finset.mem_insert.mp hp).resolve_left e
      exact (if_neg e).trans ((hinput p hp').trans
        ((z.property.1.of_dvd (Finset.dvd_prod_of_mem (fun i => i) hp')).symm : x%p=z.val%p))
  have boundary : ∀ p ∈ insert q s, (if p=q then modulus s%q else 0) = m%p := by
    intro p hp
    by_cases e : p=q
    · subst p; simp [m]
    · exact (if_neg e).trans (Nat.mod_eq_zero_of_dvd (Finset.dvd_prod_of_mem (fun i => i) ((Finset.mem_insert.mp hp).resolve_left e))).symm
  rw [agree_word candidate,agree_word boundary,← compare_crt hpr hinv hz hboundary hd]
  constructor
  · intro h
    have e : z.val=x := z.property.1.eq_of_lt_of_lt h hx
    have hzt : z.val%q=t%q := z.property.2
    rw [e,Nat.mod_eq_of_lt ht] at hzt
    exact hzt.symm
  · intro h
    have xq : x ≡ t [MOD q] := by change x%q=t%q; rw [Nat.mod_eq_of_lt ht,h]
    have e : x = z.val := (Nat.chineseRemainder_modEq_unique hc (Nat.ModEq.refl x) xq).eq_of_lt_of_lt
      (by rw [← big]; exact hx.trans hboundary) (by rw [←big]; exact hz)
    simpa [←e] using hx

/-- For an odd denominator, parity of a power-of-two remainder supplies the
corresponding fractional binary digit. At position zero this rule differs,
hence the strict positivity hypothesis. -/
theorem reciprocal_parity {p s : ℕ} (odd : p%2=1) (hs : 0<s) :
    (2^s/p)%2 = (2^s%p)%2 := by
  have h := congrArg (fun t : ℕ => t%2) (Nat.div_add_mod (2^s) p)
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  simp only [Nat.add_mod, Nat.mul_mod p, odd, Nat.one_mul, Nat.mod_mod,
    pow_succ, Nat.mul_mod_left] at h
  rw [pow_succ]
  omega

open Counting WidthFormula PrimeFormula FiniteArithmeticGap

private def oddF {k : ℕ} (x : Fin k) : Formula k := notF (.ex (addF 0 0 x.succ))

private theorem oddF_true {k U : ℕ} (x : Fin k) (env : Fin k → Fin U) :
    (oddF x).eval env = true ↔ (env x).val%2=1 := by
  simp only [oddF,notF_spec,exists_true,addF_spec,Fin.cases_zero,Fin.cases_succ]
  constructor
  · intro h
    by_contra! hn
    exact h ⟨⟨(env x).val/2,(Nat.div_le_self ..).trans_lt (env x).isLt⟩,by
      change (env x).val/2 + (env x).val/2 = (env x).val; omega⟩
  · rintro h ⟨d,hd⟩
    omega

/-- The source of the modular-power predicate can be replaced before a
universe is chosen. No long-integer multiplication is present. -/
def reciprocalWith (power : {j : ℕ} → Fin j → Fin j → Fin j → Fin j → Formula j)
    {k : ℕ} (s p : Fin k) : Formula k :=
  .ex (andF (isNat 2 0) (.ex (andF (power (0 : Fin (k+1)).succ (up2 s) (up2 p) 0) (oddF 0))))

theorem reciprocalWith_correct
    (power : {j : ℕ} → Fin j → Fin j → Fin j → Fin j → Formula j)
    {k U : ℕ} (s p : Fin k) (env : Fin k → Fin U)
    (hp : 2<(env p).val) (ho : (env p).val%2=1) (hs : 0<(env s).val)
    (powOK : ∀ (a r : Fin U), a.val=2 →
      ((power (0 : Fin (k+1)).succ (up2 s) (up2 p) 0).eval
        (Fin.cases r (Fin.cases a env)) = true ↔ r.val=2^(env s).val%(env p).val)) :
    (reciprocalWith @power s p).eval env = true ↔ (2^(env s).val/(env p).val)%2=1 := by
  rw [reciprocal_parity ho hs]
  simp only [reciprocalWith,exists_true,andF_spec,isNat_spec,oddF_true,Fin.cases_zero]
  constructor
  · rintro ⟨a,ha,r,hr,hor⟩
    rwa [← (powOK a r ha).mp hr]
  · intro h
    let a : Fin U := ⟨2,hp.trans (env p).isLt⟩
    let r : Fin U := ⟨_,(Nat.mod_lt (2^(env s).val) (by omega : 0<(env p).val)).trans (env p).isLt⟩
    exact ⟨a,rfl,r,(powOK a r rfl).mpr rfl,h⟩

/-- An actual fixed formula, with no arithmetic oracle, for the short
operands that fit in the project's packed repeated-squaring tableau. -/
def reciprocalDigit {k : ℕ} (s p : Fin k) : Formula k := reciprocalWith @ShortPower.formula s p

theorem reciprocalDigit_correct {k U K : ℕ} (s p : Fin k) (env : Fin k → Fin U)
    (hp : 2<(env p).val) (ho : (env p).val%2=1) (hs : 0<(env s).val)
    (hK : 2≤K) (he : (env s).val<2^K) (hpK : (env p).val≤2^K) (hcap : 2^((K+1)*K)<U) :
    (reciprocalDigit s p).eval env = true ↔ (2^(env s).val/(env p).val)%2=1 := by
  apply reciprocalWith_correct _ _ _ _ hp ho hs
  intro a r ha
  let e : Fin (k+2) → Fin U := Fin.cases r (Fin.cases a env)
  have ea : (e (0 : Fin (k+1)).succ).val = 2 := by simpa only [e,Fin.cases_succ,Fin.cases_zero] using ha
  have ep : e (up2 p) = env p := by simp only [e,up2,Fin.cases_succ]
  have es : e (up2 s) = env s := by simp only [e,up2,Fin.cases_succ]
  have er : e 0 = r := rfl
  simpa only [ea,ep,es,er] using ShortPower.formula_correct (0 : Fin (k+1)).succ
    (up2 s) (up2 p) 0 e hK (by rw [ea,ep]; exact hp) (by rw [ep]; omega)
    (by rw [es]; exact he) (by rw [ep]; exact hpK) hcap

/-- The j-th bit of the scaled reciprocal equals the (l−j)-th fractional
digit. At j ≥ l it is zero for every denominator greater than one. -/
theorem scaled_reciprocal_bit {l j p : ℕ} (hp : 1<p) :
    (2^l/p).testBit j = true ↔ j<l ∧ (2^(l-j)/p)%2=1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq,decide_eq_true_eq]
  by_cases hj : j<l
  · rw [and_iff_right hj,Nat.div_div_eq_div_mul,Nat.mul_comm p,←Nat.div_div_eq_div_mul]
    have e : 2^l = 2^(l-j)*2^j := by rw [←pow_add]; congr 1; omega
    rw [e, Nat.mul_div_cancel _ (Nat.two_pow_pos j)]
  · have hlt : 2^l/p < 2^j := (Nat.div_lt_self (Nat.two_pow_pos _) hp).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    simp [hj,Nat.div_eq_of_lt hlt]

/-- One arithmetic formula for a bit of floor(2^l/p) for an odd short p.
The position is measured from the low bit, as in the iterated-sum template. -/
def scaledBit {k : ℕ} (l j p : Fin k) : Formula k :=
  andF (ltF j l) (.ex (andF (addF j.succ 0 l.succ) (reciprocalDigit 0 p.succ)))

theorem scaledBit_correct {k U K : ℕ} (l j p : Fin k) (env : Fin k → Fin U)
    (hp : 2<(env p).val) (ho : (env p).val%2=1) (hK : 2≤K)
    (he : (env l).val-(env j).val<2^K) (hpK : (env p).val≤2^K)
    (hcap : 2^((K+1)*K)<U) :
    (scaledBit l j p).eval env = (2^(env l).val/(env p).val).testBit (env j).val := by
  apply Bool.eq_iff_iff.mpr
  simp only [scaledBit,andF_spec,ltF_true,exists_true,addF_spec,Fin.cases_zero,Fin.cases_succ,
    scaled_reciprocal_bit (lt_trans (by decide : 1<2) hp)]
  constructor
  · rintro ⟨hj,z,hz,h⟩
    have ez : z.val=(env l).val-(env j).val := by omega
    refine ⟨hj,?_⟩
    have := (reciprocalDigit_correct (K:=K) 0 p.succ (Fin.cases z env)
      (by simpa only [Fin.cases_succ] using hp) (by simpa only [Fin.cases_succ] using ho)
      (by simpa only [Fin.cases_zero] using (by omega : 0<z.val)) hK
      (by simpa only [Fin.cases_zero,ez] using he) (by simpa only [Fin.cases_succ] using hpK) hcap).mp h
    simpa only [Fin.cases_zero,Fin.cases_succ,ez] using this
  · rintro ⟨hj,h⟩
    let z : Fin U := ⟨(env l).val-(env j).val,(Nat.sub_le ..).trans_lt (env l).isLt⟩
    refine ⟨hj,z,by dsimp [z]; omega,?_⟩
    apply (reciprocalDigit_correct (K:=K) 0 p.succ (Fin.cases z env) (by simpa only [Fin.cases_succ] using hp)
      (by simpa only [Fin.cases_succ] using ho) (by simpa only [Fin.cases_zero,z] using (Nat.sub_pos_of_lt hj)) hK
      (by simpa only [Fin.cases_zero,z] using he) (by simpa only [Fin.cases_succ] using hpK) hcap).mpr
    simpa only [Fin.cases_zero,Fin.cases_succ,z] using h

open ShortResidue


/-- The five free variables are B mod p, the proposed quotient residue,
(X mod B) mod p, p, and X mod p. The four bound variables hold the
two sides of the congruence as ordinary, nonnegative integers. -/
private def quotientFieldP : Predicate :=
  Predicate.ex 5 ((Predicate.mul 0 1 5).both (Predicate.ex 6
    ((Predicate.add 5 2 6).both (Predicate.ex 7 (Predicate.ex 8
      ((Predicate.mul 3 7 8).both (Predicate.add 8 4 6)))))))

private def quotientFieldNames {k : ℕ} (b t r p x : Fin k) : ℕ → Fin k :=
  fun i => if i=0 then b else if i=1 then t else if i=2 then r else if i=3 then p else x

/-- Fixed field-level test for a quotient digit from three known residues. -/
def quotientField {k : ℕ} (b t r p x : Fin k) : Template k :=
  quotientFieldP.syntaxF (quotientFieldNames b t r p x)

private theorem field_semantics {U : ℕ} (e : ℕ → ℕ) (hx : e 4 < e 3)
    (hsize : e 0 * e 1 + e 2 < U) :
    quotientFieldP.holds U (fun _ _ => false) e ↔ (e 0 * e 1 + e 2)%e 3 = e 4 := by
  simp only [quotientFieldP,Predicate.ex,Predicate.both,Predicate.mul,Predicate.add]
  simp [Function.update]
  constructor
  · rintro ⟨_,_,q,_,_,h⟩
    rw [←h,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hx]
  · intro H
    let v := e 0*e 1+e 2
    let q := v/e 3
    have wv : e 0*e 1 ≤ v := Nat.le_add_right .. 
    have qv : q ≤ v := Nat.div_le_self ..
    have pv : e 3*q ≤ v := Nat.mul_div_le v (e 3)
    have hq : e 3*q + e 4 = v := by rw [←H]; exact Nat.div_add_mod .. 
    exact ⟨wv.trans_lt hsize,hsize,q,qv.trans_lt hsize,pv.trans_lt hsize,hq⟩

/-- The actual field test in HAB Lemma 4.5. If B is coprime to p, test a
proposed quotient digit by a fixed formula on short data. The capacity
condition ensures intermediate products and sums are in the universe. -/
theorem quotientField_spec {U k X B : ℕ} (b t r p x : Fin k) (e : Fin k → Fin U)
    (hp : 0<(e p).val) (cop : (e p).val.Coprime B) (hb : (e b).val=B%(e p).val)
    (hr : (e r).val=(X%B)%(e p).val) (hx : (e x).val=X%(e p).val)
    (ht : (e t).val<(e p).val) (cap : (e b).val*(e t).val+(e r).val<U) :
    (quotientField b t r p x).eval (fun _ _ => false) e=true ↔ (e t).val=(X/B)%(e p).val := by
  let σ := quotientFieldNames b t r p x
  let z := fun i => (e (σ i)).val
  have A := field_semantics z
    (by simpa [z,σ,quotientFieldNames,hx] using Nat.mod_lt X hp) (by simpa [z,σ,quotientFieldNames] using cap)
  rw [quotientField,Predicate.valid _ _ (fun _ _ => false)]
  have hlocal : quotientFieldP.holds U (fun _ _ => false) z ↔
      ((e b).val*(e t).val+(e r).val)%(e p).val=(e x).val := by
    simpa [z,σ,quotientFieldNames] using A
  rw [hlocal,hb,hr,hx]
  let n := (e p).val
  have hred : B%n*(e t).val+((X%B)%n) ≡ B*(e t).val+(X%B) [MOD n] :=
    ((Nat.mod_modEq B n).mul_right _).add (Nat.mod_modEq _ _)
  rw [show (B % (e p).val * (e t).val + X % B % (e p).val) % (e p).val =
    (B * (e t).val + X%B)%(e p).val from hred]
  change B*(e t).val + X%B ≡ X [MOD (e p).val] ↔ _
  have exa : B*(X/B) + X%B = X := Nat.div_add_mod .. 
  constructor
  · intro h
    have hq : (e t).val ≡ X/B [MOD (e p).val] := Nat.ModEq.cancel_left_of_coprime cop
      (Nat.ModEq.add_right_cancel' _ (h.trans (congrArg (· % (e p).val) exa.symm)))
    exact (Nat.mod_eq_of_lt ht).symm.trans hq
  · intro h
    have hq : (e t).val ≡ X/B [MOD (e p).val] := by rw [h]; exact Nat.mod_modEq ..
    exact ((hq.mul_left B).add_right (X%B)).trans (congrArg (· % (e p).val) exa)

/-- A single universe bound suffices for every candidate below the modulus. -/
theorem quotientField_of_square_le {U k X B : ℕ} (b t r p x : Fin k) (e : Fin k → Fin U)
    (hp : 0 < (e p).val) (cop : (e p).val.Coprime B) (hb : (e b).val = B % (e p).val)
    (hr : (e r).val = (X % B) % (e p).val) (hx : (e x).val = X % (e p).val)
    (ht : (e t).val < (e p).val) (cap : (e p).val ^ 2 ≤ U) :
    (quotientField b t r p x).eval (fun _ _ => false) e = true ↔
      (e t).val = (X / B) % (e p).val := by
  apply quotientField_spec b t r p x e hp cop hb hr hx ht
  have hbr : (e b).val < (e p).val := hb ▸ Nat.mod_lt _ hp
  have hrr : (e r).val < (e p).val := hr ▸ Nat.mod_lt _ hp
  calc
    (e b).val * (e t).val + (e r).val < (e b).val * (e p).val + (e p).val :=
      Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left _ ht.le) hrr
    _ = ((e b).val + 1) * (e p).val := (Nat.succ_mul ..).symm
    _ ≤ (e p).val ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hbr
    _ ≤ U := cap

end DiophantineNP.HABCRTRecovery
