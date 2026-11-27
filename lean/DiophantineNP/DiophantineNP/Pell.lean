import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Pell indices in the power graph

The recurrence and the congruences are over the integers. Its index and
the exponents of powers are natural numbers. The cap on the Pell solution
appears as an input to the index-selection argument. The elliptic windows
in `PowerTests.lean` enforce the cap in the power graph.
-/

namespace DiophantineNP.Pell

/-- Two consecutive values `(Uⱼ, Uⱼ₊₁)` of the draft's recurrence. -/
def pair (C : ℤ) : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | j + 1 => let p := pair C j; (p.2, C * p.2 - p.1)

def Admissible (C s t : ℤ) : Prop :=
  0 ≤ s ∧ s < t ∧ s ^ 2 - C * s * t + t ^ 2 = 1

theorem pair_admissible {C : ℤ} (hC : 4 ≤ C) (j : ℕ) :
    Admissible C (pair C j).1 (pair C j).2 := by
  induction j with
  | zero => norm_num [pair, Admissible]
  | succ j ih =>
    obtain ⟨hs, hst, heq⟩ := ih
    change 0 ≤ (pair C j).2 ∧ _ ∧ _
    refine ⟨by omega, ?_, ?_⟩
    · change (pair C j).2 < C * (pair C j).2 - (pair C j).1
      nlinarith [mul_nonneg (show 0 ≤ C - 4 by omega)
        (show 0 ≤ (pair C j).2 by omega)]
    · change (pair C j).2 ^ 2 - C * (pair C j).2 *
          (C * (pair C j).2 - (pair C j).1) +
          (C * (pair C j).2 - (pair C j).1) ^ 2 = 1
      linarith only [heq]

/-- Every nonnegative ordered solution arises from the recurrence. -/
theorem exists_index {C s t : ℤ} (h : Admissible C s t) :
    ∃ j : ℕ, pair C j = (s, t) := by
  obtain ⟨hs, hst, heq⟩ := h
  generalize hk : s.toNat = k
  induction k using Nat.strong_induction_on generalizing s t with
  | h k ih =>
    by_cases hz : s = 0
    · subst s
      simp at heq
      have ht : t = 1 := by omega
      subst t
      exact ⟨0, rfl⟩
    · have hspos : 0 < s := by omega
      have htpos : 0 < t := by omega
      let u := C * s - t
      have hu_eq : u * t = s ^ 2 - 1 := by
        dsimp [u]
        linarith only [heq]
      have hu : 0 ≤ u := by
        by_contra! hu
        have : u * t < 0 := mul_neg_of_neg_of_pos hu htpos
        nlinarith [sq_nonneg (s - 1)]
      have hus : u < s := by
        refine lt_of_mul_lt_mul_right (a := t) ?_ htpos.le
        nlinarith [mul_lt_mul_of_pos_left hst hspos]
      have hup : u ^ 2 - C * u * s + s ^ 2 = 1 := by
        dsimp [u]
        linarith only [heq]
      obtain ⟨j, hj⟩ := ih u.toNat (by omega) (s := u) (t := s) hu hus hup rfl
      refine ⟨j+1, ?_⟩
      simp [pair, hj, u]

theorem index_modEq (C : ℤ) (j : ℕ) :
    (pair C j).1 ≡ (j : ℤ) [ZMOD C - 2] ∧
    (pair C j).2 ≡ ((j : ℤ) + 1) [ZMOD C - 2] := by
  induction j with
  | zero => simp [pair]
  | succ j ih =>
    obtain ⟨h₁, h₂⟩ := ih
    simp only [pair, Nat.cast_succ]
    refine ⟨h₂, ?_⟩
    have hC : C ≡ 2 [ZMOD C - 2] := Int.modEq_sub C 2
    have hr := (hC.mul h₂).sub h₁
    convert hr using 1; ring

theorem growth {C : ℤ} (hC : 4 ≤ C) (j : ℕ) :
    (C - 1)^j ≤ (pair C j).2 ∧ (pair C j).2 ≤ C^j := by
  induction j with
  | zero => simp [pair]
  | succ j ih =>
    obtain ⟨hs, hst, _⟩ := pair_admissible hC j
    obtain ⟨hl, hu⟩ := ih
    simp only [pair, pow_succ]
    constructor
    · have h := mul_le_mul_of_nonneg_right hl (show 0 ≤ C - 1 by omega)
      linarith only [h, hst]
    · have h := mul_le_mul_of_nonneg_right hu (show 0 ≤ C by omega)
      linarith only [h, hs]

/-- One recurrence step multiplies the represented residue by the base. -/
theorem power_modEq (A g : ℤ) (j : ℕ) :
    (pair A j).2 + (g-A) * (pair A j).1 ≡ g^j [ZMOD A*g-g^2-1] := by
  induction j with
  | zero => simp [pair]
  | succ j ih =>
    rw [pow_succ' g j]
    refine Int.ModEq.trans ?_ (ih.mul_left g)
    apply Int.modEq_iff_dvd.2
    refine ⟨-(pair A j).1, ?_⟩
    simp only [pair]
    ring

private theorem residue_eq_of_range {m a b : ℤ}
    (hab : a ≡ b [ZMOD m]) (ha : 0 ≤ a) (ham : a < m) (hb : 0 ≤ b) (hbm : b < m) :
    a = b := by
  simpa only [Int.emod_eq_of_lt ha ham, Int.emod_eq_of_lt hb hbm] using hab.eq

/-- A solution below the exponential cap has exactly the prescribed index. -/
theorem select_index {A s t : ℤ} {e T : ℕ} (hA : 4 ≤ A)
    (h : Admissible A s t) (hmod : s ≡ (e : ℤ) [ZMOD A-2])
    (he : (e : ℤ) < A-2) (hT : (T : ℤ) ≤ A-2) (hcap : t < (2 : ℤ)^T) :
    pair A e = (s,t) := by
  obtain ⟨j, hj⟩ := exists_index h
  obtain ⟨hl, _⟩ := growth hA j
  have hbase : (2 : ℤ)^j ≤ (A-1)^j :=
    pow_le_pow_left₀ (by decide) (by omega) _
  rw [hj] at hl
  have hjT : j < T := by
    by_contra! hTj
    have hpow : (2 : ℤ)^T ≤ 2^j := pow_le_pow_right₀ (by decide) hTj
    change (A-1)^j ≤ t at hl
    omega
  have hres := (index_modEq A j).1
  rw [hj] at hres
  have hje : (j : ℤ) = (e : ℤ) :=
    residue_eq_of_range (hres.symm.trans hmod) (by positivity)
      (by omega) (by positivity) he
  have : j = e := by exact_mod_cast hje
  simpa only [this] using hj

/-- The second Pell pair gives the exact power once the modulus exceeds
both candidate values. The first Pell pair in the draft ensures this size. -/
theorem bounded_power_sound {A g y s t : ℤ} {e T : ℕ}
    (hA : 4 ≤ A) (h : Admissible A s t)
    (hmod : s ≡ (e : ℤ) [ZMOD A-2]) (he : (e : ℤ) < A-2)
    (hT : (T : ℤ) ≤ A-2) (hcap : t < (2 : ℤ)^T)
    (hy : 0 ≤ y) (hg : 0 ≤ g)
    (hylt : y < A*g-g^2-1) (hplt : g^e < A*g-g^2-1)
    (hout : y ≡ t + (g-A)*s [ZMOD A*g-g^2-1]) : y = g^e := by
  have hpower := power_modEq A g e
  rw [select_index hA h hmod he hT hcap] at hpower
  exact residue_eq_of_range (hout.trans hpower) hy hylt (pow_nonneg hg e) hplt


/-- The first Pell congruence gives a lower bound even if the witness uses
a later representative of the exponent class. -/
theorem first_pair_lower {c g s t : ℤ} {e : ℕ}
    (hc : 4 ≤ c) (hg : 1 ≤ g) (hgc : g ≤ c-1) (he : (e : ℤ) < c-2)
    (h : Admissible c s t) (hs : s ≡ (e : ℤ) [ZMOD c-2]) :
    g^e ≤ t := by
  obtain ⟨j, hj⟩ := exists_index h
  have hres := (index_modEq c j).1
  rw [hj] at hres
  have hje : e ≤ j := by
    by_contra! hjlt
    have heq : (j : ℤ) = (e : ℤ) :=
      residue_eq_of_range (hres.symm.trans hs) (by positivity)
        (by omega) (by positivity) he
    omega
  have hl := (growth hc j).1
  rw [hj] at hl
  calc
    g^e ≤ g^j := pow_le_pow_right₀ hg hje
    _ ≤ (c-1)^j := pow_le_pow_left₀ (by omega) hgc _
    _ ≤ t := hl

/-- Soundness of both Pell tests on the nondegenerate branch `g ≥ 2`.
The input `T` is the height construction's parameter. Its only analytic
consequence used here is the strict cap `H < 2^T`. -/
theorem two_pair_sound {g y s₀ t₀ s t H : ℤ} {e T : ℕ}
    (hg : 2 ≤ g) (hy : 0 ≤ y) (hgT : g ≤ (T : ℤ))
    (heT : e ≤ T)
    (h₀ : Admissible ((T : ℤ)+5) s₀ t₀)
    (h₀mod : s₀ ≡ (e : ℤ) [ZMOD (T : ℤ)+5-2])
    (A : ℤ) (hAeq : A = t₀ + g^2 + y + (T : ℤ) + 10)
    (h : Admissible A s t) (hs : s ≡ (e : ℤ) [ZMOD A-2])
    (hout : y ≡ t + (g-A)*s [ZMOD A*g-g^2-1])
    (ht : t ≤ H) (hH : H < (2 : ℤ)^T) : y = g^e := by
  have hT : (0 : ℤ) ≤ T := by positivity
  have ht₀ := h₀.2.1
  have hs₀ := h₀.1
  have hg₂ : 0 ≤ g^2 := sq_nonneg _
  have hA : 4 ≤ A := by omega
  have hm : A < A*g-g^2-1 := by
    nlinarith [mul_nonneg (show 0 ≤ A by omega) (show 0 ≤ g-2 by omega)]
  have hl := first_pair_lower (by omega : (4 : ℤ) ≤ (T : ℤ)+5)
    (by omega : (1 : ℤ) ≤ g) (by omega) (by omega) h₀ h₀mod
  exact bounded_power_sound hA h hs (by omega) (by omega) (ht.trans_lt hH)
    hy (by omega) (by omega) (by omega) hout

/-- Completeness for the genuine power, using the prescribed index in
each pair. The cap hypothesis is sufficient for the honest second pair. -/
theorem two_pair_complete {g H : ℤ} {e T : ℕ} (hg : 2 ≤ g)
    (hcap : ((pair ((T : ℤ)+5) e).2 + g^2 + g^e + (T : ℤ) + 10)^e ≤ H) :
    ∃ s₀ t₀ A s t : ℤ,
      Admissible ((T : ℤ)+5) s₀ t₀ ∧
      s₀ ≡ (e : ℤ) [ZMOD (T : ℤ)+5-2] ∧
      A = t₀ + g^2 + g^e + (T : ℤ) + 10 ∧
      Admissible A s t ∧ s ≡ (e : ℤ) [ZMOD A-2] ∧
      g^e ≡ t + (g-A)*s [ZMOD A*g-g^2-1] ∧ t ≤ H := by
  let c : ℤ := (T : ℤ)+5
  let p₀ := pair c e
  let A := p₀.2 + g^2 + g^e + (T : ℤ) + 10
  have hc : 4 ≤ c := by dsimp [c]; omega
  have h₀ := pair_admissible hc e
  have ht₀ : 0 < p₀.2 := lt_of_le_of_lt h₀.1 h₀.2.1
  have hA : 4 ≤ A := by
    dsimp only [A]
    have hg₁ := pow_nonneg (show 0 ≤ g by omega) e
    have hg₂ := sq_nonneg g
    omega
  exact ⟨p₀.1, p₀.2, A, (pair A e).1, (pair A e).2,
    h₀, (index_modEq c e).1, rfl, pair_admissible hA e,
    (index_modEq A e).1, (power_modEq A g e).symm,
    (growth hA e).2.trans hcap⟩

/-- Binary-size estimate for the honest cap. If `T` fits below `2^L`
and bounds the base and the true output, then `2^(2 L³)` already bounds
the power used in `two_pair_complete`. -/
theorem honest_cap_bounds {g : ℤ} {T L e : ℕ} (hL : 4 ≤ L) (hg : 2 ≤ g)
    (hgT : g ≤ (T : ℤ)) (hyT : g^e ≤ (T : ℤ)) (hT : (T : ℤ) ≤ 2^L) :
    let A := (pair ((T : ℤ)+5) e).2 + g^2 + g^e + (T : ℤ) + 10
    A ≤ (2 : ℤ)^(2*L^3) ∧ A^e ≤ (2 : ℤ)^(2*L^3) := by
  have he : e ≤ L := by
    by_contra! h
    have h₁ := pow_le_pow_left₀ (show (0 : ℤ) ≤ 2 by decide) hg e
    have h₂ := pow_lt_pow_right₀ (show (1 : ℤ) < 2 by decide) h
    omega
  let K := (L+1)*L
  have hLK : L ≤ K := by dsimp [K]; nlinarith
  have h₂LK : L*2 ≤ K := by
    dsimp [K]
    nlinarith [Nat.mul_le_mul_left L hL]
  have h₁₀ : (10 : ℤ) ≤ 2^L := by
    calc 10 ≤ (2 : ℤ)^4 := by decide
         _ ≤ 2^L := pow_le_pow_right₀ (by decide) hL
  have h₁K : (2 : ℤ)^L ≤ 2^K := pow_le_pow_right₀ (by decide) hLK
  have hc : (T : ℤ)+5 ≤ (2 : ℤ)^(L+1) := by rw [pow_succ]; omega
  have hp₀ : (pair ((T : ℤ)+5) e).2 ≤ (2 : ℤ)^K := by
    calc (pair ((T : ℤ)+5) e).2 ≤ ((T : ℤ)+5)^e := (growth (by omega) e).2
         _ ≤ ((2 : ℤ)^(L+1))^e := pow_le_pow_left₀ (by omega) hc _
         _ = (2 : ℤ)^((L+1)*e) := (pow_mul _ _ _).symm
         _ ≤ (2 : ℤ)^K := pow_le_pow_right₀ (by decide) (Nat.mul_le_mul_left _ he)
  have hg₂ : g^2 ≤ (2 : ℤ)^K := by
    calc g^2 ≤ ((2 : ℤ)^L)^2 := pow_le_pow_left₀ (by omega) (hgT.trans hT) _
         _ = (2 : ℤ)^(L*2) := (pow_mul _ _ _).symm
         _ ≤ (2 : ℤ)^K := pow_le_pow_right₀ (by decide) h₂LK
  let A := (pair ((T : ℤ)+5) e).2 + g^2 + g^e + (T : ℤ) + 10
  have hA : A ≤ (2 : ℤ)^(K+3) := by
    dsimp only [A]
    rw [pow_add]
    norm_num
    omega
  have hA₀ : 0 ≤ A := by
    obtain ⟨hs, hst, _⟩ := pair_admissible (show (4 : ℤ) ≤ (T : ℤ)+5 by omega) e
    have hg' := pow_nonneg (show 0 ≤ g by omega) e
    dsimp only [A]
    nlinarith [sq_nonneg g]
  have hexp : (K+3)*e ≤ 2*L^3 := by
    calc (K+3)*e ≤ (K+3)*L := Nat.mul_le_mul_left _ he
         _ ≤ 2*L^3 := by
           dsimp only [K]
           nlinarith [Nat.mul_le_mul_left (L*L) hL, Nat.mul_le_mul_left L hL]
  have hK : K+3 ≤ 2*L^3 := by
    dsimp only [K]
    nlinarith [Nat.mul_le_mul_left (L*L) hL, Nat.mul_le_mul_left L hL]
  refine ⟨hA.trans (pow_le_pow_right₀ (by decide) hK), ?_⟩
  calc A^e ≤ ((2 : ℤ)^(K+3))^e := pow_le_pow_left₀ hA₀ hA _
       _ = (2 : ℤ)^((K+3)*e) := (pow_mul _ _ _).symm
       _ ≤ (2 : ℤ)^(2*L^3) := pow_le_pow_right₀ (by decide) hexp

theorem honest_cap {g : ℤ} {T L e : ℕ} (hL : 4 ≤ L) (hg : 2 ≤ g)
    (hgT : g ≤ (T : ℤ)) (hyT : g^e ≤ (T : ℤ)) (hT : (T : ℤ) ≤ 2^L) :
    ((pair ((T : ℤ)+5) e).2 + g^2 + g^e + (T : ℤ) + 10)^e ≤
      (2 : ℤ)^(2*L^3) := (honest_cap_bounds hL hg hgT hyT hT).2

/-- Homogeneous Bézout identity for the numerator and denominator of
the doubling formula on `y²+y=x³−x`. This is the explicit common-factor
calculation in the height lemma. -/
theorem duplication_bezout (u v : ℤ) :
    (64*v^3 - 48*u^2*v) * (u^4+2*u^2*v^2-2*u*v^3+v^4) +
      (12*u^3+20*u*v^2-27*v^3) * (4*u^3*v-4*u*v^3+v^4) =
      37*v^7 := by ring

/-- Every common divisor of the doubling coordinates of a reduced
fraction divides 37. -/
theorem duplication_common_factor {u v d : ℤ} (huv : IsCoprime u v)
    (hdF : d ∣ u^4+2*u^2*v^2-2*u*v^3+v^4)
    (hdG : d ∣ 4*u^3*v-4*u*v^3+v^4) : d ∣ 37 := by
  have hF : IsCoprime (u^4+2*u^2*v^2-2*u*v^3+v^4) v := by
    have h : IsCoprime (u^4) v := huv.pow_left
    convert h.add_mul_left_left (2*u^2*v-2*u*v^2+v^3) using 1; ring
  have hdv : IsCoprime d (v^7) := (hF.of_isCoprime_of_dvd_left hdF).pow_right
  apply hdv.dvd_of_dvd_mul_right
  rw [← duplication_bezout]
  exact dvd_add (dvd_mul_of_dvd_right hdF _) (dvd_mul_of_dvd_right hdG _)

end DiophantineNP.Pell
