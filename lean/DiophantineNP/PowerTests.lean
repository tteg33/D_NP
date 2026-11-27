import DiophantineNP.PowerWindow

/-! # Joint semantic verification of both elliptic windows and both Pell tests

The witness points here belong to mathlib's rational-point group. The conversion
of rational coordinates and their auxiliary tests to one integer polynomial is
a separate encoding layer.
-/

namespace DiophantineNP.PowerTests

open Curve37

def total (g e y : ℕ) : ℕ := g + e + y + 2^1024

structure Trace where
  Q : E.Point
  R : E.Point
  s₀ : ℤ
  t₀ : ℤ
  A : ℤ
  s : ℤ
  t : ℤ

/-- The actual nondegenerate branch of the draft, including both arithmetic
height cutoffs. There is no free parameter for the cap. -/
def MainTests (g e y : ℕ) (w : Trace) : Prop :=
  let T := total g e y
  2 ≤ g ∧ Adjacent T w.Q ∧ Adjacent (height w.Q) w.R ∧
  Pell.Admissible ((T : ℤ)+5) w.s₀ w.t₀ ∧
  w.s₀ ≡ (e : ℤ) [ZMOD (T : ℤ)+5-2] ∧
  w.A = w.t₀ + (g : ℤ)^2 + y + T + 10 ∧
  Pell.Admissible w.A w.s w.t ∧ w.s ≡ (e : ℤ) [ZMOD w.A-2] ∧
  (y : ℤ) ≡ w.t+((g : ℤ)-w.A)*w.s [ZMOD w.A*g-(g : ℤ)^2-1] ∧
  w.t ≤ height w.R

def Small (g e y : ℕ) : Prop :=
  (g=1 ∧ y=1) ∨ (g=0 ∧ ((e=0 ∧ y=1) ∨ (0<e ∧ y=0)))

def Accepts (g e y : ℕ) (w : Trace) : Prop := Small g e y ∨ MainTests g e y w

/-- Height `H` bounds the Pell registers, and `H³` bounds all four
multiplicative x-heights. Its logarithm is quartic in the logarithm of T. -/
def Honest (g e y : ℕ) (w : Trace) : Prop :=
  let H := height w.R
  (∀ v ∈ [w.s₀,w.t₀,w.A,w.s,w.t], 0 ≤ v ∧ v ≤ (H : ℤ)) ∧
  height w.Q ≤ H ∧ height (w.Q+P) ≤ H^3 ∧ height (w.R+P) ≤ H^3 ∧
  logHeight w.R ≤ 45^3 * (Real.logb 2 (total g e y))^4

abbrev Cyclic : Prop := ∀ Q : E.Point, ∃ j : ℤ, j • P = Q
abbrev Quadratic : Prop :=
  ∀ j : ℤ, canonicalHeight (j • P) = canonicalHeight P * (j : ℝ)^2

private theorem total_large (g e y : ℕ) : 2^1024 ≤ total g e y := by
  exact Nat.le_add_left _ _

private theorem inputs_le (g e y : ℕ) :
    g ≤ total g e y ∧ e ≤ total g e y ∧ y ≤ total g e y := by
  unfold total
  generalize (2 : ℕ)^1024 = k
  omega

private theorem log_large {V : ℕ} (hV : 2^1024 ≤ V) : 1024 ≤ Real.logb 2 V := by
  have hVpos : (0 : ℝ) < V := by exact_mod_cast lt_of_lt_of_le (by positivity) hV
  apply (Real.le_logb_iff_rpow_le (by norm_num) hVpos).mpr
  rw [show (1024 : ℝ) = ((1024 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact_mod_cast hV

private theorem integer_cap {T H : ℕ} (hT : 2^1024 ≤ T) (hH : 0 < H)
    (hbound : (Real.logb 2 T)^4/8 ≤ Real.logb 2 H) :
    ∃ n : ℕ, 4 ≤ n ∧ (T : ℤ) ≤ 2^n ∧ (2 : ℤ)^(2*n^3) ≤ H := by
  let L := Real.logb 2 T
  let n := ⌊L⌋₊+1
  have hL : 1024 ≤ L := log_large hT
  have hL₀ : 0 ≤ L := by linarith
  have hn₀ : 1024 ≤ ⌊L⌋₊ := Nat.le_floor (by exact_mod_cast hL)
  have hLn : L < (n : ℝ) := by
    simpa [n] using Nat.lt_floor_add_one L
  have hnL : (n : ℝ) ≤ L+1 := by
    dsimp only [n]
    push_cast
    linarith [Nat.floor_le hL₀]
  have hVpos : (0 : ℝ) < T := by exact_mod_cast lt_of_lt_of_le (by positivity) hT
  have hinput : (T : ℝ) ≤ (2 : ℝ)^n := by
    calc (T : ℝ) = (2 : ℝ)^L := (Real.rpow_logb (by norm_num) (by norm_num) hVpos).symm
         _ ≤ (2 : ℝ)^(n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hLn.le
         _ = (2 : ℝ)^n := Real.rpow_natCast _ _
  have hpow := pow_le_pow_left₀ (show (0:ℝ) ≤ n by positivity) hnL 3
  have hh : 2*(n : ℝ)^3 ≤ Real.logb 2 H := by
    change L^4/8 ≤ _ at hbound
    nlinarith only [hpow,hbound,hL,
      mul_le_mul_of_nonneg_right hL hL₀,
      mul_le_mul_of_nonneg_right hL (sq_nonneg L),
      mul_le_mul_of_nonneg_right hL (pow_nonneg hL₀ 3)]
  have hnumpow : ((2*n^3 : ℕ) : ℝ) ≤ Real.logb 2 H := by exact_mod_cast hh
  have hr := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (show (0 : ℝ) < H by exact_mod_cast hH)).mp hnumpow
  rw [Real.rpow_natCast] at hr
  exact ⟨n, by dsimp [n]; omega, by exact_mod_cast hinput, by exact_mod_cast hr⟩

private theorem adjacent_grows (hc : Cyclic) (hq : Quadratic) {V : ℕ}
    (hV : 0 < V) (hL : 1024 ≤ Real.logb 2 V) {Q : E.Point} (h : Adjacent V Q) :
    V ≤ height Q ∧ 1024 ≤ logHeight Q := by
  have ⟨lo,hi⟩ := (adjacent_iff hV Q).mp h
  have hb := ((adjacent_height_window hc hq hL).2 Q lo hi).1
  have hplus : Real.logb 2 V ≤ logHeight Q := by
    nlinarith only [hb, mul_nonneg
      (show 0 ≤ Real.logb 2 V by linarith)
      (show 0 ≤ Real.logb 2 V - 2 by linarith)]
  have hh := (Real.logb_le_logb (by norm_num : (1:ℝ)<2)
    (show (0:ℝ)<V by exact_mod_cast hV)
    (show (0:ℝ)<height Q by exact_mod_cast height_pos Q)).mp hplus
  exact ⟨by exact_mod_cast hh, hL.trans hplus⟩

theorem sound (hc : Cyclic) (hq : Quadratic) {g e y : ℕ} {w : Trace}
    (hw : Accepts g e y w) : y = g^e := by
  rcases hw with h | h
  · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,⟨rfl,rfl⟩ | ⟨he,rfl⟩⟩
    · simp
    · simp
    · simp [Nat.ne_of_gt he]
  · let T := total g e y
    rcases h with ⟨hg,hQ,hR,h₀,hmod₀,hA,h₁,hmod₁,hy,ht⟩
    have hcap := ((two_adjacent_windows hc hq (total_large g e y)).2 _ _ hQ hR).2.2
    have hgT : g ≤ T := (inputs_le ..).1
    have heT : e ≤ T := (inputs_le ..).2.1
    have hr := Pell.two_pair_sound (g := (g : ℤ)) (e := e) (T := T)
      (by exact_mod_cast hg) (Int.natCast_nonneg y)
      (by exact_mod_cast hgT) heT h₀ hmod₀ w.A hA h₁ hmod₁ hy ht
      (by exact_mod_cast hcap)
    exact_mod_cast hr

theorem complete (hc : Cyclic) (hq : Quadratic) (g e : ℕ) :
    ∃ w : Trace, Accepts g e (g^e) w ∧ Honest g e (g^e) w := by
  let T := total g e (g^e)
  have hT := total_large g e (g^e)
  have hT₀ : 0 < T := lt_of_lt_of_le (by positivity) hT
  by_cases hg : 2 ≤ g
  · obtain ⟨⟨Q,R,hQ,hR⟩, hb⟩ := two_adjacent_windows hc hq hT
    obtain ⟨hlo,hhi,_⟩ := hb Q R hQ hR
    obtain ⟨n,hn,htn,hnr⟩ := integer_cap hT (height_pos R) hlo
    have hgT : g ≤ T := (inputs_le ..).1
    have hyT : g^e ≤ T := (inputs_le ..).2.2
    have hg' : (2 : ℤ) ≤ g := by exact_mod_cast hg
    have ha := Pell.honest_cap_bounds hn hg' (by exact_mod_cast hgT)
      (by exact_mod_cast hyT) htn
    let c : ℤ := (T : ℤ)+5
    let p₀ := Pell.pair c e
    let A := p₀.2 + (g : ℤ)^2 + (g : ℤ)^e + T + 10
    let p := Pell.pair A e
    have h₀ := Pell.pair_admissible (show 4 ≤ c by dsimp [c]; omega) e
    have hs₀ : 0 ≤ p₀.1 := h₀.1
    have hst₀ : p₀.1 < p₀.2 := h₀.2.1
    have hA₁ : 4 ≤ A := by
      dsimp only [A]
      have he' := pow_nonneg (Int.natCast_nonneg g) e
      nlinarith only [hs₀,hst₀,sq_nonneg (g : ℤ),he',Int.natCast_nonneg T]
    have ha₀ : A ≤ height R := ha.1.trans hnr
    have ha₁ : A^e ≤ height R := ha.2.trans hnr
    have hp := Pell.pair_admissible hA₁ e
    have hs : 0 ≤ p.1 := hp.1
    have hst : p.1 < p.2 := hp.2.1
    have hpt : p.2 ≤ height R := (Pell.growth hA₁ e).2.trans ha₁
    let w : Trace := ⟨Q,R,p₀.1,p₀.2,A,p.1,p.2⟩
    refine ⟨w, Or.inr ?_, ?_⟩
    · refine ⟨hg,hQ,hR,h₀,(Pell.index_modEq c e).1,?_,hp,
        (Pell.index_modEq A e).1,?_,hpt⟩
      · dsimp only [w,A]; push_cast; rfl
      · simpa only [w,Nat.cast_pow] using (Pell.power_modEq A g e).symm
    · obtain ⟨hTQ,hLQ⟩ := adjacent_grows hc hq hT₀ (log_large hT) hQ
      obtain ⟨hQR,_⟩ := adjacent_grows hc hq (height_pos Q) hLQ hR
      have hb₀ : p₀.2 ≤ A := by
        dsimp only [A]
        have he' := pow_nonneg (Int.natCast_nonneg g) e
        nlinarith only [sq_nonneg (g : ℤ),he',Int.natCast_nonneg T]
      refine ⟨?_,hQR,?_,?_,hhi⟩
      · intro v hv
        change 0 ≤ v ∧ v ≤ (height R : ℤ)
        change v ∈ [p₀.1,p₀.2,A,p.1,p.2] at hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl|rfl|rfl|rfl <;> constructor <;> omega
      · calc height (Q+P) ≤ T^2*height Q := hQ.2
             _ ≤ (height R)^2*height R := Nat.mul_le_mul (Nat.pow_le_pow_left (hTQ.trans hQR) 2) hQR
             _ = (height R)^3 := by ring
      · calc height (R+P) ≤ (height Q)^2*height R := hR.2
             _ ≤ (height R)^2*height R := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hQR 2)
             _ = (height R)^3 := by ring
  · let w : Trace := ⟨0,0,0,0,0,0,0⟩
    refine ⟨w, Or.inl ?_, ?_⟩
    · rcases (show g = 0 ∨ g = 1 by omega) with rfl|rfl
      · right
        cases e <;> simp
      · left; simp
    · have hP : height P = 1 := by decide +kernel
      have hzero : height (0 : E.Point) = 1 := rfl
      have hlog : logHeight (0 : E.Point) = 0 := by simp [logHeight,hzero]
      refine ⟨?_,?_,?_,?_,?_⟩
      · intro v hv
        change v ∈ ([0,0,0,0,0] : List ℤ) at hv
        have hz : v = 0 := by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using hv
        subst v
        exact ⟨le_rfl,Int.natCast_nonneg _⟩
      · exact le_rfl
      · change height ((0 : E.Point)+P) ≤ (height (0 : E.Point))^3
        rw [zero_add,hP,hzero]
        decide
      · change height ((0 : E.Point)+P) ≤ (height (0 : E.Point))^3
        rw [zero_add,hP,hzero]
        decide
      · change logHeight (0 : E.Point) ≤ _
        rw [hlog]
        exact mul_nonneg (by norm_num) (Even.pow_nonneg (by decide : Even 4) _)

/-- Globally sound for arbitrary traces, with bounded honest traces on positives. -/
theorem exact (hc : Cyclic) (hq : Quadratic) (g e y : ℕ) :
    (∃ w, Accepts g e y w) ↔ (y = g^e ∧ ∃ w, Accepts g e y w ∧ Honest g e y w) := by
  constructor
  · rintro ⟨w,hw⟩
    obtain rfl := sound hc hq hw
    exact ⟨rfl,complete hc hq g e⟩
  · rintro ⟨_,w,hw,_⟩
    exact ⟨w,hw⟩

end DiophantineNP.PowerTests
