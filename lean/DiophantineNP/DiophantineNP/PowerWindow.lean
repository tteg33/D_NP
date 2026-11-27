import DiophantineNP.Curve37
import DiophantineNP.Pell

/-! # The elliptic height cap used by the two Pell tests -/

namespace DiophantineNP.Curve37

/-- The two inequalities appearing in the fixed graph before logs are taken. -/
def Adjacent (V : ℕ) (Q : E.Point) : Prop :=
  V*height Q ≤ height (Q+P) ∧ height (Q+P) ≤ V^2*height Q

theorem adjacent_iff {V : ℕ} (hV : 0 < V) (Q : E.Point) :
    Adjacent V Q ↔ Real.logb 2 V ≤ logHeight (Q+P)-logHeight Q ∧
      logHeight (Q+P)-logHeight Q ≤ 2*Real.logb 2 V := by
  have hV' : (0 : ℝ) < V := by exact_mod_cast hV
  have hp : (0 : ℝ) < height Q := by exact_mod_cast height_pos Q
  have hq : (0 : ℝ) < height (Q+P) := by exact_mod_cast height_pos (Q+P)
  have h₁ := Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (mul_pos hV' hp) hq
  have h₂ := Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hq (mul_pos (pow_pos hV' 2) hp)
  rw [Real.logb_mul hV'.ne' hp.ne'] at h₁
  rw [Real.logb_mul (by positivity) hp.ne', Real.logb_pow] at h₂
  norm_num only [Nat.cast_ofNat] at h₂
  dsimp only [Adjacent,logHeight]
  constructor
  · rintro ⟨hl,hu⟩
    have ha := h₁.mpr (by exact_mod_cast hl)
    have hb := h₂.mpr (by exact_mod_cast hu)
    constructor <;> linarith
  · rintro ⟨hl,hu⟩
    have ha := h₁.mp (by linarith)
    have hb := h₂.mp (by linarith)
    exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩

private theorem quartic_nat {n : ℕ} (hn : 1024 ≤ n) : 45^3*(n+1)^4 < 2^n := by
  induction n, hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    have he : (n+2)^4 ≤ 2*(n+1)^4 := by
      nlinarith [Nat.mul_le_mul_left n hn, Nat.mul_le_mul_left (n*n) hn,
        Nat.mul_le_mul_left (n*n*n) hn]
    rw [pow_succ 2 n]
    have h := Nat.mul_le_mul_left (45^3) he
    nlinarith only [h,ih]

private theorem quartic_lt_exponential {L : ℝ} (hL : 1024 ≤ L) :
    45^3*L^4 < (2 : ℝ)^L := by
  let n := ⌊L⌋₊
  have hn : 1024 ≤ n := Nat.le_floor (by norm_num at *; linarith)
  have hlow : (n : ℝ) ≤ L := Nat.floor_le (by linarith)
  have hhi : L < (n : ℝ)+1 := Nat.lt_floor_add_one _
  have h₁ : L^4 ≤ ((n : ℝ)+1)^4 := pow_le_pow_left₀ (by linarith) hhi.le _
  calc 45^3*L^4 ≤ 45^3*((n : ℝ)+1)^4 := by linarith only [h₁]
       _ < (2 : ℝ)^n := by exact_mod_cast quartic_nat hn
       _ = (2 : ℝ)^(n : ℝ) := (Real.rpow_natCast _ _).symm
       _ ≤ (2 : ℝ)^L := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlow

/-- For a genuine input to both elliptic tests, the output is short and
strictly below the false-index threshold. Every admitted pair has these
bounds. The curve-theoretic inputs are the two stated hypotheses. -/
theorem two_adjacent_windows
    (hcyclic : ∀ Q : E.Point, ∃ j : ℤ, j • P = Q)
    (hquadratic : ∀ j : ℤ, canonicalHeight (j • P) = canonicalHeight P * (j : ℝ)^2)
    {V : ℕ} (hV : 2^1024 ≤ V) :
    (∃ Q R : E.Point, Adjacent V Q ∧ Adjacent (height Q) R) ∧
    ∀ Q R : E.Point, Adjacent V Q → Adjacent (height Q) R →
      (Real.logb 2 V)^4/8 ≤ logHeight R ∧
      logHeight R ≤ 45^3*(Real.logb 2 V)^4 ∧ height R < 2^V := by
  have hV₀ : 0 < V := lt_of_lt_of_le (by positivity) hV
  have hVpos : (0 : ℝ) < V := by exact_mod_cast hV₀
  have hL : 1024 ≤ Real.logb 2 V := by
    apply (Real.le_logb_iff_rpow_le (by norm_num) hVpos).mpr
    rw [show (1024 : ℝ) = ((1024 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact_mod_cast hV
  obtain ⟨hex,hbound⟩ := adjacent_height_window hcyclic hquadratic hL
  have h₁ (Q : E.Point) (hq : Adjacent V Q) :
      (Real.logb 2 V)^2/2 ≤ logHeight Q ∧ logHeight Q ≤ 45*(Real.logb 2 V)^2 := by
    obtain ⟨hl,hu⟩ := (adjacent_iff hV₀ Q).mp hq
    exact hbound Q hl hu
  have hbig (Q : E.Point) (hq : Adjacent V Q) : 1024 ≤ logHeight Q := by
    have hs := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1024) hL
    nlinarith only [hs,(h₁ Q hq).1]
  constructor
  · obtain ⟨Q,hq⟩ := hex
    have hQ := (adjacent_iff hV₀ Q).mpr hq
    obtain ⟨⟨R,hr⟩,_⟩ := adjacent_height_window hcyclic hquadratic (hbig Q hQ)
    exact ⟨Q,R,hQ,(adjacent_iff (height_pos Q) R).mpr hr⟩
  · intro Q R hq hr
    obtain ⟨_,hbound'⟩ := adjacent_height_window hcyclic hquadratic (hbig Q hq)
    obtain ⟨hr₁,hr₂⟩ := (adjacent_iff (height_pos Q) R).mp hr
    obtain ⟨hl,hu⟩ := hbound' R hr₁ hr₂
    obtain ⟨hl₀,hu₀⟩ := h₁ Q hq
    obtain ⟨ha,hb⟩ := HeightWindow.twice hl₀ hu₀ hl hu
    refine ⟨ha,hb,?_⟩
    have hh := hb.trans_lt (quartic_lt_exponential hL)
    rw [Real.rpow_logb (by norm_num) (by norm_num) hVpos] at hh
    have hfinal := (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2)
      (show (0 : ℝ) < height R by exact_mod_cast height_pos R)).mp hh
    rw [Real.rpow_natCast] at hfinal
    exact_mod_cast hfinal

end DiophantineNP.Curve37
