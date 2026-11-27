import DiophantineNP.IntegerCurveStep
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # Integer-register implementation of Appendix A

The registers contain ordinary integers only. Its semantics uses polynomial
equalities, order, divisibility, primitive pairs, and finite alternatives.
-/

namespace DiophantineNP.PowerTests

open Curve37

structure IntegerTrace where
  first : Step
  second : Step
  s₀ : ℤ
  t₀ : ℤ
  A : ℤ
  s : ℤ
  t : ℤ

def IntegerMain (g e y : ℕ) (w : IntegerTrace) : Prop :=
  let T := total g e y
  2 ≤ g ∧ w.first.Window T ∧ w.second.Window w.first.start ∧
  Pell.Admissible ((T:ℤ)+5) w.s₀ w.t₀ ∧
  w.s₀ ≡ (e:ℤ) [ZMOD (T:ℤ)+5-2] ∧ w.A = w.t₀+(g:ℤ)^2+y+T+10 ∧
  Pell.Admissible w.A w.s w.t ∧ w.s ≡ (e:ℤ) [ZMOD w.A-2] ∧
  (y:ℤ) ≡ w.t+((g:ℤ)-w.A)*w.s [ZMOD w.A*g-(g:ℤ)^2-1] ∧ w.t ≤ w.second.start

def IntegerAccepts (g e y : ℕ) (w : IntegerTrace) : Prop :=
  Small g e y ∨ IntegerMain g e y w

def Step.Bounded (w : Step) (B : ℕ) : Prop :=
  w.start ≤ B ∧ max w.yNum.natAbs w.yDen.natAbs ≤ B ∧ w.finish ≤ B

def IntegerTrace.Bounded (w : IntegerTrace) (B : ℕ) : Prop :=
  w.first.Bounded B ∧ w.second.Bounded B ∧
  ∀ z ∈ [w.s₀,w.t₀,w.A,w.s,w.t], z.natAbs ≤ B

/-- Every integer register of a true witness has magnitude at most 2 to this
quartic power. -/
def budget (T : ℕ) := 5 + 3 * (45^3) * (T.log2+1)^4

theorem integer_sound (hc : Cyclic) (hq : Quadratic) {g e y : ℕ} {w : IntegerTrace}
    (hw : IntegerAccepts g e y w) : y = g^e := by
  rcases hw with hh | hh
  · exact sound hc hq (w := ⟨0,0,0,0,0,0,0⟩) (Or.inl hh)
  · rcases hh with ⟨hg,⟨hv,h₁,h₂⟩,⟨hv',h₁',h₂'⟩,h₀,hm₀,hA,hp,hm,hy,ht⟩
    obtain ⟨Q,hQ,hQ'⟩ := Step.decode hv
    obtain ⟨R,hR,hR'⟩ := Step.decode hv'
    rw [hQ,hQ'] at h₁ h₂
    rw [hQ,hR,hR'] at h₁' h₂'
    rw [hR] at ht
    exact sound hc hq (w := ⟨Q,R,w.s₀,w.t₀,w.A,w.s,w.t⟩)
      (Or.inr ⟨hg,⟨h₁,h₂⟩,⟨h₁',h₂'⟩,h₀,hm₀,hA,hp,hm,hy,ht⟩)

private theorem budget_of_log_bound {T H : ℕ} (hT : 1 ≤ T) (hH : 0 < H)
    (hb : Real.logb 2 H ≤ 45^3*(Real.logb 2 T)^4) :
    20*H^3 ≤ 2^(budget T) := by
  let L := T.log2+1
  let N := 45^3*L^4
  have ht : T < 2^L := Nat.lt_log2_self
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hpow : (T : ℝ) ≤ (2 : ℝ)^(L : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast ht.le
  have hL := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2) hTpos).mpr hpow
  have hh : 0 ≤ Real.logb 2 T := Real.logb_nonneg (by norm_num) (by exact_mod_cast hT)
  have h₁ : (Real.logb 2 T)^4 ≤ (L:ℝ)^4 := pow_le_pow_left₀ hh hL _
  have hb' : Real.logb 2 H ≤ (N:ℝ) := by
    dsimp [N]; push_cast
    linarith only [hb,h₁]
  have hbig := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2)
    (show (0:ℝ)<H by exact_mod_cast hH)).mp hb'
  rw [Real.rpow_natCast] at hbig
  have hc : H ≤ 2^N := by exact_mod_cast hbig
  have hn : budget T = 5 + N*3 := by unfold budget N L; ring
  rw [hn,pow_add,pow_mul]
  exact Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hc 3)

private def zeroStep : Step := ⟨0,0,0,0,0,0⟩

/-- Honest registers for the two elliptic height steps and both Pell pairs
have size bounded by a fixed polynomial in the input/output bit length. -/
theorem integer_complete (hc : Cyclic) (hq : Quadratic) (g e : ℕ) :
    ∃ w : IntegerTrace, IntegerAccepts g e (g^e) w ∧
      w.Bounded (2^(budget (total g e (g^e)))) := by
  let T := total g e (g^e)
  obtain ⟨w,hw,hwsize⟩ := complete hc hq g e
  rcases hw with hsmall | hh
  · refine ⟨⟨zeroStep,zeroStep,0,0,0,0,0⟩,Or.inl hsmall,?_⟩
    let B := 2^(budget T)
    have hz : zeroStep.Bounded B := ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
    refine ⟨hz,hz,?_⟩
    intro v h
    have he : v = 0 := by
      change v ∈ ([0,0,0,0,0] : List ℤ) at h
      simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using h
    rw [he]; exact Nat.zero_le _
  · rcases hh with ⟨hg,hQ,hR,h₀,hm₀,hA,hp,hm,hy,ht⟩
    obtain ⟨hregs,hQR,hQP,hRP,hlog⟩ := hwsize
    have hlarge : 2^1024 ≤ T := Nat.le_add_left _ _
    have hT : 1 ≤ T := (Nat.pow_pos (by decide : 0 < 2)).trans_le hlarge
    have h01 : 1 < height w.Q := by
      have hVpos : 0 < T := hT
      have hL : 1024 ≤ Real.logb 2 T := by
        apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2)
          (show (0:ℝ)<T by exact_mod_cast hVpos)).mpr
        rw [show (1024 : ℝ) = ((1024 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        exact_mod_cast hlarge
      obtain ⟨ha,hb⟩ := (adjacent_iff hVpos w.Q).mp hQ
      have hl := ((adjacent_height_window hc hq hL).2 w.Q ha hb).1
      have hpos : 0 < logHeight w.Q := by
        have hs := mul_self_le_mul_self (by norm_num : (0:ℝ)≤1024) hL
        nlinarith only [hl,hs]
      have hreal := (Real.logb_pos_iff (by norm_num : (1:ℝ)<2)
        (show (0:ℝ)<height w.Q by exact_mod_cast height_pos w.Q)).mp hpos
      exact_mod_cast hreal
    obtain ⟨q,hqv,hq₁,hq₂,hqy⟩ := Step.encode w.Q h01
    obtain ⟨r,hrv,hr₁,hr₂,hry⟩ := Step.encode w.R (h01.trans_le hQR)
    let z : IntegerTrace := ⟨q,r,w.s₀,w.t₀,w.A,w.s,w.t⟩
    refine ⟨z, Or.inr ?_, ?_⟩
    · refine ⟨hg,⟨hqv,?_,?_⟩,⟨hrv,?_,?_⟩,h₀,hm₀,hA,hp,hm,hy,?_⟩
      · simpa only [z,hq₁,hq₂] using hQ.1
      · simpa only [z,hq₁,hq₂] using hQ.2
      · simpa only [z,hq₁,hr₁,hr₂] using hR.1
      · simpa only [z,hq₁,hr₁,hr₂] using hR.2
      · simpa only [z,hr₁] using ht
    · let H := height w.R
      let B := 2^(budget T)
      have hH : 20*H^3 ≤ B := budget_of_log_bound hT (height_pos w.R) hlog
      have h₃ : H^3 ≤ B := (Nat.le_mul_of_pos_left _ (by decide : 0 < 20)).trans hH
      have h₁ : H ≤ B := (Nat.le_self_pow (n := 3) (by decide) _).trans h₃
      have hy₁ := (Nat.le_self_pow (n := 2) (by decide) _).trans hqy
      have hy₂ := (Nat.le_self_pow (n := 2) (by decide) _).trans hry
      have hqr : 20*(height w.Q)^3 ≤ 20*H^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQR 3)
      refine ⟨⟨?_,hy₁.trans (hqr.trans hH),?_⟩,⟨?_,hy₂.trans hH,?_⟩,?_⟩
      · rw [show z.first = q from rfl,hq₁]; exact hQR.trans h₁
      · rw [show z.first = q from rfl,hq₂]; exact hQP.trans h₃
      · rw [show z.second = r from rfl,hr₁]; exact h₁
      · rw [show z.second = r from rfl,hr₂]; exact hRP.trans h₃
      · intro v hv
        obtain ⟨hpos,hle⟩ := hregs v hv
        have hv' : v.natAbs ≤ H := by
          exact_mod_cast (show (v.natAbs : ℤ) ≤ (H : ℤ) by simpa [Int.natCast_natAbs,abs_of_nonneg hpos] using hle)
        exact hv'.trans h₁

theorem integer_exact (hc : Cyclic) (hq : Quadratic) (g e y : ℕ) :
    y = g^e ↔ ∃ w : IntegerTrace, IntegerAccepts g e y w ∧ w.Bounded (2^(budget (total g e y))) := by
  constructor
  · rintro rfl; exact integer_complete hc hq g e
  · rintro ⟨w,hw,_⟩; exact integer_sound hc hq hw

/-- This is the input/output length parameter of Theorem A.1, up to
rounding by one bit. The additive constant in T only changes the coefficient. -/
def inputBits (g e y : ℕ) := (2+g+e+y).log2+1

set_option exponentiation.threshold 1024 in
theorem budget_input_bits (g e y : ℕ) :
    budget (total g e y) ≤ (5+3*45^3*1025^4)*(inputBits g e y)^4 := by
  let U := 2+g+e+y
  let T := total g e y
  let b := inputBits g e y
  have hb : 1 ≤ b := Nat.le_add_left _ _
  have hlt : U < 2^b := Nat.lt_log2_self
  have hc : 1 ≤ (2 : ℕ)^1024 := @Nat.one_le_two_pow 1024
  have hT : T ≤ 2^1024*U := by
    change g+e+y+2^1024 ≤ 2^1024*(2+g+e+y)
    generalize (2:ℕ)^1024 = k at hc ⊢
    nlinarith only [Nat.mul_le_mul_right (g+e+y) hc, hc]
  have hT₀ : T ≠ 0 := by
    have h₁ : 2^1024 ≤ T := Nat.le_add_left _ _
    exact ne_of_gt (lt_of_lt_of_le hc h₁)
  have hTlt : T < (2 : ℕ)^(1024+b) := by
    rw [pow_add]
    exact hT.trans_lt (Nat.mul_lt_mul_of_pos_left hlt hc)
  have hbits : T.log2+1 ≤ 1025*b := by
    have h := (Nat.log2_lt hT₀).mpr hTlt
    omega
  have hpow := Nat.pow_le_pow_left hbits 4
  have hpow' : 1 ≤ b^4 := Nat.one_le_pow 4 b hb
  change 5+3*45^3*(T.log2+1)^4 ≤ (5+3*45^3*1025^4)*b^4
  nlinarith only [hpow,hpow']

def Step.registers (w : Step) : List ℤ :=
  [w.xNum,w.xDen,w.yNum,w.yDen,w.nextNum,w.nextDen]

def IntegerTrace.registers (w : IntegerTrace) : List ℤ :=
  w.first.registers ++ w.second.registers ++ [w.s₀,w.t₀,w.A,w.s,w.t]

private theorem Step.registers_bound {w : Step} {B : ℕ} (h : w.Bounded B) :
    ∀ v ∈ w.registers, v.natAbs ≤ B := by
  rcases h with ⟨ha,hb,hc⟩
  intro v hv
  simp only [Step.registers,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl
  · exact (le_max_left _ _).trans ha
  · exact (le_max_right _ _).trans ha
  · exact (le_max_left _ _).trans hb
  · exact (le_max_right _ _).trans hb
  · exact (le_max_left _ _).trans hc
  · exact (le_max_right _ _).trans hc

theorem IntegerTrace.all_registers_bound {w : IntegerTrace} {B : ℕ} (h : w.Bounded B) :
    ∀ v ∈ w.registers, v.natAbs ≤ B := by
  intro v hv
  simp only [IntegerTrace.registers,List.mem_append] at hv
  rcases hv with (h₁|h₂)|h₃
  · exact Step.registers_bound h.1 v h₁
  · exact Step.registers_bound h.2.1 v h₂
  · exact h.2.2 v h₃

/-- One magnitude bit for zero and one sign bit for each integer. -/
def IntegerTrace.bitCost (w : IntegerTrace) :=
  (w.registers.map (fun z => z.natAbs.log2+2)).sum

theorem IntegerTrace.cost_bound {w : IntegerTrace} {p : ℕ} (h : w.Bounded (2^p)) :
    w.bitCost ≤ 17*(p+2) := by
  let xs := w.registers.map (fun z => z.natAbs.log2+2)
  have hlen : xs.length = 17 := rfl
  have hb : ∀ t ∈ xs, t ≤ p+2 := by
    intro t ht
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
    have hm := IntegerTrace.all_registers_bound h v hv
    by_cases hz : v.natAbs = 0
    · simp [hz]
    · have he := (Nat.log2_lt hz).mpr (hm.trans_lt <|
          pow_lt_pow_right₀ (by decide : 1 < (2:ℕ)) (Nat.lt_succ_self p))
      omega
  have hs := List.sum_le_card_nsmul xs (p+2) hb
  rw [hlen] at hs
  exact hs

/-- Total magnitude and sign bits of the 17 primary integer registers.
Auxiliary Bézout, order, and divisibility certificates are additional coordinates
introduced by polynomial compilation. -/
theorem short_integer_registers (hc : Cyclic) (hq : Quadratic) (g e : ℕ) :
    ∃ w : IntegerTrace, IntegerAccepts g e (g^e) w ∧
      w.bitCost ≤ 17*((5+3*45^3*1025^4)*(inputBits g e (g^e))^4+2) := by
  obtain ⟨w,hw,hB⟩ := integer_complete hc hq g e
  exact ⟨w, hw, (IntegerTrace.cost_bound hB).trans <|
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (budget_input_bits _ _ _) _)⟩

end DiophantineNP.PowerTests
