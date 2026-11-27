import DiophantineNP.Fourier
import Mathlib.Data.Int.Interval

/-! # The ideal four-coordinate Fourier readout

After replacing the real selectors by their intended bits, the four grid
coordinates encode a binary label, a signed frequency, a balanced quotient,
and a balanced remainder. Every true output position contributes exactly
`8*J*2^i` to the unnormalized sum.
-/

namespace DiophantineNP.BinaryKernel

open Finset
open scoped BigOperators

abbrev period (B : ℕ) := 2*B+1

/-- Shift a least residue into the complete centered interval [-B,B]. -/
def centered {B : ℕ} (k : ZMod (period B)) : ℤ :=
  (((k+B).val:ℕ):ℤ)-B

private theorem centered_cast {B : ℕ} (k : ZMod (period B)) :
    ((centered k : ℤ) : ZMod (period B)) = k := by
  simp [centered]

private theorem centered_range {B : ℕ} (k : ZMod (period B)) : |centered k| ≤ B := by
  have h := (k+B).val_lt
  unfold period at h
  rw [centered, abs_le]
  omega

private theorem sum_balanced {B p : ℤ} (hB : 0 ≤ B) (hp : |p| ≤ B*B)
    (f : ℤ → ℂ) :
    ∃ t₀ q₀ : ℤ, p = (2*B+1)*q₀+t₀ ∧
      (∑ q ∈ Icc (-B) B, ∑ t ∈ Icc (-B) B,
        if p = (2*B+1)*q+t then f t else 0) = f t₀ := by
  obtain ⟨⟨q₀,t₀⟩, ht, unique⟩ := Fourier.balanced_division B p hB
  dsimp only at ht
  obtain ⟨htlo,hthi,he⟩ := ht
  have hq := Fourier.balanced_quotient_bounds B p q₀ t₀ hB (abs_le.mp hp) ⟨htlo,hthi⟩ he
  have hu (q t : ℤ) (hₜ : t ∈ Icc (-B) B) (h : p=(2*B+1)*q+t) : q=q₀ ∧ t=t₀ := by
    have r := unique (q,t) ⟨(mem_Icc.mp hₜ).1,(mem_Icc.mp hₜ).2,h⟩
    exact Prod.mk.inj r
  refine ⟨t₀,q₀,he,?_⟩
  rw [sum_eq_single_of_mem q₀ (mem_Icc.mpr hq)]
  · rw [sum_eq_single_of_mem t₀ (mem_Icc.mpr ⟨htlo,hthi⟩), if_pos he]
    intro t ht hne
    exact if_neg (fun e => hne (hu _ _ ht e).2)
  · intro q _ hne
    apply sum_eq_zero
    intro t ht
    exact if_neg (fun e => hne (hu _ _ ht e).1)

/-- A single signed arc's contribution before summing frequencies. -/
noncomputable def arcTerm {B : ℕ} (i k : ZMod (period B)) (s : Bool) : ℂ :=
  ∑ q ∈ Icc (-(B:ℤ)) B, ∑ t ∈ Icc (-(B:ℤ)) B,
    if (i.val:ℤ)*centered k = ((period B:ℕ):ℤ)*q+t then
      ∑ b : ZMod (period B), (2:ℂ)^b.val * ZMod.stdAddChar
        (if s then -((t-b.val*centered k : ℤ) : ZMod (period B))
         else ((t-b.val*centered k : ℤ) : ZMod (period B)))
    else 0

private theorem arcTerm_eq {B : ℕ} (i k : ZMod (period B)) (hi : i.val ≤ B) (s : Bool) :
    arcTerm i k s = ∑ b : ZMod (period B), (2:ℂ)^b.val * ZMod.stdAddChar
      ((if s then -(i-b) else i-b) * k) := by
  have hp : |(i.val:ℤ)*centered k| ≤ (B:ℤ)*B := by
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
    exact mul_le_mul (by exact_mod_cast hi) (centered_range k) (abs_nonneg _) (Int.natCast_nonneg _)
  let f (t : ℤ) := ∑ b : ZMod (period B), (2:ℂ)^b.val * ZMod.stdAddChar
      (if s then -((t-b.val*centered k : ℤ) : ZMod (period B))
       else ((t-b.val*centered k : ℤ) : ZMod (period B)))
  obtain ⟨t,q,he,hs⟩ := sum_balanced (Int.natCast_nonneg B) hp f
  have hc : ((period B:ℕ):ℤ) = 2*(B:ℤ)+1 := by simp [period]
  unfold arcTerm
  rw [hc,hs]
  apply Finset.sum_congr rfl
  intro b _
  have h := Fourier.balanced_phase (J := period B) (i.val:ℤ) (centered k) q t (b.val:ℤ) (hc ▸ he)
  have heq : ((t-b.val*centered k : ℤ) : ZMod (period B)) = (i-b)*k := by
    calc
      _ = (((i.val:ℤ)-(b.val:ℤ):ℤ):ZMod (period B))*(centered k:ZMod (period B)) := h
      _ = _ := by simp [centered_cast]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, heq, neg_mul]

theorem sum_arcTerm {B : ℕ} (i : ZMod (period B)) (hi : i.val ≤ B) (s : Bool) :
    (∑ k : ZMod (period B), arcTerm i k s) = (period B : ℂ)*(2:ℂ)^i.val := by
  simp_rw [fun k => arcTerm_eq i k hi s]
  exact Fourier.signed_weight s (fun b => (2:ℂ)^b.val) i

/-- Ideal kernel with the equality selector, both copies of the label and
quotient, and the common-sign selector on the frequency and remainder. -/
theorem ideal_sum {B : ℕ} (truth : Finset (ZMod (period B)))
    (ht : ∀ i ∈ truth, i.val ≤ B) :
    (∑ i ∈ truth, ∑ _z : Bool, ∑ _u : Bool, ∑ w : Bool, ∑ v : Bool,
      if w=v then ∑ k : ZMod (period B), arcTerm i k w else 0) =
      (8*(period B:ℂ))*(∑ i ∈ truth, (2:ℂ)^i.val) := by
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro i hi
  simp [sum_arcTerm i (ht i hi)]
  ring

/-- Uniform pointwise replacement of selectors bounds the error on the
*entire* grid (including points outside the windows). -/
theorem grid_sum_error {G : Type*} [Fintype G]
    (actual ideal : G → ℝ) (w : G → ℂ) {ε K : ℝ} (hε : 0 ≤ ε)
    (hs : ∀ z, |actual z-ideal z| ≤ 7*ε) (hw : ∀ z, ‖w z‖ ≤ K) :
    ‖(∑ z, (actual z:ℂ)*w z) - ∑ z, (ideal z:ℂ)*w z‖ ≤
      Fintype.card G * (7*ε*K) := by
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ _z : G, 7*ε*K := by
      apply norm_sum_le_of_le
      intro z _
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hs z) (hw z) (norm_nonneg _) (by positivity)
    _ = _ := by simp

/-- A selected coordinate of the M-grid has index s(Jr+t), with
Jr=M/4. Raising to M/J removes the quarter-period offset. -/
theorem quarter_phase {M J d : ℕ} [NeZero M] [NeZero J]
    (hm : M = J*d) (s r t : ℤ) :
    ZMod.stdAddChar ((s*((J:ℤ)*r+t):ℤ):ZMod M)^d =
      ZMod.stdAddChar ((s*t:ℤ):ZMod J) := by
  have hd : (d:ℂ) ≠ 0 := by
    have hh : d ≠ 0 := by intro h; simp [h] at hm; exact NeZero.ne M hm
    exact_mod_cast hh
  have hJ : (J:ℂ) ≠ 0 := NeZero.ne _
  have hmc : (M:ℂ) = (J:ℂ)*d := by exact_mod_cast hm
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_nat_mul]
  have hphase : (d:ℂ)*(2*(Real.pi:ℂ)*Complex.I*((s*((J:ℤ)*r+t):ℤ):ℂ)/(M:ℂ)) =
      ((s*r:ℤ):ℂ)*(2*(Real.pi:ℂ)*Complex.I) +
        2*(Real.pi:ℂ)*Complex.I*((s*t:ℤ):ℂ)/(J:ℂ) := by
    rw [hmc]
    push_cast
    field_simp
  rw [hphase, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- Exact phase of the b-th geometric-series term in the manuscript's
kernel whenever the frequency and remainder use the same sign s. -/
theorem carrier_term {M J d : ℕ} [NeZero M] [NeZero J] (hm : M = J*d)
    (s r t k : ℤ) (b : ℕ) :
    ZMod.stdAddChar ((s*((J:ℤ)*r+t):ℤ):ZMod M)^d *
      (2*(ZMod.stdAddChar ((s*((J:ℤ)*r+k):ℤ):ZMod M)^d)⁻¹)^b =
      (2:ℂ)^b * ZMod.stdAddChar ((s*(t-(b:ℤ)*k):ℤ):ZMod J) := by
  rw [quarter_phase hm, quarter_phase hm, mul_pow, inv_pow,
    ← AddChar.map_nsmul_eq_pow, ← AddChar.map_neg_eq_inv]
  rw [mul_left_comm, ← AddChar.map_add_eq_mul]
  congr 2
  push_cast
  simp only [nsmul_eq_mul]
  ring

/-- After the four root averages are undone, the explicit choice of bit
precision makes the total selector error less than one quarter. -/
theorem readout_precision (M J q : ℕ) (hJ : 0 < J)
    (hq : J+4*(M.log2+1)+4 ≤ q) :
    7*(M:ℝ)^4*(2:ℝ)^J/((8*(J:ℝ))*(2:ℝ)^q) < 1/4 := by
  have hm := Nat.lt_log2_self (n := M)
  have h₁ := Nat.pow_le_pow_left hm.le 4
  have h₂ : 16*M^4*2^J ≤ 2^q := by
    apply le_trans _ (Nat.pow_le_pow_right (by decide : 0<2) hq)
    calc
      _ ≤ 16*(2^(M.log2+1))^4*2^J := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 16 h₁)
      _ = _ := by
        conv_rhs => rw [pow_add, pow_add, mul_comm 4 (M.log2+1), pow_mul]
        ring
  have hreal : 16*(M:ℝ)^4*(2:ℝ)^J ≤ (2:ℝ)^q := by exact_mod_cast h₂
  have hJR : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hpos : 0 < (2:ℝ)^q := by positivity
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_right hJR hpos.le]

end DiophantineNP.BinaryKernel
