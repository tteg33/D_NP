import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A binomial tail for the majority gate

An odd row of Pascal's triangle splits into two halves of equal mass.
Bounding each term by the one at the midpoint gives an elementary version
of the concentration estimate used in Section 3.1.
-/

namespace DiophantineNP.Threshold

open Finset
open scoped BigOperators

/-- Probability, with weights `a,b`, of at most `m` first outcomes in
`2*m+1` trials. The expression also makes sense outside probabilities. -/
noncomputable def lowerTail (m : ℕ) (a b : ℝ) : ℝ :=
  ∑ i ∈ range (m + 1), a ^ i * b ^ (2*m+1-i) * (2*m+1).choose i

/-- The usual upper tail, by exchanging successes and failures. -/
noncomputable def majority (m : ℕ) (t : ℝ) : ℝ :=
  lowerTail m ((1-t)/2) ((1+t)/2)

theorem lowerTail_nonneg (m : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ lowerTail m a b := by
  unfold lowerTail
  exact Finset.sum_nonneg fun i _ => by positivity

theorem lowerTail_eq_upper (m : ℕ) (a b : ℝ) :
    lowerTail m b a = ∑ i ∈ Ico (m+1) (2*m+2),
      a ^ i * b ^ (2*m+1-i) * (2*m+1).choose i := by
  let f (i : ℕ) : ℝ := a ^ i * b ^ (2*m+1-i) * (2*m+1).choose i
  calc
    lowerTail m b a = ∑ i ∈ range (m+1), f (2*m+1-i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h : i ≤ 2*m+1 := by have := Finset.mem_range.mp hi; omega
      simp only [f, Nat.sub_sub_self h, Nat.choose_symm h]
      ring
    _ = _ := by
      rw [Finset.range_eq_Ico, Finset.sum_Ico_reflect f 0 (by omega)]
      congr 1
      · congr 1; omega

theorem lowerTail_partition (m : ℕ) (a b : ℝ) :
    lowerTail m a b + lowerTail m b a = (a+b) ^ (2*m+1) := by
  rw [lowerTail_eq_upper m a b, lowerTail, add_pow]
  exact Finset.sum_range_add_sum_Ico _ (by omega)

theorem majority_range (m : ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    0 ≤ majority m t ∧ majority m t ≤ 1 := by
  obtain ⟨h₁,h₂⟩ := abs_le.mp ht
  have ha : 0 ≤ (1-t)/2 := by linarith
  have hb : 0 ≤ (1+t)/2 := by linarith
  have hp := lowerTail_partition m ((1-t)/2) ((1+t)/2)
  rw [show (1-t)/2 + (1+t)/2 = 1 by ring, one_pow] at hp
  exact ⟨lowerTail_nonneg _ ha hb, by unfold majority; linarith [lowerTail_nonneg m hb ha]⟩

/-- All terms of the tail are bounded by their middle monomial times
their respective binomial coefficient. -/
theorem lowerTail_bound (m : ℕ) {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    lowerTail m a b ≤ b * (4*a*b) ^ m := by
  have ha := hb.trans hba
  have hsum : (∑ i ∈ range (m+1), ((2*m+1).choose i : ℝ)) = (4 : ℝ)^m := by
    exact_mod_cast Nat.sum_range_choose_halfway m
  calc
    lowerTail m a b ≤ ∑ i ∈ range (m+1), (a^m * b^(m+1)) * (2*m+1).choose i := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hbpow := pow_le_pow_left₀ hb hba (m-i)
      calc
        a^i * b^(2*m+1-i) = (a^i * b^(m+1)) * b^(m-i) := by
          rw [show 2*m+1-i = (m+1)+(m-i) by omega, pow_add]; ring
        _ ≤ (a^i * b^(m+1)) * a^(m-i) := mul_le_mul_of_nonneg_left hbpow (by positivity)
        _ = a^m * b^(m+1) := by
          rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le hi']
    _ = _ := by rw [← Finset.mul_sum, hsum, mul_pow, mul_pow, pow_succ]; ring

/-- Error of the majority polynomial on either side of zero. -/
theorem majority_error (m : ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    |majority m t - (if 0 < t then 1 else 0)| ≤ (1-t^2)^m := by
  have hr := majority_range m ht
  obtain ⟨h₁,h₂⟩ := abs_le.mp ht
  have hbase : 0 ≤ 1 - t^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-t) (by linarith : 0 ≤ 1+t)]
  by_cases hs : 0 < t
  · rw [if_pos hs, abs_of_nonpos (by linarith [hr.2])]
    have h := lowerTail_bound m (a := (1+t)/2) (b := (1-t)/2) (by linarith) (by linarith)
    rw [show 4*((1+t)/2)*((1-t)/2) = 1-t^2 by ring] at h
    have hp := lowerTail_partition m ((1-t)/2) ((1+t)/2)
    rw [show (1-t)/2 + (1+t)/2 = 1 by ring, one_pow] at hp
    have hsmall := mul_le_mul_of_nonneg_right (by linarith : (1-t)/2 ≤ 1) (pow_nonneg hbase m)
    unfold majority
    linarith
  · rw [if_neg hs, sub_zero, abs_of_nonneg hr.1]
    have h := lowerTail_bound m (a := (1-t)/2) (b := (1+t)/2) (by linarith) (by linarith)
    rw [show 4*((1-t)/2)*((1+t)/2) = 1-t^2 by ring] at h
    exact h.trans (by simpa using mul_le_mul_of_nonneg_right (by linarith : (1+t)/2 ≤ 1) (pow_nonneg hbase m))

/-- Once the squared margin times the half-degree exceeds the requested
precision, the output differs from the target bit by less than 2^(-q). -/
theorem majority_precision (m q : ℕ) {t : ℝ} (ht : |t| ≤ 1)
    (hprecision : (q : ℝ) < m*t^2) :
    |majority m t - (if 0 < t then 1 else 0)| < ((2 : ℝ)^q)⁻¹ := by
  have hbase : 0 ≤ 1-t^2 := by
    obtain ⟨h₁,h₂⟩ := abs_le.mp ht
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-t) (by linarith : 0 ≤ 1+t)]
  have hlog : Real.log 2 ≤ 1 := by
    linarith [Real.log_lt_sub_one_of_pos (show (0:ℝ)<2 by norm_num) (show (2:ℝ)≠1 by norm_num)]
  calc
    _ ≤ (1-t^2)^m := majority_error m ht
    _ ≤ Real.exp (-(t^2)) ^ m := pow_le_pow_left₀ hbase (by linarith [Real.add_one_le_exp (-(t^2))]) m
    _ = Real.exp ((m:ℝ) * -(t^2)) := (Real.exp_nat_mul _ _).symm
    _ < Real.exp (-((q:ℝ)*Real.log 2)) := by
      apply Real.exp_lt_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ) ≤ q)]
    _ = _ := by rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- The explicit degree and margin in the draft satisfy the preceding
precision criterion. `l` may be any natural number, in particular the
binary length of `M`. -/
theorem draft_degree_precision (M q l : ℕ) (hM : 0 < M) {t : ℝ}
    (ht : |t| ≤ 1) (hmargin : 1 / (64*(M:ℝ)^4) ≤ |t|) :
    |majority (2^15*M^8*(q+20*l+100)) t - (if 0<t then 1 else 0)| < ((2:ℝ)^q)⁻¹ := by
  apply majority_precision _ _ ht
  have hpos : (0:ℝ) < M := by exact_mod_cast hM
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 1/(64*(M:ℝ)^4)) (abs_nonneg t)).2 hmargin
  rw [sq_abs] at hsq
  push_cast
  calc
    (q:ℝ) < 8*((q:ℝ)+20*l+100) := by linarith [Nat.cast_nonneg (α := ℝ) q, Nat.cast_nonneg (α := ℝ) l]
    _ = 32768*(M:ℝ)^8*((q:ℝ)+20*l+100)*(1/(64*(M:ℝ)^4))^2 := by
      field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by positivity)

end DiophantineNP.Threshold
