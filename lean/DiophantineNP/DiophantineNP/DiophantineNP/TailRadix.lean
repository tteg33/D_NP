import DiophantineNP.Extraction
import DiophantineNP.Threshold

/-!
# Exact signed binomial-tail evaluation

The coefficient list below is proof data. The evaluator only raises integers
to powers, rounds one quotient, and takes one centered residue.
-/
namespace DiophantineNP.TailRadix
open Extraction

/-- The residue of a polynomial evaluation modulo `z-1` is its coefficient sum. -/
private theorem eval_mod_radix_sub_one (cs : List Int) (z : Int) :
    ∃ q : Int, evaluate z cs = cs.sum + (z-1)*q := by
  induction cs with
  | nil => exact ⟨0, by simp [evaluate]⟩
  | cons a cs ih =>
    obtain ⟨q,hq⟩ := ih
    refine ⟨cs.sum + z*q, ?_⟩
    simp only [evaluate, List.sum_cons, hq]
    grind

/-- After the low digits are rounded away, the modulus `z-1` adds the
remaining signed digits. This applies to arbitrary integer coefficients. -/
theorem extract_tail (lo hi : List Int) (z : Int) (h : 2*mass (lo++hi) < z-1) :
    centered (nearest (evaluate z (lo++hi)) (z^lo.length)) (z-1) = hi.sum := by
  rw [mass_append] at h
  have h0 := mass_nonneg lo
  have h1 := mass_nonneg hi
  rw [nearest_append _ _ _ (by omega)]
  obtain ⟨q, hq⟩ := eval_mod_radix_sub_one hi z
  rw [hq]
  have hbounds : -mass hi ≤ hi.sum ∧ hi.sum ≤ mass hi := by
    clear h h1 hq
    induction hi with
    | nil => simp [mass]
    | cons a hi ih =>
      have := abs_bounds a
      simp only [List.sum_cons, mass]
      grind
  apply centered_eq_of_decomposition <;> omega

theorem extract_dropped_sum (cs : List Int) (k : Nat) (z : Int)
    (hk : k ≤ cs.length) (h : 2*mass cs < z-1) :
    centered (nearest (evaluate z cs) (z^k)) (z-1) = (cs.drop k).sum := by
  have heq := List.take_append_drop k cs
  have hlen : (cs.take k).length = k := by rw [List.length_take]; omega
  simpa only [heq, hlen] using extract_tail (cs.take k) (cs.drop k) z (by rwa [heq])

open Finset
open scoped BigOperators

private def table (n : ℕ) (f : ℕ → ℤ) : List Int := (List.range n).map f

private theorem table_succ (n : ℕ) (f : ℕ → ℤ) :
    table (n+1) f = table n f ++ [f n] := by simp [table, List.range_succ]

private theorem table_len (n : ℕ) (f : ℕ → ℤ) : (table n f).length = n := by simp [table]

private theorem table_eval (n : ℕ) (f : ℕ → ℤ) (z : ℤ) :
    evaluate z (table n f) = ∑ i ∈ range n, z^i * f i := by
  induction n with
  | zero => simp [table, evaluate]
  | succ n ih => simp [table_succ, evaluate_append, ih, table_len, evaluate, Finset.sum_range_succ]

private theorem table_mass (n : ℕ) (f : ℕ → ℤ) :
    mass (table n f) = ∑ i ∈ range n, |f i| := by
  induction n with
  | zero => simp [table, mass]
  | succ n ih =>
    rw [table_succ, mass_append, ih, Finset.sum_range_succ]
    simp [mass]

private theorem table_drop_sum (n k : ℕ) (hk : k ≤ n) (f : ℕ → ℤ) :
    ((table n f).drop k).sum = ∑ i ∈ Ico k n, f i := by
  induction n with
  | zero => simp [table]
  | succ n ih =>
    by_cases hkn : k ≤ n
    · rw [table_succ, List.drop_append_of_le_length (by rwa [table_len]),
        List.sum_append, ih hkn, Finset.sum_Ico_succ_top hkn]
      simp
    · have he : k = n+1 := by omega
      subst k
      rw [List.drop_eq_nil_of_le (by rw [table_len])]
      simp

/-- Coefficients of `(b+aX)^d`, using mathlib's binomial coefficient. -/
def binomialCoeffs (a b : ℤ) (d : ℕ) : List ℤ :=
  table (d+1) (fun i => a^i*b^(d-i)*(d.choose i))

theorem binomial_eval (a b z : ℤ) (d : ℕ) :
    evaluate z (binomialCoeffs a b d) = (b+a*z)^d := by
  rw [binomialCoeffs, table_eval, add_comm b, add_pow]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow]; ring

theorem binomial_mass (a b : ℤ) (d : ℕ) :
    mass (binomialCoeffs a b d) = (|a|+|b|)^d := by
  rw [binomialCoeffs, table_mass, add_pow]
  apply Finset.sum_congr rfl
  intro i hi
  simp [abs_mul]

/-- Exact numerator of a binomial tail, using the explicit radix in §3.1. -/
def tailNumerator (a b : Int) (d k : Nat) : Int :=
  let H : Int := ((2+a.natAbs+b.natAbs : Nat)^d : Nat)
  let z := 8*H+3
  centered (nearest ((b+a*z)^d) (z^k)) (z-1)

theorem tailNumerator_eq (a b : ℤ) (d k : ℕ) (hk : k ≤ d+1) :
    tailNumerator a b d k = ∑ i ∈ Ico k (d+1), a^i*b^(d-i)*(d.choose i) := by
  let H : Int := ((2+a.natAbs+b.natAbs : Nat)^d : Nat)
  let z := 8*H+3
  have h0 : 0 ≤ |a| + |b| := by positivity
  have hp : (|a|+|b|)^d ≤ H := by
    dsimp [H]
    push_cast
    exact pow_le_pow_left₀ h0 (by linarith) d
  have hH : 0 ≤ H := Int.natCast_nonneg _
  have hZ : 2*mass (binomialCoeffs a b d) < z-1 := by
    rw [binomial_mass]; dsimp [z]; omega
  have hlen : k ≤ (binomialCoeffs a b d).length := by rwa [binomialCoeffs, table_len]
  have ha := extract_dropped_sum (binomialCoeffs a b d) k z hlen hZ
  rw [binomial_eval, binomialCoeffs, table_drop_sum _ _ hk] at ha
  exact ha

/-- Dividing the integer numerator by the positive common denominator gives
the real threshold polynomial at every rational argument, including arguments
outside the probability interval. -/
theorem scalar_majority (num den : ℤ) (hden : 0 < den) (m : ℕ) :
    (tailNumerator (den+num) (den-num) (2*m+1) (m+1) : ℝ) /
      ((2*(den:ℝ))^(2*m+1)) = Threshold.majority m ((num:ℝ)/(den:ℝ)) := by
  have hden' : (den : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hden)
  rw [tailNumerator_eq _ _ _ _ (by omega), Threshold.majority, Threshold.lowerTail_eq_upper]
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr (by congr 1)
  intro i hi
  have hi' : i ≤ 2*m+1 := by have := Finset.mem_Ico.mp hi; omega
  have ha : (1+(num:ℝ)/den)/2 = ((den:ℝ)+num)/(2*den) := by field_simp
  have hb : (1-(num:ℝ)/den)/2 = ((den:ℝ)-num)/(2*den) := by field_simp
  rw [ha, hb, div_pow, div_pow]
  have hpow : (2*(den:ℝ))^(2*m+1) = (2*den)^i*(2*den)^(2*m+1-i) := by
    rw [← pow_add, Nat.add_sub_of_le hi']
  rw [hpow]
  ring

private theorem eval_nonneg (cs : List ℤ) (z : ℤ) (hz : 0 ≤ z)
    (hc : ∀ a ∈ cs, 0 ≤ a) : 0 ≤ evaluate z cs := by
  induction cs with
  | nil => simp [evaluate]
  | cons a cs ih =>
    have ha := hc a (by simp)
    have ht := ih (fun a ha => hc a (by simp [ha]))
    simp only [evaluate]
    positivity

/-- Positive-coefficient digit extraction uses ordinary floor and remainder.
The weaker strict bound on the total mass is enough in the unsigned case. -/
theorem extract_unsigned (cs : List ℤ) (k : ℕ) (z : ℤ) (hk : k ≤ cs.length)
    (hc : ∀ a ∈ cs, 0 ≤ a) (hm : mass cs < z) :
    (evaluate z cs / z^k) % z = cs[k]?.getD 0 := by
  let lo := cs.take k
  let hi := cs.drop k
  have hs : lo++hi = cs := List.take_append_drop k cs
  have hl : lo.length = k := by simp [lo, List.length_take, Nat.min_eq_left hk]
  have mlo := mass_nonneg lo
  have mhi := mass_nonneg hi
  have hsum : mass lo + mass hi = mass cs := by rw [← mass_append, hs]
  have hz : 0 < z := by omega
  have hlow : 0 ≤ evaluate z lo := eval_nonneg _ _ (by omega) (fun a ha => hc a (List.mem_of_mem_take ha))
  have he := (evaluate_scaled_bounds z hz lo).2
  rw [hl] at he
  have he' : evaluate z lo < z^k :=
    Int.lt_of_mul_lt_mul_left (lt_of_le_of_lt he
      (Int.mul_lt_mul_of_pos_right (by omega : mass lo < z) (Int.pow_pos hz))) (by omega)
  have ev : evaluate z cs = evaluate z lo + z^k*evaluate z hi := by
    conv_lhs => rw [← hs, evaluate_append, hl]
  rw [ev, Int.add_mul_ediv_left _ _ (by positivity), Int.ediv_eq_zero_of_lt hlow he', Int.zero_add]
  have hhead : hi[0]? = cs[k]? := by simp [hi, List.getElem?_drop]
  rw [← hhead]
  cases h : hi with
  | nil => simp [evaluate]
  | cons a rest =>
    have hm' := mass_nonneg rest
    have heq : mass hi = (a.natAbs : ℤ) + mass rest := by rw [h]; rfl
    have ha : a ∈ hi := by rw [h]; simp
    have hp := hc a (List.mem_of_mem_drop ha)
    have ha' := (abs_bounds a).2
    simp only [evaluate, Int.add_mul_emod_self_left, List.getElem?_cons_zero,
      Option.getD_some]
    exact Int.emod_eq_of_lt hp (by omega)

/-- The exact unsigned coefficient extraction used in the manuscript's
Wallis parameter: specialize `n=2*β`, `k=β`. -/
theorem choose_from_power (n k : ℕ) (hk : k ≤ n) :
    let R := (2 : ℤ)^(n+1)
    ((1+R)^n / R^k) % R = (n.choose k : ℤ) := by
  let cs := binomialCoeffs 1 1 n
  let R := (2 : ℤ)^(n+1)
  have hlen : k ≤ cs.length := by simpa [cs, binomialCoeffs, table_len] using (show k ≤ n+1 by omega)
  have hnon : ∀ c ∈ cs, 0 ≤ c := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    simp
  have hm : mass cs < R := by
    dsimp [cs, R]
    rw [binomial_mass]; norm_num
    exact pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self n)
  have hcoef : cs[k]? = some (n.choose k : ℤ) := by
    change ((List.range (n+1)).map _)[k]? = _
    simp [List.getElem?_map, List.getElem?_range (by omega : k < n+1)]
  have h := extract_unsigned cs k R hlen hnon hm
  rw [hcoef] at h
  simpa [cs, binomial_eval, R] using h

end DiophantineNP.TailRadix
