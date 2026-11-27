import DiophantineNP.LaurentBounds
import DiophantineNP.Fourier
import Mathlib.Tactic.FieldSimp

/-! # Evaluation of the certified Laurent expansions

An integer exponent vector acts multiplicatively under evaluation. The lemmas
below evaluate the integral expansions and identify the projected numerator
with the normalized average on the full cyclic grid. The normalized expression
uses the syntax-generated denominator of `LaurentBounds`.
-/

namespace DiophantineNP.LaurentBounds

open Finset

variable {d : ℕ} {K : Type*} [Field K]

noncomputable section

/-- A multiplicative assignment of weights to exponent vectors. -/
abbrev Character (d : ℕ) (K : Type*) [Field K] := (Fin d → ℤ) →+ Additive K

/-- Usual Laurent monomial evaluation at a tuple of nonzero coordinates. -/
def coordinateCharacter (x : Fin d → Kˣ) : Character d K where
  toFun v := Additive.ofMul (∏ j, (x j : K) ^ v j)
  map_zero' := by apply Additive.toMul.injective; simp
  map_add' a b := by
    apply Additive.toMul.injective
    simp [Pi.add_apply, zpow_add₀ (Units.ne_zero _), Finset.prod_mul_distrib, toMul_add]

namespace Raw

/-- Evaluate a raw integral numerator at the given monomial weights. -/
def evaluate (P : Raw d) (χ : (Fin d → ℤ) → K) : K := ∑ t, (P.coeff t : K) * χ (P.exponent t)

lemma evaluate_atom (a : ℤ) (v : Fin d → ℤ) (χ : (Fin d → ℤ) → K) :
    (atom a v).evaluate χ = a * χ v := by simp [evaluate, atom]

lemma evaluate_scale (P : Raw d) (a : ℤ) (χ : (Fin d → ℤ) → K) :
    (P.scale a).evaluate χ = a * P.evaluate χ := by
  simp [scale, evaluate, Int.cast_mul, Finset.mul_sum, mul_assoc]

lemma evaluate_plus (P Q : Raw d) (χ : (Fin d → ℤ) → K) :
    (P.plus Q).evaluate χ = P.evaluate χ + Q.evaluate χ := by
  simp [plus, evaluate, Fintype.sum_sum_type]

lemma evaluate_mul (P Q : Raw d) (χ : Character d K) :
    (P.mul Q).evaluate (fun v => (χ v).toMul) =
    P.evaluate (fun v => (χ v).toMul) * Q.evaluate (fun v => (χ v).toMul) := by
  simp only [evaluate, mul, Fintype.sum_prod_type, Int.cast_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  change _ * (χ (P.exponent t + Q.exponent u)).toMul = _
  rw [map_add, toMul_add]
  ring

lemma evaluate_pow (P : Raw d) (n : ℕ) (χ : Character d K) :
    (P.pow n).evaluate (fun v => (χ v).toMul) = (P.evaluate (fun v => (χ v).toMul)) ^ n := by
  induction n with
  | zero => simp [pow, evaluate_atom, ← Pi.zero_def]
  | succ n h => simp only [pow, evaluate_mul, pow_succ, h]

lemma evaluate_tailTerm (P : Raw d) (D n i : ℕ) (χ : Character d K) :
    (P.tailTerm D n i).evaluate (fun v => (χ v).toMul) =
      (D + P.evaluate (fun v => (χ v).toMul))^i *
      (D - P.evaluate (fun v => (χ v).toMul))^(n-i) := by
  simp [tailTerm, evaluate_mul, evaluate_pow, evaluate_plus, evaluate_atom,
    evaluate_scale, ← Pi.zero_def, sub_eq_add_neg]

lemma evaluate_tail (P : Raw d) (D n k : ℕ) (χ : Character d K) :
    (P.tail D n k).evaluate (fun v => (χ v).toMul) =
    ∑ i : Fin (n+1), if k ≤ i.val then (n.choose i.val : K) *
      (D + P.evaluate (fun v => (χ v).toMul))^i.val *
      (D - P.evaluate (fun v => (χ v).toMul))^(n-i.val) else 0 := by
  let T := fun i : Fin (n+1) => P.tailTerm D n i
  change (∑ t : (i : Fin (n+1)) × (T i).terms,
    ((if k ≤ t.1.val then n.choose t.1.val * (T t.1).coeff t.2 else 0 : ℤ) : K) * _) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : k ≤ i.val
  · simp only [if_pos hi, Int.cast_mul, Int.cast_natCast, mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    exact evaluate_tailTerm P D n i χ
  · simp [hi]

/-- At scalar arguments the entire Fourier kernel leaf reduces to a geometric
series, with the constant-ratio-one branch kept explicit. -/
lemma evaluate_geometric [DecidableEq K] (j : Fin d) (stride J : ℕ) (χ : Character d K) :
    (geometric j stride J).evaluate (fun v => (χ v).toMul) =
      let r := 2 * (χ (step j stride)).toMul
      if r = 1 then (J : K) else (r^J-1)/(r-1) := by
  let r := 2 * (χ (step j stride)).toMul
  have he : (geometric j stride J).evaluate (fun v => (χ v).toMul) =
      ∑ i ∈ range J, r^i := by
    change (∑ i : Fin J, (((2 : ℤ)^i.val : ℤ) : K) * (χ (i.val • step j stride)).toMul) = _
    simp only [map_nsmul, toMul_nsmul, Int.cast_pow, Int.cast_ofNat]
    rw [← Fin.sum_univ_eq_sum_range (fun i => r^i)]
    simp [r, mul_pow]
  rw [he]
  change _ = if r = 1 then _ else _
  by_cases hr : r = 1
  · simp [hr]
  · rw [if_neg hr, eq_div_iff (sub_ne_zero.mpr hr), geom_sum_mul]

/-- Remove the exponent in the averaged coordinate. -/
def without (v : Fin d → ℤ) (j : Fin d) : Fin d → ℤ := fun k => if k = j then 0 else v k

/-- For arbitrary complex weights on the remaining coordinates, cyclic projection
is exactly the normalized root-of-unity mean. -/
theorem evaluate_project (P : Raw d) (j : Fin d) {m : ℕ} [NeZero m]
    (χ : (Fin d → ℤ) → ℂ) :
    (P.project j m).evaluate χ =
    (m : ℂ)⁻¹ * ∑ k : ZMod m, P.evaluate
      (fun v => χ (without v j) * ZMod.stdAddChar ((v j : ZMod m) * k)) := by
  symm
  unfold evaluate
  simp only [← mul_assoc]
  rw [DiophantineNP.Fourier.laurent_mean]
  apply Finset.sum_congr rfl
  intro t _
  change (if (m : ℤ) ∣ P.exponent t j then (P.coeff t : ℂ) * χ (without (P.exponent t) j) else 0) =
    ((if (m : ℤ) ∣ P.exponent t j then P.coeff t else 0 : ℤ) : ℂ) * χ (without (P.exponent t) j)
  split <;> simp

end Raw


/-- Rational Laurent expression normalized by its computed common denominator. -/
def Expr.evaluate (f : Expr d) (χ : Character d K) : K :=
  f.expand.evaluate (fun v => (χ v).toMul) / (f.bounds.denominator : K)

/-- The geometric leaf needs one scalar power and one division in the nonconstant case. -/
lemma Expr.evaluate_geometric [DecidableEq K] (j : Fin d) (stride J : ℕ) (χ : Character d K) :
    (Expr.geometric j stride J).evaluate χ =
      let r := 2 * (χ (Raw.step j stride)).toMul
      if r = 1 then (J : K) else (r^J-1)/(r-1) := by
  simp [evaluate, expand, bounds, Raw.evaluate_geometric]

lemma Expr.evaluate_mul (f g : Expr d) (χ : Character d K) :
    (f.mul g).evaluate χ = f.evaluate χ * g.evaluate χ := by
  simp [evaluate, expand, bounds, Raw.evaluate_mul, div_mul_div_comm]

lemma Expr.evaluate_add [CharZero K] (f g : Expr d) (χ : Character d K) :
    (f.add g).evaluate χ = f.evaluate χ + g.evaluate χ := by
  have hf : (f.bounds.denominator : K) ≠ 0 := by exact_mod_cast f.denominator_pos.ne'
  have hg : (g.bounds.denominator : K) ≠ 0 := by exact_mod_cast g.denominator_pos.ne'
  simp [evaluate, expand, bounds, Raw.evaluate_plus, Raw.evaluate_scale]
  field_simp

lemma Expr.evaluate_pow (f : Expr d) (n : ℕ) (χ : Character d K) :
    (f.pow n).evaluate χ = (f.evaluate χ) ^ n := by
  simp [evaluate, expand, bounds, Raw.evaluate_pow, div_pow]

/-- This is the binomial-tail polynomial at a normalized expression argument. -/
theorem Expr.evaluate_threshold [CharZero K] (f : Expr d) (n k : ℕ) (χ : Character d K) :
    (f.threshold n k).evaluate χ = ∑ i : Fin (n+1), if k ≤ i.val then
      (n.choose i.val : K) * ((1 + f.evaluate χ)/2)^i.val *
      ((1 - f.evaluate χ)/2)^(n-i.val) else 0 := by
  let D : K := f.bounds.denominator
  let V := f.expand.evaluate (fun v => (χ v).toMul)
  have hD : D ≠ 0 := by dsimp [D]; exact_mod_cast f.denominator_pos.ne'
  have hplus : (1 + V / D) / 2 = (D+V)/(2*D) := by field_simp
  have hminus : (1 - V / D) / 2 = (D-V)/(2*D) := by field_simp
  simp only [evaluate, expand, bounds, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Raw.evaluate_tail]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : k ≤ i.val
  · simp only [if_pos hi]
    change _ / (2*D)^n = (n.choose i.val : K) * ((1+V/D)/2)^i.val * ((1-V/D)/2)^(n-i.val)
    have hi' : i.val + (n-i.val) = n := by have := i.isLt; omega
    have hfac : (2*D)^i.val * (2*D)^(n-i.val) = (2*D)^n := by rw [← pow_add, hi']
    rw [hplus,hminus, div_pow, div_pow, ← hfac]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · simp [hi]

end
end DiophantineNP.LaurentBounds
