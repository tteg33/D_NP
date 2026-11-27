import DiophantineNP.LaurentExtraction
import DiophantineNP.LaurentSemantics
import DiophantineNP.RadixGrowth
import Mathlib.Algebra.Order.Floor.Ring

/-! # One scalar call for a multivariate Laurent projection

The dense coefficient list occurs only in the proof. The scalar algorithm takes
the support and magnitude bounds, the positive rational coordinates, and the
child's scalar evaluator. It never receives or enumerates Laurent coefficients.
-/
namespace DiophantineNP.ScalarProjection
open Extraction LaurentExtraction LaurentBounds Finset
open scoped BigOperators
noncomputable section

private def binSum {T : Type*} [Fintype T] (a : T → ℤ) (i : T → ℕ) (k : ℕ) :=
  ∑ t, if i t=k then a t else 0

private def dense {T : Type*} [Fintype T] (a : T → ℤ) (i : T → ℕ) (n : ℕ) : List ℤ :=
  (List.range n).map (binSum a i)

private theorem table_eval (f : ℕ → ℤ) (n : ℕ) (z : ℤ) :
    evaluate z ((List.range n).map f) = ∑ i ∈ range n, z^i*f i := by
  induction n with
  | zero => simp [evaluate]
  | succ n ih => simp [List.range_succ, evaluate_append, ih, evaluate, sum_range_succ]

private theorem table_mass (f : ℕ → ℤ) (n : ℕ) :
    mass ((List.range n).map f) = ∑ i ∈ range n, |f i| := by
  induction n with
  | zero => simp [mass]
  | succ n ih => simp [List.range_succ, mass_append, ih, mass, sum_range_succ]

private theorem weighted_sum {T : Type*} [Fintype T] (a : T → ℤ) (i : T → ℕ)
    (n : ℕ) (hn : ∀ t, i t < n) (f : ℕ → ℤ) :
    (∑ k ∈ range n, f k * binSum a i k) = ∑ t, f (i t)*a t := by
  simp only [binSum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  simp [mul_ite, hn t]

private theorem dense_mass {T : Type*} [Fintype T] (a : T → ℤ) (i : T → ℕ) (n : ℕ)
    (hn : ∀ t, i t < n) : mass (dense a i n) ≤ ∑ t, |a t| := by
  rw [dense, table_mass]
  calc
    _ ≤ ∑ k ∈ range n, ∑ t, |if i t = k then a t else 0| :=
      sum_le_sum (fun _ _ => abs_sum_le_sum_abs ..)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro t _
      simp [apply_ite (fun x : ℤ => |x|), hn t]

private theorem coefficient_get (cs : List ℤ) (k : ℕ) :
    coefficient cs k = cs[k]?.getD 0 := by
  induction cs generalizing k with
  | nil => simp [coefficient]
  | cons a cs ih => cases k <;> simp [coefficient, ih]

private theorem dense_coeff {T : Type*} [Fintype T] (a : T → ℤ) (i : T → ℕ)
    {n k : ℕ} (hk : k < n) : coefficient (dense a i n) k = binSum a i k := by
  simp [dense, coefficient_get, List.getElem?_map, List.getElem?_range hk]

/-- A version of signed extraction for finitely many (possibly repeated)
signed exponents. The algorithm only uses their aggregate scalar evaluation. -/
theorem sparse_extraction {T : Type*} [Fintype T] (a : T → ℤ) (e : T → ℤ)
    (m b : ℕ) (hm : 0 < m) (hb : m ∣ b) (he : ∀ t, -(b:ℤ) ≤ e t ∧ e t ≤ b)
    (z : ℤ) (hz : 1 < z) (h : 2*((2*b/m+1 : ℕ)*(∑ t, |a t|)) < z) :
    extractCoefficient ((∑ t, z^((b:ℤ)+e t).toNat*a t) *
      ((z^(m*(2*b/m+1))-1)/(z^m-1))) z (2*b) =
      ∑ t, if (m:ℤ) ∣ e t then a t else 0 := by
  let i t := ((b:ℤ)+e t).toNat
  have ix (t : T) : (i t : ℤ)-(b:ℤ)=e t := by dsimp [i]; have := he t; omega
  have hin (t : T) : i t < 2*b+1 := by have := he t; have := ix t; omega
  let cs := dense a i (2*b+1)
  have hm' := dense_mass a i (2*b+1) hin
  have hcs : 2*((2*b/m+1 : ℕ)*mass cs) < z := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm' (by positivity)) (by decide)) h
  have hev : evaluate z cs = ∑ t, z^(i t)*a t := (table_eval ..).trans (weighted_sum _ _ _ hin _)
  change extractCoefficient ((∑ t, z^(i t)*a t)*_) _ _ = _
  rw [← hev, extract_periodic_quotient _ _ _ _ _ hm hz hcs, sum_sampled_coefficients _ _ _ hm hb]
  let f (k : ℕ) : ℤ := if (m:ℤ) ∣ (k:ℤ)-b then 1 else 0
  calc
    _ = ∑ k ∈ range (2*b+1), f k * binSum a i k := by
      apply sum_congr rfl
      intro k hk
      rw [show coefficient cs k = binSum a i k from dense_coeff _ _ (mem_range.mp hk)]
      simp [f, ite_mul]
    _ = _ := by rw [weighted_sum _ _ _ hin]; simp [f, ix, ite_mul]

/-- The least positive multiple of m that is at least max(G,1). -/
def shiftBound (G m : ℕ) := m*((max G 1-1)/m+1)

theorem shift_properties {m : ℕ} (G : ℕ) (hm : 0 < m) :
    G ≤ shiftBound G m ∧ m ∣ shiftBound G m ∧ shiftBound G m ≤ max G 1 + m := by
  let g := max G 1 - 1
  have hd := Nat.mod_add_div g m
  have hr := Nat.mod_lt g hm
  have hmax : G ≤ max G 1 := le_max_left ..
  change G ≤ m*(g/m+1) ∧ m ∣ m*(g/m+1) ∧ m*(g/m+1) ≤ max G 1 + m
  refine ⟨?_, dvd_mul_right _ _, ?_⟩ <;> rw [Nat.mul_add, Nat.mul_one] <;>
    dsimp [g] at * <;> omega

/-- Scalar evaluation of an integral Laurent numerator at ordinary rationals. -/
def monomialValue {d : ℕ} (x : Fin d → ℚ) (v : Fin d → ℤ) : ℚ := ∏ i, (x i)^(v i)
def rawValue {d : ℕ} (P : Raw d) (x : Fin d → ℚ) := P.evaluate (monomialValue x)
def rationalPoint {d : ℕ} (p q : Fin d → ℕ) (i : Fin d) : ℚ := (p i : ℚ)/(q i : ℚ)

private theorem split_monomial {d : ℕ} (x : Fin d → ℚ) (z : ℚ) (v : Fin d → ℤ) (j : Fin d) :
    monomialValue (Function.update x j z) v = monomialValue x (Raw.without v j)*z^(v j) := by
  classical
  have eq (i : Fin d) : (Function.update x j z i)^(v i) =
      (x i)^(Raw.without v j i)*(if i=j then z^(v j) else 1) := by
    by_cases h : i=j <;> simp [h, Raw.without, Function.update]
  simp only [monomialValue, eq, prod_mul_distrib]
  simp

private def clearedCoeff {d : ℕ} (P : Raw d) (p q : Fin d → ℕ) (j : Fin d) (G : ℕ)
    (t : P.terms) : ℤ :=
  P.coeff t * ((∏ i, coordinateFactor (p i) (q i) G (Raw.without (P.exponent t) j i) : ℕ) : ℤ)

private theorem without_bounds {d H G : ℕ} {P : Raw d} (hs : P.Safe H G)
    (t : P.terms) (j i : Fin d) :
    -(G:ℤ) ≤ Raw.without (P.exponent t) j i ∧ Raw.without (P.exponent t) j i ≤ G := by
  have hb := hs.2 t i
  have ha := Extraction.abs_bounds (P.exponent t i)
  by_cases hij : i=j
  · simp [Raw.without,hij]
  · simp [Raw.without,hij]; omega

private theorem coeff_value {d H G : ℕ} (P : Raw d) (hs : P.Safe H G) (j : Fin d)
    (p q : Fin d → ℕ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (t : P.terms) :
    (RadixGrowth.clearFactor p q G : ℚ) *
        ((P.coeff t : ℚ)*monomialValue (rationalPoint p q) (Raw.without (P.exponent t) j)) =
      (clearedCoeff P p q j G t : ℚ) := by
  have h := clear_monomial p q G (Raw.without (P.exponent t) j) hp hq (without_bounds hs t j)
  unfold RadixGrowth.clearFactor monomialValue rationalPoint clearedCoeff
  push_cast at h ⊢
  linear_combination (P.coeff t : ℚ)*h

private theorem coeff_mass {d H G : ℕ} (P : Raw d) (hs : P.Safe H G) (j : Fin d)
    (p q : Fin d → ℕ) :
    (∑ t, |clearedCoeff P p q j G t|) ≤ (RadixGrowth.specializedHeight p q H G : ℤ) := by
  have h := specialized_mass_le univ p q G (fun t => Raw.without (P.exponent t) j) P.coeff
    (fun t _ => without_bounds hs t j)
  have hmass : (∑ t, |P.coeff t|) = (P.mass : ℤ) := by simp [Raw.mass]
  rw [hmass] at h
  apply h.trans
  unfold RadixGrowth.specializedHeight
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs.1) (by positivity)

private theorem eval_cleared {d H G : ℕ} (P : Raw d) (hs : P.Safe H G) (j : Fin d)
    (p q : Fin d → ℕ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (b z : ℕ) (hb : G ≤ b) (hz : 0 < z) :
    (RadixGrowth.clearFactor p q G : ℚ) * (z : ℚ)^b *
      rawValue P (Function.update (rationalPoint p q) j (z : ℚ)) =
      ((∑ t, (z:ℤ)^((b:ℤ)+P.exponent t j).toNat * clearedCoeff P p q j G t : ℤ) : ℚ) := by
  unfold rawValue Raw.evaluate
  rw [mul_sum, Int.cast_sum]
  apply sum_congr rfl
  intro t _
  have ha := hs.2 t j
  have he := Extraction.abs_bounds (P.exponent t j)
  have hcast : (z:ℚ) ≠ 0 := by exact_mod_cast hz.ne'
  have hpow : (z:ℚ)^b * (z:ℚ)^(P.exponent t j) = (z:ℚ)^((b:ℤ)+P.exponent t j).toNat := by
    rw [← zpow_natCast (z:ℚ) b, ← zpow_add₀ hcast,
      ← zpow_natCast (z:ℚ) (((b:ℤ)+P.exponent t j).toNat), Int.toNat_of_nonneg (by omega)]
  rw [split_monomial, Int.cast_mul, Int.cast_pow, Int.cast_natCast, ← hpow, ← coeff_value P hs j p q hp hq t]
  ring

private theorem eval_project_cleared {d H G : ℕ} (P : Raw d) (hs : P.Safe H G) (j : Fin d)
    (p q : Fin d → ℕ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (m : ℕ) :
    (RadixGrowth.clearFactor p q G : ℚ) * rawValue (P.project j m) (rationalPoint p q) =
      ((∑ t, if (m:ℤ) ∣ P.exponent t j then clearedCoeff P p q j G t else 0 : ℤ) : ℚ) := by
  unfold rawValue Raw.evaluate
  rw [mul_sum, Int.cast_sum]
  apply sum_congr rfl
  intro t _
  change _ * (Int.cast (if (m:ℤ) ∣ P.exponent t j then P.coeff t else 0) *
    monomialValue _ (Raw.without (P.exponent t) j)) = _
  split_ifs with h
  · exact coeff_value P hs j p q hp hq t
  · simp

/-- The entire scalar recipe. Its single invocation of `child` is at the
positive radix Z. This callback returns the normalized rational child value
with its distinguished coordinate replaced by Z. -/
def scalarRecipe {d : ℕ} (p q : Fin d → ℕ) (D H G m : ℕ) (child : ℕ → ℚ) : ℚ :=
  let b := shiftBound G m
  let z := RadixGrowth.radix p q H G b
  let C := RadixGrowth.clearFactor p q G
  let n := 2*b/m+1
  let v := ⌊(C:ℚ)*(z:ℚ)^b*((D:ℚ)*child z)⌋
  (extractCoefficient (v*(((z:ℤ)^(m*n)-1)/((z:ℤ)^m-1))) z (2*b) : ℚ) / ((C:ℚ)*D)

/-- The callback receives no coefficients. For arbitrary finitely represented
multivariate integer Laurent numerators and positive rational coordinates,
one scalar value gives exactly the normalized cyclic projection. -/
theorem scalarRecipe_raw {d D H G m : ℕ} (P : Raw d) (hs : P.Safe H G) (j : Fin d)
    (p q : Fin d → ℕ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (hD : 0 < D) (hm : 0 < m) :
    scalarRecipe p q D H G m (fun z =>
      rawValue P (Function.update (rationalPoint p q) j (z:ℚ)) / D) =
        rawValue (P.project j m) (rationalPoint p q) / D := by
  let b := shiftBound G m
  let z := RadixGrowth.radix p q H G b
  let C := RadixGrowth.clearFactor p q G
  let w := clearedCoeff P p q j G
  have hb := shift_properties G hm
  have hz : 1 < z := by dsimp [z, RadixGrowth.radix]; omega
  have hDZ : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hCZ : (C:ℚ) ≠ 0 := by
    dsimp [C, RadixGrowth.clearFactor]
    have pos : 0 < ∏ i, (p i*q i)^G :=
      Finset.prod_pos fun i _ => pow_pos (Nat.mul_pos (hp i) (hq i)) _
    exact_mod_cast pos.ne'
  have hbounds (t : P.terms) : -(b:ℤ) ≤ P.exponent t j ∧ P.exponent t j ≤ b := by
    have := hs.2 t j
    have := Extraction.abs_bounds (P.exponent t j)
    dsimp [b]
    omega
  have hmass := coeff_mass P hs j p q
  have hfactor : 2*b/m+1 ≤ 2*b+1 := by have := Nat.div_le_self (2*b) m; omega
  have hsparse : 2*((2*b/m+1 : ℕ)*(∑ t, |w t|)) < (z:ℤ) := by
    have hh := mul_le_mul_of_nonneg_left hmass (by positivity : (0:ℤ) ≤ (2*b/m+1 : ℕ))
    have hj := Nat.mul_le_mul_left (RadixGrowth.specializedHeight p q H G) hfactor
    have hj' : ((2*b/m+1 : ℕ) : ℤ) * (RadixGrowth.specializedHeight p q H G:ℤ) ≤
        ((RadixGrowth.specializedHeight p q H G * (2*b+1) : ℕ) : ℤ) := by
      exact_mod_cast (by simpa [Nat.mul_comm] using hj :
        (2*b/m+1)*RadixGrowth.specializedHeight p q H G ≤ _)
    change ∑ t, |w t| ≤ _ at hmass
    change _* (∑ t, |w t|) ≤ _ at hh
    have hz' : 2*((RadixGrowth.specializedHeight p q H G * (2*b+1) : ℕ):ℤ) < (z:ℤ) := by
      exact_mod_cast (show 2*(RadixGrowth.specializedHeight p q H G*(2*b+1)) < z by
        dsimp [z, RadixGrowth.radix]; omega)
    exact (mul_le_mul_of_nonneg_left (hh.trans hj') (by decide : (0:ℤ) ≤ 2 )).trans_lt hz'
  have hv := eval_cleared P hs j p q hp hq b z hb.1 (by omega)
  have hpval := eval_project_cleared P hs j p q hp hq m
  have hfloor : ⌊(C:ℚ)*(z:ℚ)^b*((D:ℚ)*
      (rawValue P (Function.update (rationalPoint p q) j (z:ℚ))/D))⌋ =
      ∑ t, (z:ℤ)^((b:ℤ)+P.exponent t j).toNat*w t := by
    rw [mul_comm (D:ℚ) (_ / _), div_mul_cancel₀ _ hDZ]
    change ⌊(RadixGrowth.clearFactor p q G : ℚ)*_ * _⌋ = _
    rw [hv, Int.floor_intCast]
  change ((extractCoefficient (⌊(C:ℚ)*(z:ℚ)^b*((D:ℚ)*_)⌋*_) z (2*b) : ℤ) : ℚ) / ((C:ℚ)*D) = _
  rw [hfloor, sparse_extraction w _ m b hm hb.2.1 hbounds z (by exact_mod_cast hz) hsparse]
  change ((∑ t, if (m:ℤ) ∣ P.exponent t j then clearedCoeff P p q j G t else 0 : ℤ) : ℚ) /
    ((C:ℚ)*D) = _
  rw [← hpval]
  change ((C:ℚ)*_)/((C:ℚ)*D) = _
  exact mul_div_mul_left _ _ hCZ

/-- Rational normalized value, convenient for scalar hardware; it agrees
definitionally with `Expr.evaluate` applied to the corresponding character. -/
def exprValue {d : ℕ} (e : Expr d) (x : Fin d → ℚ) : ℚ :=
  rawValue e.expand x / (e.bounds.denominator : ℚ)

theorem exprValue_eq_character {d : ℕ} (e : Expr d) (x : Fin d → ℚˣ) :
    exprValue e (fun i => (x i : ℚ)) = e.evaluate (coordinateCharacter x) := rfl

/-- Normalized one-child-call projection using only the expression's computed
bounds. This equality has no assumptions on the input Laurent expression. -/
theorem scalarRecipe_expr {d : ℕ} (e : Expr d) (j : Fin d) (m : ℕ+)
    (p q : Fin d → ℕ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    scalarRecipe p q e.bounds.denominator e.bounds.height e.bounds.radius m
      (fun z => exprValue e (Function.update (rationalPoint p q) j (z:ℚ))) =
        exprValue (e.project j m) (rationalPoint p q) :=
  scalarRecipe_raw e.expand e.bounds_sound j p q hp hq e.denominator_pos m.property

private theorem sparse_height {T : Type*} [Fintype T] (a : T → ℤ) (i : T → ℕ)
    (N : ℕ) (hi : ∀ t, i t ≤ N) (z : ℕ) (hz : 0 < z) :
    |∑ t, (z:ℤ)^(i t)*a t| ≤ (z:ℤ)^N * ∑ t, |a t| := by
  have h1 : 1 ≤ (z:ℤ) := by exact_mod_cast hz
  calc
    _ ≤ ∑ t, |(z:ℤ)^(i t)*a t| := abs_sum_le_sum_abs ..
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro t _
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ (z:ℤ)^(i t))]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 (hi t)) (abs_nonneg _)

/-- Magnitude of the scalar integer recovered from the callback, before the
geometric multiplier is attached. The bound uses the syntax radius and input
heights, irrespective of the number of terms of the expansion. -/
theorem cleared_callback_bound {d H G : ℕ} (P : Raw d) (hs : P.Safe H G) (j : Fin d)
    (p q : Fin d → ℕ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (b z : ℕ) (hb : G ≤ b) (hz : 0 < z) :
    |⌊(RadixGrowth.clearFactor p q G : ℚ)*(z:ℚ)^b*
      rawValue P (Function.update (rationalPoint p q) j (z:ℚ))⌋| ≤
      ((z^(2*b)*RadixGrowth.specializedHeight p q H G : ℕ) : ℤ) := by
  rw [eval_cleared P hs j p q hp hq b z hb hz, Int.floor_intCast, Nat.cast_mul, Nat.cast_pow]
  apply le_trans (sparse_height _ _ (2*b) ?_ z hz)
  · exact mul_le_mul_of_nonneg_left (coeff_mass P hs j p q) (by positivity)
  · intro t
    have := hs.2 t j
    have := Extraction.abs_bounds (P.exponent t j)
    omega

/-- Both radix powers and the positive callback argument have explicit bit costs.
The numerator exponent of the geometric quotient is `2*b+m`, even for G=0. -/
theorem scalarRecipe_growth {d : ℕ} (p q : Fin d → ℕ) (H G m : ℕ) (hm : 0 < m) :
    let b := shiftBound G m
    let z := RadixGrowth.radix p q H G b
    let h := bits H + 2*G*RadixGrowth.coordinateBits p q + bits (2*b+1) + 5
    b ≤ max G 1+m ∧ bits z ≤ h ∧ m*(2*b/m+1) = 2*b+m ∧
      bits (z^(m*(2*b/m+1))) ≤ (2*b+m)*h+1 := by
  dsimp only
  have h := shift_properties G hm
  have hd : m ∣ 2*shiftBound G m := dvd_mul_of_dvd_right h.2.1 _
  have hpow : m*(2*shiftBound G m/m+1) = 2*shiftBound G m+m := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm m, Nat.div_mul_cancel hd]
  refine ⟨h.2.2, RadixGrowth.radix_bits .., hpow, ?_⟩
  rw [hpow]
  exact RadixGrowth.radix_power_bits ..

end
end DiophantineNP.ScalarProjection
