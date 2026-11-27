import DiophantineNP.EvaluatorGrowth

/-! # Exact integer evaluation of Laurent expressions -/

namespace DiophantineNP.Blueprint
open LaurentBounds ScalarProgram ScalarProjection FormulaLaurent
open scoped BigOperators
noncomputable section

/-- Bounds for the evaluator. The denominator is the one of `Expr.bounds`.
Height and radius are over-estimates that need only `+`, `*` and `^`
(no `max`, no absolute value). -/
def evalBounds {d : ℕ} : Expr d → Bounds
  | .scalar p q => ⟨q, p.natAbs^2 + 1, 0⟩
  | .monomial v => ⟨1, 1, ∑ j, (v j).natAbs⟩
  | .geometric _ s J => ⟨1, 2^J, J*s⟩
  | .neg f | .project f _ _ => evalBounds f
  | .add f g => ⟨(evalBounds f).denominator * (evalBounds g).denominator,
      (evalBounds g).denominator * (evalBounds f).height +
        (evalBounds f).denominator * (evalBounds g).height,
      (evalBounds f).radius + (evalBounds g).radius⟩
  | .mul f g => ⟨(evalBounds f).denominator * (evalBounds g).denominator,
      (evalBounds f).height * (evalBounds g).height,
      (evalBounds f).radius + (evalBounds g).radius⟩
  | .pow f n => ⟨(evalBounds f).denominator^n, (evalBounds f).height^n, n*(evalBounds f).radius⟩
  | .threshold f n _ => ⟨(2*(evalBounds f).denominator)^n,
      (2*((evalBounds f).denominator + (evalBounds f).height))^n, n*(evalBounds f).radius⟩

theorem evalBounds_denominator {d : ℕ} (e : Expr d) :
    (evalBounds e).denominator = e.bounds.denominator := by
  induction e <;> simp_all [evalBounds, Expr.bounds]

/-- The over-estimates are still valid support and mass bounds, so
`scalarRecipe_raw` applies with them. -/
theorem evalBounds_safe {d : ℕ} (e : Expr d) :
    e.expand.Safe (evalBounds e).height (evalBounds e).radius := by
  induction e with
  | scalar p q =>
    apply Raw.safe_atom
    · change p.natAbs ≤ p.natAbs^2 + 1
      nlinarith [Nat.zero_le (p.natAbs-1)]
    · simp [evalBounds]
  | monomial v =>
    apply Raw.safe_atom (by simp [evalBounds])
    intro j
    exact Finset.single_le_sum (f := fun i => (v i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  | geometric j s J =>
    have h := Raw.safe_geometric j s J
    have hp : 0 < 2^J := by positivity
    exact ⟨h.1.trans (by change max 1 (2^J-1) ≤ 2^J; omega),
      fun t i => (h.2 t i).trans (Nat.mul_le_mul_right s (Nat.sub_le _ _))⟩
  | neg f ih => simpa [Expr.expand, evalBounds] using Raw.safe_scale ih (-1)
  | add f g ihf ihg =>
    have h := Raw.safe_plus (Raw.safe_scale ihf (g.bounds.denominator : ℤ))
      (Raw.safe_scale ihg (f.bounds.denominator : ℤ))
    refine ⟨?_, fun t i => (h.2 t i).trans ?_⟩
    · simpa [Expr.expand, evalBounds, evalBounds_denominator] using h.1
    · change max _ _ ≤ _ + _
      omega
  | mul f g ihf ihg => exact Raw.safe_mul ihf ihg
  | pow f n ih => exact Raw.safe_pow ih n
  | threshold f n k ih =>
    simpa [Expr.expand, evalBounds, evalBounds_denominator] using
      Raw.safe_tail ih f.bounds.denominator n k
  | project f j m ih => exact Raw.safe_project ih j m

/-- `∑_{i<J} 2^i y^(J-i)`: the numerator of the geometric leaf. -/
def geomSum (y : ℤ) (J : ℕ) : ℤ := ∑ i ∈ Finset.range J, 2^i * y^(J-i)

/-- The same integer with two powers and one exact division, with no case
split in the program: `positiveDiv t t` is the indicator of `0 < t`. -/
theorem geomSum_closed (y : ℤ) (J : ℕ) :
    geomSum y J = positiveDiv ((y^J - 2^J) * y * (y-2)) ((y-2)^2) +
      (1 - positiveDiv ((y-2)^2) ((y-2)^2)) * ((J : ℤ) * 2^J) := by
  have step (n : ℕ) : geomSum y (n+1) = geomSum y n * y + 2^n * y := by
    unfold geomSum
    rw [Finset.sum_range_succ, Finset.sum_mul]
    simp only [Nat.add_sub_cancel_left, pow_one]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show n+1-i = (n-i)+1 by omega, pow_succ, mul_assoc]
  by_cases h : y = 2
  · subst y
    simp [positiveDiv]
    induction J with
    | zero => simp [geomSum]
    | succ n ih => rw [step, ih, pow_succ]; push_cast; ring
  · have hy : 0 < (y-2)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
    have ident (n : ℕ) : geomSum y n * (y-2) = (y^n - 2^n)*y := by
      induction n with
      | zero => simp [geomSum]
      | succ n ih =>
        rw [step, pow_succ, pow_succ]
        linear_combination y * ih
    have num : (y^J - 2^J) * y * (y-2) = geomSum y J * (y-2)^2 := by
      rw [← ident]; ring
    simp [positiveDiv, hy, num, Int.mul_ediv_cancel _ hy.ne', Int.ediv_self hy.ne']

/-- The integer `(∏ x)^G̃ * rawValue e.expand x`, where `G̃ = (evalBounds e).radius`,
computed without expanding anything. Each clause uses a bounded number of the
certified scalar operations. The projection clause is `scalarRecipe` with
`p = x`, `q = 1`: one recursive call at the radix. -/
def clearedNum {d : ℕ} : Expr d → (Fin d → ℕ) → ℤ
  | .scalar p _, _ => p
  | .monomial v, x => ∏ i, (x i : ℤ)^(((∑ j, (v j).natAbs : ℕ) : ℤ) + v i).toNat
  | .geometric j s J, x =>
      (∏ i, if i = j then (1 : ℤ) else (x i : ℤ)^(J*s)) * geomSum ((x j : ℤ)^s) J
  | .neg f, x => -clearedNum f x
  | .add f g, x =>
      let X : ℤ := ∏ i, (x i : ℤ)
      ((evalBounds g).denominator : ℤ) * X^(evalBounds g).radius * clearedNum f x +
        ((evalBounds f).denominator : ℤ) * X^(evalBounds f).radius * clearedNum g x
  | .mul f g, x => clearedNum f x * clearedNum g x
  | .pow f n, x => clearedNum f x ^ n
  | .threshold f n k, x =>
      let A : ℤ := (∏ i, (x i : ℤ))^(evalBounds f).radius * ((evalBounds f).denominator : ℤ)
      TailRadix.tailNumerator (A + clearedNum f x) (A - clearedNum f x) n k
  | .project f j m, x =>
      let G : ℕ := (evalBounds f).radius
      let m' : ℕ := m
      let b : ℕ := shiftBound G m'
      let z : ℕ := RadixGrowth.radix x (fun _ => 1) (evalBounds f).height G b
      let v : ℤ := (x j : ℤ)^G * (z : ℤ)^(b - G) * clearedNum f (Function.update x j z)
      Extraction.extractCoefficient
        (v * (((z : ℤ)^(m'*(2*b/m'+1)) - 1) / ((z : ℤ)^m' - 1))) (z : ℤ) (2*b)

/-- `TailRadix.tailNumerator_eq` asks for `k ≤ n+1`. Every threshold of
`packedExpr` has `n = 2*h+1` and `k = h+1`. -/
def WellFormed {d : ℕ} : Expr d → Prop
  | .scalar _ _ | .monomial _ | .geometric _ _ _ => True
  | .neg f | .pow f _ | .project f _ _ => WellFormed f
  | .add f g | .mul f g => WellFormed f ∧ WellFormed g
  | .threshold f n k => k ≤ n+1 ∧ WellFormed f

private def integerPointChar {d : ℕ} (x : Fin d → ℕ) (hx : ∀ i, 0 < x i) : Character d ℚ :=
  coordinateCharacter (fun i => Units.mk0 (x i : ℚ) (by exact_mod_cast (hx i).ne'))

private theorem rawValue_mul_at {d : ℕ} (P Q : Raw d) (x : Fin d → ℕ) (hx : ∀ i, 0 < x i) :
    rawValue (P.mul Q) (fun i => (x i : ℚ)) =
      rawValue P (fun i => (x i : ℚ)) * rawValue Q (fun i => (x i : ℚ)) :=
  Raw.evaluate_mul P Q (integerPointChar x hx)

private theorem rawValue_pow_at {d : ℕ} (P : Raw d) (n : ℕ) (x : Fin d → ℕ) (hx : ∀ i, 0 < x i) :
    rawValue (P.pow n) (fun i => (x i : ℚ)) = rawValue P (fun i => (x i : ℚ))^n :=
  Raw.evaluate_pow P n (integerPointChar x hx)

private theorem rawValue_tail_at {d : ℕ} (P : Raw d) (D n k : ℕ) (x : Fin d → ℕ)
    (hx : ∀ i, 0 < x i) :
    rawValue (P.tail D n k) (fun i => (x i : ℚ)) =
        ∑ i ∈ Finset.Ico k (n+1), (n.choose i : ℚ) *
          (D + rawValue P (fun j => (x j : ℚ)))^i * (D - rawValue P (fun j => (x j : ℚ)))^(n-i) := by
  let A := fun i : ℕ => (n.choose i : ℚ) *
    (D + rawValue P (fun j => (x j : ℚ)))^i * (D - rawValue P (fun j => (x j : ℚ)))^(n-i)
  have h : rawValue (P.tail D n k) (fun i => (x i : ℚ)) =
      ∑ i : Fin (n+1), if k ≤ i.val then A i else 0 :=
    Raw.evaluate_tail P D n k (integerPointChar x hx)
  rw [h, Fin.sum_univ_eq_sum_range (fun j : ℕ => if k ≤ j then A j else 0), ← Finset.sum_filter]
  have hf : (Finset.range (n+1)).filter (fun j => k ≤ j) = Finset.Ico k (n+1) := by
    ext
    simp [and_comm]
  rw [hf]

private theorem monomial_cleared {d : ℕ} (v : Fin d → ℤ) (x : Fin d → ℕ) (hx : ∀ i, 0 < x i) :
    (∏ i, (x i : ℚ)^(((∑ j, (v j).natAbs : ℕ) : ℤ) + v i).toNat) =
       (∏ i, (x i : ℚ))^(∑ j, (v j).natAbs) * monomialValue (fun i => (x i : ℚ)) v := by
  rw [monomialValue, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have ha : (v i).natAbs ≤ ∑ j, (v j).natAbs :=
    Finset.single_le_sum (f := fun j => (v j).natAbs) (by simp) (Finset.mem_univ i)
  have hb := Extraction.abs_bounds (v i)
  rw [← zpow_natCast (x i : ℚ) (((∑ j, (v j).natAbs : ℕ) : ℤ) + v i).toNat,
    Int.toNat_of_nonneg (by omega), zpow_add₀ (by exact_mod_cast (hx i).ne'), zpow_natCast]

private theorem geo_product_split {d : ℕ} (x : Fin d → ℕ) (j : Fin d) (n : ℕ) :
    (∏ i, (x i : ℚ))^n = (∏ i, if i=j then (1:ℚ) else (x i : ℚ)^n) * (x j : ℚ)^n := by
  have split (i : Fin d) : (x i : ℚ)^n = (if i=j then (1:ℚ) else (x i : ℚ)^n) *
      (if i=j then (x j : ℚ)^n else 1) := by by_cases h : i=j <;> simp [h]
  rw [← Finset.prod_pow]
  calc
    _ = ∏ i, ((if i=j then (1:ℚ) else (x i : ℚ)^n) * (if i=j then (x j : ℚ)^n else 1)) :=
      Finset.prod_congr rfl (fun i _ => split i)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

private theorem eval_geo_power {d : ℕ} (j : Fin d) (s J : ℕ) (x : Fin d → ℕ)
    (hx : ∀ i, 0 < x i) : rawValue (Raw.geometric j s J) (fun i => (x i : ℚ)) =
      ∑ i ∈ Finset.range J, (2:ℚ)^i * (((x j : ℚ)^s)⁻¹)^i := by
  let χ := integerPointChar x hx
  have hs : (χ (Raw.step j s)).toMul = (((x j : ℚ)^s)⁻¹) := by
    change (∏ i, (x i : ℚ) ^ (Raw.step j s i)) = _
    rw [Finset.prod_eq_single j]
    · simp [Raw.step]
    · intro i _ hi; simp [Raw.step, hi]
    · simp
  change (∑ i : Fin J, (((2 : ℤ)^i.val : ℤ) : ℚ) * (χ (i.val • Raw.step j s)).toMul) = _
  simp only [map_nsmul, toMul_nsmul, Int.cast_pow, Int.cast_ofNat, hs]
  exact Fin.sum_univ_eq_sum_range (fun i => (2:ℚ)^i * (((x j:ℚ)^s)⁻¹)^i) J

private theorem geometric_cleared {d : ℕ} (j : Fin d) (s J : ℕ) (x : Fin d → ℕ)
    (hx : ∀ i, 0 < x i) :
    ((clearedNum (.geometric j s J) x : ℤ) : ℚ) =
       (∏ i, (x i : ℚ))^(J*s) * rawValue (Raw.geometric j s J) (fun i => (x i : ℚ)) := by
  rw [clearedNum, geomSum, eval_geo_power j s J x hx, geo_product_split x j (J*s), mul_assoc]
  push_cast
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiJ : i ≤ J := (Finset.mem_range.mp hi).le
  have hp : (x j : ℚ) ≠ 0 := by exact_mod_cast (hx j).ne'
  have hsplit : (x j : ℚ)^(J*s) = ((x j : ℚ)^s)^(J-i) * ((x j : ℚ)^s)^i := by
    rw [← pow_add, Nat.sub_add_cancel hiJ, ← pow_mul, Nat.mul_comm]
  rw [hsplit, inv_pow]
  field_simp

private theorem threshold_scale (c r D : ℚ) (n i : ℕ) (hi : i ≤ n) :
    (c*D+c*r)^i * (c*D-c*r)^(n-i) * (n.choose i : ℚ) =
      c^n * ((n.choose i : ℚ) * (D+r)^i * (D-r)^(n-i)) := by
  rw [← mul_add, ← mul_sub, mul_pow, mul_pow]
  have hp : c^i * c^(n-i) = c^n := by rw [← pow_add, Nat.add_sub_of_le hi]
  linear_combination (n.choose i : ℚ) * (D+r)^i * (D-r)^(n-i) * hp

/-- Replacing coordinate `j` by the integer radix supplies the same cleared
numerator as the one-call cyclic extraction for the positive integral point. -/
theorem clearedNum_project_step {d : ℕ} (f : Expr d) (j : Fin d) (m : ℕ+)
    (hs : f.expand.Safe (evalBounds f).height (evalBounds f).radius)
    (ih : ∀ y : Fin d → ℕ, (∀ i, 0 < y i) →
      (clearedNum f y : ℚ) = (∏ i, (y i : ℚ))^(evalBounds f).radius *
        rawValue f.expand (fun i => (y i : ℚ)))
    (x : Fin d → ℕ) (hx : ∀ i, 0 < x i) :
    (clearedNum (f.project j m) x : ℚ) =
      (∏ i, (x i : ℚ))^(evalBounds (f.project j m)).radius *
        rawValue (f.project j m).expand (fun i => (x i : ℚ)) := by
  classical
  let G := (evalBounds f).radius
  let H := (evalBounds f).height
  let b := shiftBound G m
  let one : Fin d → ℕ := fun _ => 1
  let z := RadixGrowth.radix x one H G b
  let y := Function.update x j z
  let X : ℚ := ∏ i, (x i : ℚ)
  let Y : ℚ := ∏ i, (y i : ℚ)
  let F := rawValue f.expand (fun i => (y i : ℚ))
  let C := RadixGrowth.clearFactor x one G
  let v : ℤ := (x j : ℤ)^G * (z : ℤ)^(b-G) * clearedNum f y
  have hz : 0 < z := by dsimp [z, RadixGrowth.radix]; omega
  have hy : ∀ i, 0 < y i := by
    intro i
    by_cases hi : i = j
    · simpa [y, hi] using hz
    · simpa [y, Function.update_of_ne hi] using hx i
  have hb : G ≤ b := (shift_properties G m.property).1
  have hC : (C : ℚ) = X^G := by
    simp [C, one, RadixGrowth.clearFactor, X, Finset.prod_pow]
  have hpos : (C : ℚ) ≠ 0 := by
    rw [hC]
    exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast (hx i).ne'))
  have hpoint : rationalPoint x one = (fun i => (x i : ℚ)) := by
    funext i; simp [one, rationalPoint]
  have hupdate : Function.update (rationalPoint x one) j (z : ℚ) = (fun i => (y i : ℚ)) := by
    rw [hpoint]
    funext i
    by_cases hi : i = j
    · subst i; simp [y]
    · simp [y, Function.update_of_ne hi]
  have hXY : (x j : ℚ) * Y = X * z := by
    dsimp [Y, X]
    change (x j : ℚ) * (∏ i, (Function.update x j z i : ℚ)) = _
    rw [← Nat.cast_prod, Finset.prod_update_of_mem (Finset.mem_univ j),
      Finset.sdiff_singleton_eq_erase, Nat.cast_mul, Nat.cast_prod]
    rw [← Finset.mul_prod_erase Finset.univ (fun i => (x i : ℚ)) (Finset.mem_univ j)]
    ring
  have hproduct : (x j : ℚ)^G * Y^G = X^G * (z : ℚ)^G := by
    simpa only [mul_pow] using congrArg (fun t : ℚ => t^G) hXY
  have hr : (clearedNum f y : ℚ) = Y^G * F := ih y hy
  have hshift : (z : ℚ)^G * (z : ℚ)^(b-G) = (z : ℚ)^b := by
    rw [← pow_add]; congr 1; omega
  have hv : (v : ℚ) = (C : ℚ) * (z : ℚ)^b * F := by
    dsimp only [v]
    push_cast
    rw [hr, hC]
    calc
      _ = ((x j : ℚ)^G * Y^G) * (z : ℚ)^(b-G) * F := by ring
      _ = _ := by rw [hproduct, mul_assoc (X^G) _ _, hshift]
  have hfloor : ⌊(C : ℚ)*(z : ℚ)^b*F⌋ = v := by rw [← hv, Int.floor_intCast]
  have h := scalarRecipe_raw (D := 1) (H := H) (G := G) (m := m) f.expand hs j
    x one hx (fun _ => by decide : ∀ _i : Fin d, 0 < (1 : ℕ)) (by decide) m.property
  unfold scalarRecipe at h
  change (Extraction.extractCoefficient
    (⌊(C : ℚ)*(z : ℚ)^b*((1:ℚ)*(rawValue f.expand (Function.update (rationalPoint x one) j (z:ℚ)) / 1))⌋ *
      (((z:ℤ)^((m:ℕ)*(2*b/(m:ℕ)+1))-1)/((z:ℤ)^(m:ℕ)-1))) z (2*b) : ℚ) /
      ((C:ℚ)*1) = rawValue (f.expand.project j m) (rationalPoint x one)/1 at h
  rw [hupdate, div_one, one_mul, hfloor, mul_one, hpoint, div_one] at h
  rw [div_eq_iff hpos] at h
  change (Extraction.extractCoefficient
    (v * (((z:ℤ)^((m:ℕ)*(2*b/(m:ℕ)+1))-1)/((z:ℤ)^(m:ℕ)-1))) z (2*b) : ℚ) = _
  rw [h, hC, mul_comm]
  rfl

/-- Correctness of integer evaluation. Induction on `e` for all
`x`. Cases: `Raw.evaluate_plus`, `Raw.evaluate_scale`, `Raw.evaluate_mul`,
`Raw.evaluate_pow`, `Raw.evaluate_tail` with `tailNumerator_eq`,
`geomSum_closed`, and `scalarRecipe_raw` at `p = x`, `q = 1` with the induction
hypothesis at `Function.update x j z`. -/
theorem clearedNum_spec {d : ℕ} (e : Expr d) (he : WellFormed e) (x : Fin d → ℕ)
    (hx : ∀ i, 0 < x i) :
    ((clearedNum e x : ℤ) : ℚ) =
      (∏ i, (x i : ℚ))^(evalBounds e).radius * rawValue e.expand (fun i => (x i : ℚ)) := by
  induction e generalizing x with
  | scalar p q => simp [clearedNum, evalBounds, Expr.expand, rawValue, Raw.evaluate_atom, monomialValue]
  | monomial v =>
    simpa [clearedNum, evalBounds, Expr.expand, rawValue, Raw.evaluate_atom] using monomial_cleared v x hx
  | geometric j s J => exact geometric_cleared j s J x hx
  | add f g ihf ihg =>
    obtain ⟨hf,hg⟩ := he
    simp only [clearedNum, evalBounds, Expr.expand, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      Int.cast_pow, Int.cast_prod, ihf hf x hx, ihg hg x hx, evalBounds_denominator, pow_add]
    simp [rawValue, Raw.evaluate_plus, Raw.evaluate_scale]
    ring
  | neg f ih =>
    simp only [clearedNum, evalBounds, Expr.expand, Int.cast_neg, ih he x hx]
    simp [rawValue, Raw.evaluate_scale]
  | mul f g ihf ihg =>
    obtain ⟨hf,hg⟩ := he
    simp only [clearedNum, evalBounds, Expr.expand, Int.cast_mul, ihf hf x hx, ihg hg x hx,
      rawValue_mul_at _ _ _ hx, pow_add]
    ring
  | pow f n ih =>
    simp only [clearedNum, evalBounds, Expr.expand, Int.cast_pow, ih he x hx, rawValue_pow_at _ _ _ hx,
      mul_pow, ← pow_mul, Nat.mul_comm n]
  | threshold f n k ih =>
    obtain ⟨hr, hf⟩ := he
    rw [clearedNum, TailRadix.tailNumerator_eq _ _ _ _ hr]
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_sub, Int.cast_natCast,
      Int.cast_prod, ih hf x hx, evalBounds_denominator, evalBounds, Expr.expand, rawValue_tail_at _ _ _ _ _ hx]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.mul_comm n, pow_mul]
    exact threshold_scale _ _ _ _ _ (by have := (Finset.mem_Ico.mp hi).2; omega)
  | project f j m ih => exact clearedNum_project_step f j m (evalBounds_safe f) (ih he) x hx

theorem exprValue_eq_clearedNum {d : ℕ} (e : Expr d) (he : WellFormed e) (x : Fin d → ℕ)
    (hx : ∀ i, 0 < x i) :
    exprValue e (fun i => (x i : ℚ)) =
      ((clearedNum e x : ℤ) : ℚ) /
        ((∏ i, (x i : ℚ))^(evalBounds e).radius * (e.bounds.denominator : ℚ)) := by
  rw [exprValue, clearedNum_spec e he x hx]
  have hp : (∏ i, (x i : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast (hx i).ne')
  have hD : (e.bounds.denominator : ℚ) ≠ 0 := by exact_mod_cast e.denominator_pos.ne'
  field_simp

/-- At the point `(1, …, 1)` no clearing factor is left. -/
theorem scalarAtOne_eq_clearedNum {d : ℕ} (e : Expr d) (he : WellFormed e) :
    scalarAtOne e = ((clearedNum e (fun _ => 1) : ℤ) : ℚ) / (e.bounds.denominator : ℚ) := by
  have h := exprValue_eq_clearedNum e he (fun _ => 1) (fun _ => Nat.zero_lt_one)
  simpa [exprValue, rawValue, Raw.evaluate, monomialValue, scalarAtOne, Expr.evaluate, coordinateCharacter] using h

/-- The same tree with every scalar leaf replaced by an equal fraction. All
projections have the period of the grid, so that `gridChar_project` applies. -/
inductive ScalarEquiv (U : ℕ) {d : ℕ} : Expr d → Expr d → Prop
  | scalar {p p' : ℤ} {q q' : ℕ+} (h : (p : ℚ) / ((q : ℕ) : ℚ) = (p' : ℚ) / ((q' : ℕ) : ℚ)) :
      ScalarEquiv U (.scalar p q) (.scalar p' q')
  | monomial (v : Fin d → ℤ) : ScalarEquiv U (.monomial v) (.monomial v)
  | geometric (j : Fin d) (s J : ℕ) :
      ScalarEquiv U (.geometric j s J) (.geometric j s J)
  | add {f f' g g' : Expr d} :
      ScalarEquiv U f f' → ScalarEquiv U g g' → ScalarEquiv U (.add f g) (.add f' g')
  | neg {f f' : Expr d} : ScalarEquiv U f f' → ScalarEquiv U (.neg f) (.neg f')
  | mul {f f' g g' : Expr d} :
      ScalarEquiv U f f' → ScalarEquiv U g g' → ScalarEquiv U (.mul f g) (.mul f' g')
  | pow {f f' : Expr d} (n : ℕ) : ScalarEquiv U f f' → ScalarEquiv U (.pow f n) (.pow f' n)
  | threshold {f f' : Expr d} (n k : ℕ) :
      ScalarEquiv U f f' → ScalarEquiv U (.threshold f n k) (.threshold f' n k)
  | project {f f' : Expr d} (j : Fin d) :
      ScalarEquiv U f f' → ScalarEquiv U (.project f j (period U)) (.project f' j (period U))

/-- Induction with `Expr.evaluate_add`, `Expr.evaluate_mul`, `Expr.evaluate_pow`,
`Expr.evaluate_threshold` and `gridChar_project`. -/
theorem ScalarEquiv.evaluate_eq {U d : ℕ} {e e' : Expr d} (h : ScalarEquiv U e e')
    (z : Fin d → Point U) : e.evaluate (gridChar z) = e'.evaluate (gridChar z) := by
  induction h generalizing z with
  | scalar h =>
    simp only [Expr.evaluate, Expr.expand, Expr.bounds, Raw.evaluate_atom, ← Pi.zero_def,
      map_zero]
    change _ * (1 : ℂ) / _ = _ * 1 / _
    simp only [mul_one]
    exact_mod_cast h
  | monomial | geometric => rfl
  | add _ _ ihf ihg => simp only [Expr.evaluate_add, ihf, ihg]
  | neg h ih =>
    have neg_eval (f : Expr d) : f.neg.evaluate (gridChar z) = -f.evaluate (gridChar z) := by
      simp [Expr.evaluate, Expr.expand, Expr.bounds, Raw.evaluate_scale, neg_div]
    rw [neg_eval, neg_eval, ih]
  | mul _ _ ihf ihg => simp only [Expr.evaluate_mul, ihf, ihg]
  | pow n h ih => simp only [Expr.evaluate_pow, ih]
  | threshold n k h ih => simp only [Expr.evaluate_threshold, ih]
  | project j h ih => simp only [gridChar_project, ih]

/-- Follows from `ScalarEquiv.evaluate_eq` and `eval_at_roots_one`. -/
theorem ScalarEquiv.scalarAtOne_eq {U d : ℕ} {e e' : Expr d} (h : ScalarEquiv U e e') :
    scalarAtOne e = scalarAtOne e' := by
  apply (Rat.cast_injective (α := ℂ))
  simpa only [eval_at_roots_one] using h.evaluate_eq (fun _ => rootOne U)

end
end DiophantineNP.Blueprint
