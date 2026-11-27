import DiophantineNP.HeightGenerator
import DiophantineNP.CurveRootBound
import Mathlib.Tactic.Abel

/-! # The parallelogram law for the height on 37a1 -/

namespace DiophantineNP.Curve37

open WeierstrassCurve Filter

private theorem height_neg_eq (Q : E.Point) : height (-Q) = height Q := by
  cases Q with
  | zero => rfl
  | some h => rfl

theorem canonicalHeight_neg (Q : E.Point) : canonicalHeight (-Q) = canonicalHeight Q := by
  apply tendsto_nhds_unique (canonical_limit (-Q))
  have he (n : ℕ) : logHeight ((2^n:ℕ) • (-Q)) = logHeight ((2^n:ℕ) • Q) := by
    rw [neg_nsmul]; exact congrArg (fun u : ℕ => Real.logb 2 u) (height_neg_eq _)
  simp_rw [he]
  exact canonical_limit Q

theorem canonicalHeight_zero : canonicalHeight (0 : E.Point) = 0 := by
  have h := canonical_double (0 : E.Point)
  simp only [add_zero] at h
  linarith

/-- A one-sided bound for naive heights suffices. Taking doubling limits
removes the additive error, and applying the upper inequality to the sum
and difference gives the reverse inequality. -/
theorem canonicalHeight_parallelogram_of_upper {C : ℝ}
    (h : ∀ A B : E.Point, logHeight (A+B) + logHeight (A-B) ≤
      2*logHeight A + 2*logHeight B + C) (Q R : E.Point) :
    canonicalHeight (Q+R) + canonicalHeight (Q-R) =
      2*canonicalHeight Q + 2*canonicalHeight R := by
  have upper (A B : E.Point) : canonicalHeight (A+B)+canonicalHeight (A-B) ≤
      2*canonicalHeight A+2*canonicalHeight B := by
    have hzero : Tendsto (fun n : ℕ => C/(4:ℝ)^n) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.div_atTop
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<4))
    have hs := ((canonical_limit A).const_mul 2).add ((canonical_limit B).const_mul 2)
    have hh := hs.add hzero
    rw [add_zero] at hh
    apply le_of_tendsto_of_tendsto' ((canonical_limit (A+B)).add (canonical_limit (A-B))) hh
    intro n
    have hn := div_le_div_of_nonneg_right (h ((2^n:ℕ) • A) ((2^n:ℕ) • B))
      (show 0 ≤ (4:ℝ)^n by positivity)
    simpa only [nsmul_add,nsmul_sub,add_div,mul_div_assoc] using hn
  apply le_antisymm (upper Q R)
  have rev := upper (Q+R) (Q-R)
  rw [show Q+R+(Q-R) = Q+Q by abel, show Q+R-(Q-R) = R+R by abel,
      canonical_double,canonical_double] at rev
  linarith

/-- The parallelogram yields the square law for all integer multiples.
The recurrence only requires the second argument to be the base point. -/
theorem canonicalHeight_zsmul_of_parallelogram (Q : E.Point)
    (h : ∀ n : ℕ, canonicalHeight (n • Q+Q) + canonicalHeight (n • Q-Q) =
      2*canonicalHeight (n • Q) + 2*canonicalHeight Q) (j : ℤ) :
    canonicalHeight (j • Q) = canonicalHeight Q * (j:ℝ)^2 := by
  have hn (n : ℕ) : canonicalHeight (n • Q) = canonicalHeight Q * (n:ℝ)^2 := by
    induction n using Nat.twoStepInduction with
    | zero => simp [canonicalHeight_zero]
    | one => simp
    | more n h0 h1 =>
      have he := h (n+1)
      rw [show (n+1) • Q + Q = (n+2) • Q by exact (succ_nsmul Q (n+1)).symm,
        show (n+1) • Q - Q = n • Q by rw [succ_nsmul,add_sub_cancel_right],h0,h1] at he
      push_cast at *
      linarith only [he]
  cases j with
  | ofNat n => simpa using hn n
  | negSucc n =>
    rw [negSucc_zsmul, canonicalHeight_neg, hn]
    push_cast
    ring

private theorem affine_equation {x y : ℚ} (h : E.Nonsingular x y) : y^2+y=x^3-x := by
  have he := (Affine.equation_iff x y).mp ((Affine.nonsingular_iff x y).mp h).1
  dsimp [E] at he
  linarith only [he]

/-- The two x coordinates in the parallelogram have rational sum and product
given by biquadratic forms in the original x coordinates. -/
theorem secant_biquadratics {x y z w : ℚ} (h : E.Nonsingular x y) (k : E.Nonsingular z w)
    (hx : x ≠ z) : ∃ r t : ℚ,
    xCoord (.some h + (.some k : E.Point)) = some r ∧
    xCoord (.some h - (.some k : E.Point)) = some t ∧
    (x-z)^2*(r+t) = 2*(x+z)*(x*z-1)+1 ∧
    (x-z)^2*(r*t) = (x*z+1)^2-x-z := by
  let r := ((y-w)/(x-z))^2-x-z
  let t := ((y+w+1)/(x-z))^2-x-z
  have hd := sub_ne_zero.mpr hx
  have hy := affine_equation h
  have hw := affine_equation k
  refine ⟨r,t,?_,?_,?_,?_⟩
  · rw [Affine.Point.add_of_X_ne hx]
    change some (E.addX x z (E.slope x z y w)) = some _
    rw [Affine.slope_of_X_ne hx]
    simp [Affine.addX,E,r]
  · rw [sub_eq_add_neg,Affine.Point.neg_some,Affine.Point.add_of_X_ne hx]
    change some (E.addX x z (E.slope x z y (E.negY z w))) = some _
    rw [Affine.slope_of_X_ne hx]
    congr 1
    simp [Affine.addX,Affine.negY,E,t,sub_eq_add_neg,add_assoc,add_comm,add_left_comm]
  · dsimp [r,t]
    field_simp [hd]
    linear_combination 2 * hy + 2 * hw
  · dsimp [r,t]
    field_simp [hd]
    linear_combination
      (-2*w^2-2*w-x^3+2*x^2*z+2*x*z^2-x+y^2+y-2*z^3) * hy +
      (w^2+w-4*x^3+2*x^2*z+2*x*z^2+2*x-z^3-z) * hw

private def coordHeight (x : ℚ) := max x.num.natAbs x.den

/-- Clear both input denominators. All coefficients of the symmetric pair are
bounded by nine times the square of the product of the two input heights. -/
private theorem biquadratic_integral_bound {x z r t : ℚ} (hx : x ≠ z)
    (hs : (x-z)^2*(r+t) = 2*(x+z)*(x*z-1)+1)
    (hp : (x-z)^2*(r*t) = (x*z+1)^2-x-z) :
    ∃ A B C : ℤ, A ≠ 0 ∧ (A:ℚ)*(r+t) = B ∧ (A:ℚ)*(r*t) = C ∧
      max A.natAbs (max B.natAbs C.natAbs) ≤ 9*(coordHeight x * coordHeight z)^2 := by
  let u := x.num
  let v : ℤ := x.den
  let j := z.num
  let k : ℤ := z.den
  let a := u*k
  let b := v*j
  let c := u*j
  let d := v*k
  let A := (a-b)^2
  let B := 2*(a+b)*(c-d)+d^2
  let C := (c+d)^2-(a+b)*d
  have hv : (v:ℚ) ≠ 0 := by dsimp [v]; exact_mod_cast x.den_ne_zero
  have hk : (k:ℚ) ≠ 0 := by dsimp [k]; exact_mod_cast z.den_ne_zero
  have hu : (u:ℚ) = x*v := (div_eq_iff hv).1 x.num_div_den
  have hj : (j:ℚ) = z*k := (div_eq_iff hk).1 z.num_div_den
  have ha : (A:ℚ) = (v:ℚ)^2*k^2*(x-z)^2 := by
    dsimp only [A,a,b]; push_cast; rw [hu,hj]; ring
  have hb : (B:ℚ) = (v:ℚ)^2*k^2*(2*(x+z)*(x*z-1)+1) := by
    dsimp only [B,a,b,c,d]; push_cast; rw [hu,hj]; ring
  have hc : (C:ℚ) = (v:ℚ)^2*k^2*((x*z+1)^2-x-z) := by
    dsimp only [C,a,b,c,d]; push_cast; rw [hu,hj]; ring
  refine ⟨A,B,C,?_,?_,?_,?_⟩
  · have hn : (A:ℚ) ≠ 0 := by
      rw [ha]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hv) (pow_ne_zero _ hk)) (pow_ne_zero _ (sub_ne_zero.mpr hx))
    exact_mod_cast hn
  · rw [ha,hb,mul_assoc _ ((x-z)^2),hs]
  · rw [ha,hc,mul_assoc _ ((x-z)^2),hp]
  let M := coordHeight x * coordHeight z
  have hv' : v.natAbs ≤ coordHeight x := le_max_right ..
  have hu' : u.natAbs ≤ coordHeight x := le_max_left ..
  have hk' : k.natAbs ≤ coordHeight z := le_max_right ..
  have hj' : j.natAbs ≤ coordHeight z := le_max_left ..
  have ha' : a.natAbs ≤ M := by simpa only [a,Int.natAbs_mul] using Nat.mul_le_mul hu' hk'
  have hb' : b.natAbs ≤ M := by simpa only [b,Int.natAbs_mul] using Nat.mul_le_mul hv' hj'
  have hc' : c.natAbs ≤ M := by simpa only [c,Int.natAbs_mul] using Nat.mul_le_mul hu' hj'
  have hd' : d.natAbs ≤ M := by simpa only [d,Int.natAbs_mul] using Nat.mul_le_mul hv' hk'
  have plus (s t : ℤ) (h1 : s.natAbs ≤ M) (h2 : t.natAbs ≤ M) :
      (s+t).natAbs ≤ 2*M := (Int.natAbs_add_le ..).trans (by omega)
  have minus (s t : ℤ) (h1 : s.natAbs ≤ M) (h2 : t.natAbs ≤ M) :
      (s-t).natAbs ≤ 2*M := (Int.natAbs_sub_le ..).trans (by omega)
  refine max_le ?_ (max_le ?_ ?_)
  · change ((a-b)^2).natAbs ≤ 9*M^2
    rw [Int.natAbs_pow]
    exact (Nat.pow_le_pow_left (minus a b ha' hb') 2).trans (by nlinarith)
  · apply (Int.natAbs_add_le ..).trans
    simp only [Int.natAbs_mul,Int.natAbs_pow]
    have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left 2 (plus a b ha' hb')) (minus c d hc' hd')
    have hd2 := Nat.pow_le_pow_left hd' 2
    change (2*(a+b).natAbs*(c-d).natAbs+d.natAbs^2) ≤ 9*M^2
    nlinarith only [hprod,hd2]
  · apply (Int.natAbs_sub_le ..).trans
    simp only [Int.natAbs_mul,Int.natAbs_pow]
    have hprod := Nat.mul_le_mul (plus a b ha' hb') hd'
    have hsquare := Nat.pow_le_pow_left (plus c d hc' hd') 2
    change (c+d).natAbs^2+(a+b).natAbs*d.natAbs ≤ 9*M^2
    nlinarith only [hprod,hsquare]

private theorem height_zero_eq : height (0:E.Point) = 1 := rfl

theorem height_parallelogram_upper (Q R : E.Point) :
    height (Q+R) * height (Q-R) ≤ 18*(height Q*height R)^2 := by
  have diag (A : E.Point) : height (A+A) ≤ 18*(height A*height A)^2 := by
    have h : height (A+A) ≤ 9*(height A)^4 := by exact_mod_cast (doubling_height A).2
    nlinarith only [h]
  cases Q with
  | zero =>
    change height (0+R)*height (0-R) ≤ 18*(height 0*height R)^2
    simp only [zero_add,zero_sub,height_neg_eq,height_zero_eq,one_mul]
    nlinarith
  | @some x y h =>
    cases R with
    | zero =>
      change height (_+0)*height (_-0) ≤ 18*(_*height 0)^2
      simp only [add_zero,sub_zero,height_zero_eq,mul_one]
      nlinarith
    | @some z w k =>
      by_cases hx : x = z
      · subst z
        rcases Affine.Y_eq_of_X_eq h.1 k.1 rfl with hy|hy
        · subst w
          rw [sub_self,height_zero_eq,mul_one]
          exact diag _
        · have hn : (Affine.Point.some h : E.Point) = -Affine.Point.some k := by
            rw [Affine.Point.neg_some,Affine.Point.some.injEq]
            exact ⟨rfl,hy⟩
          rw [hn,neg_add_cancel,height_zero_eq,one_mul,show
            -Affine.Point.some k - Affine.Point.some k = -(Affine.Point.some k + Affine.Point.some k) by abel,
            height_neg_eq,height_neg_eq]
          exact diag _
      · obtain ⟨r,t,hr,ht,hs,hp⟩ := secant_biquadratics h k hx
        obtain ⟨A,B,C,hA,hB,hC,hsize⟩ := biquadratic_integral_bound hx hs hp
        have hh := (root_height_product hA hB hC).trans (Nat.mul_le_mul_left 2 hsize)
        simp only [height,hr,ht]
        change _ ≤ 18*(coordHeight x*coordHeight z)^2
        omega

theorem logHeight_parallelogram_upper (Q R : E.Point) :
    logHeight (Q+R)+logHeight (Q-R) ≤ 2*logHeight Q + 2*logHeight R + Real.logb 2 18 := by
  have pos (A : E.Point) : 0 < (height A:ℝ) := by exact_mod_cast height_pos A
  have h : (height (Q+R):ℝ)*height (Q-R) ≤ 18*((height Q:ℝ)*height R)^2 :=
    by exact_mod_cast height_parallelogram_upper Q R
  have ht := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
    (mul_pos (pos (Q+R)) (pos (Q-R))) h
  rw [Real.logb_mul (pos _).ne' (pos _).ne',
      Real.logb_mul (by norm_num : (18:ℝ) ≠ 0) (pow_ne_zero 2 (mul_ne_zero (pos Q).ne' (pos R).ne')),Real.logb_pow,
      Real.logb_mul (pos _).ne' (pos _).ne'] at ht
  dsimp only [logHeight]
  norm_num only [Nat.cast_ofNat] at ht
  linarith

theorem canonicalHeight_parallelogram (Q R : E.Point) :
    canonicalHeight (Q+R)+canonicalHeight (Q-R) = 2*canonicalHeight Q+2*canonicalHeight R :=
  canonicalHeight_parallelogram_of_upper logHeight_parallelogram_upper Q R

/-- The canonical height defined from this curve's doubling orbit is quadratic
on the integer multiples of every rational point. -/
theorem canonicalHeight_zsmul (Q : E.Point) (j : ℤ) :
    canonicalHeight (j • Q) = canonicalHeight Q * (j : ℝ)^2 :=
  canonicalHeight_zsmul_of_parallelogram Q (fun n => canonicalHeight_parallelogram (n • Q) Q) j

end DiophantineNP.Curve37
