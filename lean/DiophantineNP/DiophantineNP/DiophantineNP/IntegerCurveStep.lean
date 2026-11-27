import DiophantineNP.CurveCoordinateSize
import DiophantineNP.PowerTests

/-! # Six integer coordinates for the elliptic height transition

The witness stores the coordinates of Q and only the x-coordinate of Q+P.
An honest large-height window never needs the exceptional x = 0 branch.
-/

namespace DiophantineNP.PowerTests

open Curve37 WeierstrassCurve

structure Step where
  xNum : ℤ
  xDen : ℤ
  yNum : ℤ
  yDen : ℤ
  nextNum : ℤ
  nextDen : ℤ

def Step.start (w : Step) : ℕ := max w.xNum.natAbs w.xDen.natAbs
def Step.finish (w : Step) : ℕ := max w.nextNum.natAbs w.nextDen.natAbs

/-- Two denominator-cleared equalities, signs, and primitive x-coordinate
conditions. Each coprimality condition is an existential Bézout equation. -/
def Step.Valid (w : Step) : Prop :=
  let u := w.xNum; let v := w.xDen; let r := w.yNum; let s := w.yDen
  let a := w.nextNum; let b := w.nextDen
  0 < v ∧ 0 < s ∧ 0 < b ∧ u ≠ 0 ∧ IsCoprime u v ∧ IsCoprime a b ∧
    (r^2+r*s)*v^3 = (u^3-u*v^2)*s^2 ∧
    a*(s^2*u^2*v) = b*(r^2*v^3-s^2*u^3)

def Step.Window (w : Step) (V : ℕ) : Prop :=
  w.Valid ∧ V*w.start ≤ w.finish ∧ w.finish ≤ V^2*w.start

private theorem add_generator_x {x y : ℚ} (hp : E.Nonsingular x y) (hx : x ≠ 0) :
    xCoord (Affine.Point.some hp + P) = some ((y/x)^2-x) := by
  unfold P
  rw [Affine.Point.add_of_X_ne hx]
  change some (E.addX x 0 (E.slope x 0 y 0)) = _
  simp [Affine.slope,hx,E]

private theorem fraction_equations {u v r s a b : ℚ}
    (hv : v ≠ 0) (hs : s ≠ 0) (hu : u ≠ 0) (hb : b ≠ 0) :
    (((r/s)^2+r/s=(u/v)^3-u/v) ∧ a/b=((r/s)/(u/v))^2-u/v) ↔
      (r^2+r*s)*v^3=(u^3-u*v^2)*s^2 ∧
      a*(s^2*u^2*v)=b*(r^2*v^3-s^2*u^3) := by
  apply and_congr
  · field_simp [hs,hv]
  · field_simp [hs,hv,hu,hb]

private theorem rep_height {a b : ℤ} (hb : 0 < b) (hab : IsCoprime a b) :
    rationalHeight ((a : ℚ)/b) = max a.natAbs b.natAbs := by
  let h := Int.isCoprime_iff_nat_coprime.mp hab
  obtain hn := Rat.num_div_eq_of_coprime hb h
  obtain hd := Rat.den_div_eq_of_coprime hb h
  unfold rationalHeight
  have he : ((a : ℚ) / b).den = b.natAbs := by simpa only [Int.natAbs_natCast] using congrArg Int.natAbs hd
  rw [hn,he]

/-- Soundness of the fixed integer graph of one transition. -/
theorem Step.decode {w : Step} (h : w.Valid) :
    ∃ Q : E.Point, w.start = height Q ∧ w.finish = height (Q+P) := by
  rcases h with ⟨hv,hs,hb,hu,hx,hz,he,he'⟩
  let x : ℚ := w.xNum/w.xDen
  let y : ℚ := w.yNum/w.yDen
  let z : ℚ := w.nextNum/w.nextDen
  have hv' : (w.xDen : ℚ) ≠ 0 := by exact_mod_cast hv.ne'
  have hs' : (w.yDen : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  have hu' : (w.xNum : ℚ) ≠ 0 := by exact_mod_cast hu
  have hb' : (w.nextDen : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have ⟨hc,ha⟩ := (fraction_equations (r := w.yNum) (a := w.nextNum) hv' hs' hu' hb').mpr
    ⟨by exact_mod_cast he,by exact_mod_cast he'⟩
  have hns : E.Nonsingular x y := by
    apply (Affine.equation_iff_nonsingular_of_Δ_ne_zero (W := E) (by rw [discriminant]; norm_num)).mp
    apply (Affine.equation_iff x y).mpr
    dsimp only [E]
    change y^2 + 0*x*y + 1*y = x^3 + 0*x^2 + (-1)*x+0
    change y^2+y=x^3-x at hc
    linarith only [hc]
  refine ⟨.some hns, (rep_height hv hx).symm, ?_⟩
  have hz' : xCoord (Affine.Point.some hns+P) = some z := by
    rw [add_generator_x hns (div_ne_zero hu' hv')]
    exact congrArg some ha.symm
  rw [height,hz']
  exact (rep_height hb hz).symm

/-- Completeness uses a nonzero native x-coordinate. All six honest register
magnitudes are bounded in terms of the two x-heights. -/
theorem Step.encode (Q : E.Point) (hQ : 1 < height Q) :
    ∃ w : Step, w.Valid ∧ w.start = height Q ∧ w.finish = height (Q+P) ∧
      (max w.yNum.natAbs w.yDen.natAbs)^2 ≤ 20*(height Q)^3 := by
  cases Q with
  | zero => change 1 < 1 at hQ; omega
  | @some x y h =>
    have hx : x ≠ 0 := by
      intro hzero
      change 1 < rationalHeight x at hQ
      rw [hzero] at hQ
      norm_num [rationalHeight] at hQ
    let z := (y/x)^2-x
    let w : Step := ⟨x.num,x.den,y.num,y.den,z.num,z.den⟩
    have hc : y^2+y=x^3-x := by
      have he := (Affine.equation_iff x y).mp ((Affine.nonsingular_iff x y).mp h).1
      dsimp [E] at he
      linarith only [he]
    have hv : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
    have hs : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_ne_zero
    have hb : (z.den : ℚ) ≠ 0 := by exact_mod_cast z.den_ne_zero
    have hnum : x.num ≠ 0 := by intro hn; exact hx (Rat.zero_of_num_zero hn)
    have hu : (x.num : ℚ) ≠ 0 := by exact_mod_cast hnum
    have he := (fraction_equations hv hs hu hb).mp
      (show (((y.num:ℚ)/y.den)^2+y.num/y.den=((x.num:ℚ)/x.den)^3-x.num/x.den) ∧
        (z.num:ℚ)/z.den=(((y.num:ℚ)/y.den)/((x.num:ℚ)/x.den))^2-(x.num:ℚ)/x.den by
        simp only [Rat.num_div_den]; exact ⟨hc,rfl⟩)
    refine ⟨w, ?_, rfl, ?_, ?_⟩
    · dsimp only [Step.Valid,w]
      refine ⟨by exact_mod_cast x.den_pos,by exact_mod_cast y.den_pos,by exact_mod_cast z.den_pos,
        hnum,Int.isCoprime_iff_nat_coprime.mpr x.reduced,
        Int.isCoprime_iff_nat_coprime.mpr z.reduced,?_,?_⟩
      · dsimp only [w]; exact_mod_cast he.1
      · dsimp only [w]; exact_mod_cast he.2
    · rw [height,add_generator_x h hx]
      rfl
    · exact y_coordinate_size h

end DiophantineNP.PowerTests
