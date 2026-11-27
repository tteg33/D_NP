import DiophantineNP.CurveQuadraticGap
import DiophantineNP.PowerTests

/-! # Small points and descent on the curve of conductor 37 -/

namespace DiophantineNP.Curve37

open WeierstrassCurve

private def pointOfCoords (x y : ℚ) (h : E.Nonsingular x y) : E.Point := .some h

local macro "solve_point" : tactic =>
  `(tactic| norm_num [Affine.nonsingular_iff, Affine.equation_iff, E])

private def M2 := pointOfCoords 1 0 (by solve_point)
private def M3 := pointOfCoords (-1) (-1) (by solve_point)
private def M4 := pointOfCoords 2 (-3) (by solve_point)
private def M5 := pointOfCoords (1/4) (-5/8) (by solve_point)
private def M6 := pointOfCoords 6 14 (by solve_point)
private def M7 := pointOfCoords (-5/9) (8/27) (by solve_point)

private theorem multiple2 : (2:ℤ) • P = M2 := by
  change P+P = M2
  unfold P M2 pointOfCoords
  rw [Affine.Point.add_self_of_Y_ne (by norm_num [E,Affine.negY]),Affine.Point.some.injEq]
  norm_num [E,Affine.addX,Affine.addY,Affine.negAddY,Affine.negY,Affine.slope]

private theorem multiple3 : (3:ℤ) • P = M3 := by
  rw [show (3:ℤ)=2+1 by decide,add_zsmul,one_zsmul,multiple2]
  unfold M2 M3 P pointOfCoords
  rw [Affine.Point.add_of_X_ne (by norm_num),Affine.Point.some.injEq]
  norm_num [E,Affine.addX,Affine.addY,Affine.negAddY,Affine.negY,Affine.slope]

private theorem multiple4 : (4:ℤ) • P = M4 := by
  rw [show (4:ℤ)=3+1 by decide,add_zsmul,one_zsmul,multiple3]
  unfold M3 M4 P pointOfCoords
  rw [Affine.Point.add_of_X_ne (by norm_num),Affine.Point.some.injEq]
  norm_num [E,Affine.addX,Affine.addY,Affine.negAddY,Affine.negY,Affine.slope]

private theorem multiple5 : (5:ℤ) • P = M5 := by
  rw [show (5:ℤ)=4+1 by decide,add_zsmul,one_zsmul,multiple4]
  unfold M4 M5 P pointOfCoords
  rw [Affine.Point.add_of_X_ne (by norm_num),Affine.Point.some.injEq]
  norm_num [E,Affine.addX,Affine.addY,Affine.negAddY,Affine.negY,Affine.slope]

private theorem multiple6 : (6:ℤ) • P = M6 := by
  rw [show (6:ℤ)=5+1 by decide,add_zsmul,one_zsmul,multiple5]
  unfold M5 M6 P pointOfCoords
  rw [Affine.Point.add_of_X_ne (by norm_num),Affine.Point.some.injEq]
  norm_num [E,Affine.addX,Affine.addY,Affine.negAddY,Affine.negY,Affine.slope]

private theorem multiple7 : (7:ℤ) • P = M7 := by
  rw [show (7:ℤ)=6+1 by decide,add_zsmul,one_zsmul,multiple6]
  unfold M6 M7 P pointOfCoords
  rw [Affine.Point.add_of_X_ne (by norm_num),Affine.Point.some.injEq]
  norm_num [E,Affine.addX,Affine.addY,Affine.negAddY,Affine.negY,Affine.slope]

private theorem equation_of_point {x y : ℚ} (h : E.Nonsingular x y) : y^2+y=x^3-x := by
  have he := (Affine.equation_iff x y).mp ((Affine.nonsingular_iff x y).mp h).1
  dsimp [E] at he
  linarith only [he]

private def listed (x : ℚ) : Prop := x=0 ∨ x=1 ∨ x= -1 ∨ x=2 ∨ x=1/4 ∨ x=6 ∨ x= -5/9

private instance (x : ℚ) : Decidable (listed x) := by unfold listed; infer_instance

/-- The search supplies a candidate square-root floor. Soundness uses the
checked neighboring squares, independently of how the candidate was found. -/
private def sqrtCandidate (n : ℕ) : ℕ :=
  (List.range 9).foldl (fun t i =>
    let next := t+2^(8-i)
    if next^2 ≤ n then next else t) 0

private def gap (n : ℕ) : Prop := (sqrtCandidate n)^2 < n ∧ n < (sqrtCandidate n+1)^2
private instance (n : ℕ) : Decidable (gap n) := by unfold gap; infer_instance

private theorem not_gap_square (m : ℕ) : ¬gap (m^2) := by
  rintro ⟨h₁,h₂⟩
  by_cases hm : m ≤ sqrtCandidate (m^2)
  · exact (not_lt_of_ge (Nat.pow_le_pow_left hm 2)) h₁
  · exact (not_lt_of_ge (Nat.pow_le_pow_left (by omega : sqrtCandidate (m^2)+1 ≤ m) 2)) h₂

private def screened (q : ℚ) : Prop := q < 0 ∨ gap q.num.natAbs ∨ gap q.den
private instance (q : ℚ) : Decidable (screened q) := by unfold screened; infer_instance

private theorem square_passes (r : ℚ) : ¬screened (r^2) := by
  simp [screened,Rat.num_pow,Rat.den_pow,Int.natAbs_pow,not_gap_square,sq_nonneg]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem low_sieve (a : Fin 33) (b : Fin 16) :
    let x : ℚ := ((a.val : ℤ)-16 : ℤ) / ((b.val+1:ℕ):ℚ)
    ¬screened (4*x^3-4*x+1) → listed x := by
  revert a b
  decide +kernel

private theorem low_x_list {x y : ℚ} (h : E.Nonsingular x y) (hh : max x.num.natAbs x.den ≤ 16) :
    listed x := by
  have he := equation_of_point h
  have hd : 4*x^3-4*x+1 = (2*y+1)^2 := by linarith only [he]
  have hs : ¬screened (4*x^3-4*x+1) := hd ▸ square_passes _
  have ha : x.num.natAbs ≤ 16 := (le_max_left ..).trans hh
  have hb : x.den ≤ 16 := (le_max_right ..).trans hh
  let a : Fin 33 := ⟨(x.num+16).toNat,by omega⟩
  let b : Fin 16 := ⟨x.den-1,by omega⟩
  have ea : (a.val:ℤ)-16 = x.num := by dsimp [a]; omega
  have eb : b.val+1 = x.den := by dsimp [b]; have := x.den_pos; omega
  have H := low_sieve a b
  simp only [ea,eb,Rat.num_div_den] at H
  exact H hs

private theorem generated_of_x_equal {Q : E.Point} {j : ℤ} (h : xCoord Q = xCoord (j • P)) :
    ∃ n : ℤ, n • P = Q := by
  generalize he : j • P = R at h
  cases Q with
  | zero => exact ⟨0,zero_zsmul ..⟩
  | @some x y hq =>
    cases R with
    | zero => simp [xCoord] at h
    | @some x' y' hr =>
      have hx : x=x' := Option.some.inj h
      subst x'
      obtain hy|hy := Affine.Y_eq_of_X_eq ((Affine.nonsingular_iff ..).mp hq).1
        ((Affine.nonsingular_iff ..).mp hr).1 rfl
      · subst y'; exact ⟨j,he⟩
      · refine ⟨-j,?_⟩
        rw [neg_zsmul,he,Affine.Point.neg_some,Affine.Point.some.injEq]
        exact ⟨rfl,hy.symm⟩

/-- Enumeration of all affine solutions of height at most sixteen. The comparison
uses the rational square condition and identifies each point up to sign. -/
theorem generated_of_height_le_sixteen (Q : E.Point) (hh : height Q ≤ 16) :
    ∃ n : ℤ, n • P = Q := by
  cases Q with
  | zero => exact ⟨0,zero_zsmul ..⟩
  | @some x y hp =>
    obtain hx|hx|hx|hx|hx|hx|hx := low_x_list hp hh
    · apply generated_of_x_equal (j:=1); simpa [one_zsmul,xCoord,P] using hx
    · apply generated_of_x_equal (j:=2); simpa [multiple2,xCoord,M2,pointOfCoords] using hx
    · apply generated_of_x_equal (j:=3); simpa [multiple3,xCoord,M3,pointOfCoords] using hx
    · apply generated_of_x_equal (j:=4); simpa [multiple4,xCoord,M4,pointOfCoords] using hx
    · apply generated_of_x_equal (j:=5); simpa [multiple5,xCoord,M5,pointOfCoords] using hx
    · apply generated_of_x_equal (j:=6); simpa [multiple6,xCoord,M6,pointOfCoords] using hx
    · apply generated_of_x_equal (j:=7); simpa [multiple7,xCoord,M7,pointOfCoords] using hx

private theorem quadratic_root_bound (a b c : ℤ) (z : ℚ) (ha : a ≠ 0) (hc : c ≠ 0)
    (hz : (a:ℚ)*z^2+b*z+c=0) :
    z.num.natAbs ≤ c.natAbs ∧ z.den ≤ a.natAbs := by
  let u := z.num
  let v : ℤ := z.den
  have huv : IsCoprime u v := Int.isCoprime_iff_nat_coprime.mpr z.reduced
  have e : a*u^2+b*u*v+c*v^2=0 := by
    rw [← z.num_div_den] at hz
    have hv : (z.den:ℚ) ≠ 0 := by exact_mod_cast z.den_ne_zero
    field_simp [hv] at hz
    dsimp only [u,v]
    apply (Rat.intCast_inj).mp
    push_cast
    linarith only [hz]
  have hvd : v ∣ a := huv.symm.pow_right.dvd_of_dvd_mul_right
    (show v ∣ a * u^2 from ⟨-(b*u+c*v),by linarith only [e]⟩)
  have hud : u ∣ c := huv.pow_right.dvd_of_dvd_mul_right
    (show u ∣ c * v^2 from ⟨-(a*u+b*v),by linarith only [e]⟩)
  exact ⟨Nat.le_of_dvd (Int.natAbs_pos.mpr hc) (Int.natAbs_dvd_natAbs.mpr hud),
    Nat.le_of_dvd (Int.natAbs_pos.mpr ha) (Int.natAbs_dvd_natAbs.mpr hvd)⟩

/-- Translation by (0,0) gives the rational root of a quadratic with outer
coefficients u² and v²−uv when x = u/v. Only the outer coefficients are
needed for its reduced height. -/
theorem translate_height_bound (Q : E.Point) (hlarge : 16 < height Q) :
    height (Q+P) ≤ 2*(height Q)^2 := by
  cases Q with
  | zero => change 16 < 1 at hlarge; omega
  | @some x y h =>
    let u := x.num
    let v : ℤ := x.den
    let z := (y/x)^2-x
    let H := max x.num.natAbs x.den
    have hx0 : x ≠ 0 := by rintro rfl; norm_num [height,xCoord] at hlarge
    have hx1 : x ≠ 1 := by rintro rfl; norm_num [height,xCoord] at hlarge
    have hv : (x.den:ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
    have hu : (u:ℚ) = x*x.den := (div_eq_iff hv).mp x.num_div_den
    have he := equation_of_point h
    have hz : z = -(x+y)/x^2 := by
      dsimp [z]
      field_simp [hx0]
      linarith only [he]
    have hz' : x^2*z^2+(2*x-1)*z+(1-x)=0 := by
      rw [hz]
      field_simp [hx0]
      linarith only [he]
    have heq : ((u^2:ℤ):ℚ)*z^2 + ((2*u*v-v^2:ℤ):ℚ)*z + ((v^2-u*v:ℤ):ℚ) = 0 := by
      dsimp only [v]
      push_cast
      rw [hu]
      linear_combination (x.den:ℚ)^2 * hz'
    have ha : u^2 ≠ 0 := pow_ne_zero _ (fun hh => hx0 (Rat.zero_of_num_zero hh))
    have hc : v^2-u*v ≠ 0 := by
      intro hh
      have hq : (x.den:ℚ)^2 - (u:ℚ)*x.den=0 := by exact_mod_cast hh
      rw [hu] at hq
      exact hx1 (by apply (mul_right_cancel₀ (pow_ne_zero 2 hv)); linarith only [hq])
    have hb := quadratic_root_bound _ _ _ z ha hc heq
    have hnum : (v^2-u*v).natAbs ≤ 2*H^2 := by
      have hvv : v.natAbs ≤ H := by simp [v,H]
      have huu : u.natAbs ≤ H := le_max_left .. 
      have hs := Nat.pow_le_pow_left hvv 2
      have hp := Nat.mul_le_mul huu hvv
      calc _ ≤ (v^2).natAbs + (u*v).natAbs := Int.natAbs_sub_le .. 
           _ ≤ _ := by rw [Int.natAbs_pow,Int.natAbs_mul]; nlinarith only [hs,hp]
    have hden : (u^2).natAbs ≤ H^2 := by
      rw [Int.natAbs_pow]; exact Nat.pow_le_pow_left (le_max_left ..) 2
    have hxadd : xCoord (Affine.Point.some h + P) = some z := by
      unfold P
      rw [Affine.Point.add_of_X_ne hx0]
      change some (E.addX x 0 (E.slope x 0 y 0)) = _
      simp [Affine.slope,hx0,E,z]
    rw [height,hxadd]
    change max z.num.natAbs z.den ≤ 2*H^2
    exact max_le (hb.1.trans hnum) (hb.2.trans (hden.trans (by omega)))

/-- The only descent input needed to prove full generation. This asserts the
two cosets of 2E(Q) can be represented by O and P, allowing coincidence. -/
def ModTwoGeneration : Prop := ∀ Q : E.Point, ∃ R : E.Point, Q=R+R ∨ Q+P=R+R

theorem cyclic_of_mod_two (hmod : ModTwoGeneration) : PowerTests.Cyclic := by
  intro Q
  induction Q using (measure height).wf.induction with
  | h Q ih =>
    by_cases hsmall : height Q ≤ 16
    · exact generated_of_height_le_sixteen Q hsmall
    have hlarge : 16 < height Q := by omega
    obtain ⟨R,hr⟩ := hmod Q
    have htrans : height (R+R) ≤ 2*(height Q)^2 := by
      rcases hr with hh|hh
      · rw [←hh]
        nlinarith only [hlarge,sq_nonneg (height Q-1:ℤ)]
      · rw [←hh]
        exact translate_height_bound Q hlarge
    have hl := (doubling_height R).1
    have hrsmall : height R < height Q := by
      by_contra! hge
      have hu : (height (R+R):ℝ) ≤ 2*(height Q:ℝ)^2 := by exact_mod_cast htrans
      have hw := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ height Q) (by exact_mod_cast hge : (height Q:ℝ) ≤ height R) 4
      have h16 : (16:ℝ) < height Q := by exact_mod_cast hlarge
      nlinarith only [hw,hu,hl, mul_pos (show 0 < (height Q:ℝ)^2 by positivity)
        (show (0:ℝ) < (height Q:ℝ)^2-148 by nlinarith [sq_nonneg ((height Q:ℝ)-16)])]
    obtain ⟨j,hj⟩ := ih R hrsmall
    rcases hr with hh|hh
    · exact ⟨j+j,by rw [add_zsmul,hj,hh]⟩
    · exact ⟨(j+j)-1,by rw [sub_zsmul,add_zsmul,one_zsmul,hj,←hh,add_assoc,add_neg_cancel,add_zero]⟩

/-- Every point whose canonical height is at most that of P is generated by P. -/
theorem generated_of_canonical_le (Q : E.Point) (hQ : canonicalHeight Q ≤ canonicalHeight P) :
    ∃ j : ℤ, j • P = Q := by
  have h₂ := (abs_le.mp (canonical_comparison (Q+Q))).2
  rw [canonical_double] at h₂
  have hh : logHeight (Q+Q) < 5 := by linarith [canonical_generator_bounds.2]
  have hpos : 0 < (height (Q+Q):ℝ) := by exact_mod_cast height_pos _
  have ht := (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hpos).mp hh
  norm_num at ht
  have hl := (doubling_height Q).1
  apply generated_of_height_le_sixteen
  by_contra! hbig
  have hb : 16 ≤ (height Q:ℝ) := by exact_mod_cast hbig.le
  have := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤16) hb 4
  norm_num at this
  have H : (height (Q+Q):ℝ) < 32 := by exact_mod_cast ht
  linarith

private theorem multiplier_injective : Function.Injective (fun j : ℤ => j • P) :=
  injective_zsmul_iff_not_isOfFinAddOrder.mpr generator_infinite_order

/-- No nonidentity rational point on this curve is torsion. -/
theorem torsion_point_eq_zero (Q : E.Point) (ht : IsOfFinAddOrder Q) : Q=0 := by
  obtain ⟨n,hn,hz⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ht
  have he : (n:ℤ) • Q=0 := by simpa using hz
  have hh := canonicalHeight_zsmul Q (n:ℤ)
  rw [he,canonicalHeight_zero] at hh
  have hc : canonicalHeight Q = 0 :=
    (mul_eq_zero.mp hh.symm).resolve_right (pow_ne_zero _ (by exact_mod_cast hn.ne'))
  obtain ⟨j,rfl⟩ := generated_of_canonical_le Q (by rw [hc]; linarith [canonical_generator_bounds.1])
  have hm : ((n:ℤ)*j) • P = (0:ℤ) • P := by simpa only [mul_zsmul,zero_zsmul] using he
  have hj := (mul_eq_zero.mp (multiplier_injective hm)).resolve_left (by exact_mod_cast hn.ne')
  simp [hj]

/-- Every rational point commensurable with P is an integral multiple of P.
Taking the integer quotient b/a shifts it into a canonical-height interval
already covered by the finite enumeration. -/
theorem generated_of_relation (Q : E.Point) {a b : ℤ} (ha : a≠0) (he : a • Q=b • P) :
    ∃ j : ℤ, j • P=Q := by
  let R := Q-(b/a) • P
  have hr : a • R=(b%a) • P := by
    dsimp only [R]
    rw [zsmul_sub,he,←mul_zsmul,sub_eq_add_neg,←sub_zsmul]
    congr 1
    have h := Int.emod_add_mul_ediv b a
    omega
  have hh := congrArg canonicalHeight hr
  simp only [canonicalHeight_zsmul] at hh
  have hrem : |b%a| ≤ |a| := by
    rw [abs_of_nonneg (Int.emod_nonneg b ha)]
    exact (Int.emod_lt_abs b ha).le
  have hr₂ : ((b%a:ℤ):ℝ)^2 ≤ (a:ℝ)^2 := by exact_mod_cast (sq_le_sq.mpr hrem)
  have hP : 0 ≤ canonicalHeight P := by linarith [canonical_generator_bounds.1]
  have hA : (0:ℝ)<(a:ℝ)^2 := sq_pos_of_ne_zero (by exact_mod_cast ha)
  have hR : canonicalHeight R ≤ canonicalHeight P := by
    apply le_of_mul_le_mul_right _ hA
    rw [hh]
    exact mul_le_mul_of_nonneg_left hr₂ hP
  obtain ⟨j,hj⟩ := generated_of_canonical_le R hR
  exact ⟨j+b/a,by rw [add_zsmul,hj]; dsimp [R]; abel⟩

/-- No integer of absolute value greater than one divides the point P in E(ℚ). -/
theorem generator_primitive {Q : E.Point} {a : ℤ} (h : a • Q=P) : IsUnit a := by
  have ha : a ≠ 0 := by
    intro hz
    rw [hz,zero_zsmul] at h
    have he₀ : (1:ℤ) • P=(0:ℤ) • P := by simpa using h.symm
    exact one_ne_zero (multiplier_injective he₀)
  obtain ⟨j,hj⟩ := generated_of_relation Q ha (b:=1) (by simpa using h)
  have he : (a*j) • P = (1:ℤ) • P := by rw [mul_zsmul,hj,one_zsmul,h]
  exact isUnit_of_dvd_one ⟨j,(multiplier_injective he).symm⟩

/-- The published upper bound on the Mordell–Weil rank suffices. The finite
enumeration and height descent prove both saturation and trivial torsion. -/
theorem cyclic_of_rank_le_one (h : Module.rank ℤ E.Point ≤ 1) : PowerTests.Cyclic := by
  classical
  intro Q
  by_contra hn
  have hi : LinearIndependent ℤ ![Q,P] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at hg
    have h0 : g 0=0 := by
      by_contra hm
      exact hn (generated_of_relation Q hm (b:= -(g 1)) (by rw [neg_zsmul]; exact eq_neg_of_add_eq_zero_left hg))
    have h1 : g 1=0 := multiplier_injective (by simpa [h0] using hg)
    fin_cases i <;> assumption
  have hbad := hi.cardinal_le_rank.trans h
  norm_num [Cardinal.mk_fin] at hbad


/-- The lower bound follows from the already verified infinite order of P. -/
theorem one_le_mordell_weil_rank : 1 ≤ Module.rank ℤ E.Point := by
  simpa only [Module.rank_self] using
    (LinearMap.toSpanSingleton ℤ E.Point P).rank_le_of_injective multiplier_injective

/-- This particular generator spans exactly when the curve has rank one. -/
theorem cyclic_iff_rank_one : PowerTests.Cyclic ↔ Module.rank ℤ E.Point = 1 := by
  constructor
  · intro h
    apply le_antisymm _ one_le_mordell_weil_rank
    simpa only [Module.rank_self] using
      (LinearMap.toSpanSingleton ℤ E.Point P).rank_le_of_surjective h
  · exact fun h => cyclic_of_rank_le_one h.le

end DiophantineNP.Curve37
