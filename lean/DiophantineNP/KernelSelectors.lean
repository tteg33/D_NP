import DiophantineNP.GridLogic

/-! # The equality and common-arc selectors in the four-coordinate readout -/
namespace DiophantineNP.KernelSelectors
open ConcreteGrid Counting Real
noncomputable section
abbrev Pnt (U : ℕ) := Counting.LabelGrid U (Invalid U) (Outside U)
abbrev Sel (U : ℕ) := (Fin U × Bool) ⊕ Invalid U
def label {U : ℕ} (w : Sel U) : ℤ := ConcreteGrid.centered (selectedEquiv U w).1
def arcSign {U : ℕ} (w : Sel U) : Bool := (selectedEquiv U w).2

variable {U : ℕ}
def y (w : Pnt U) : ℝ := (observed U).x w - radius U
def residual (z w u v : Pnt U) : ℝ :=
  (observed U).x z * y w - (J U:ℝ)*y u - y v
def L (z w u v : Pnt U) : ℝ :=
  (gate U).H ((1/4-(residual z w u v)^2)/(8*(size U:ℝ)^4))
def sine (w : Pnt U) : ℝ := sin (2*π*((roots U w).val:ℝ)/(size U:ℝ))
def S (w v : Pnt U) : ℝ := (gate U).H (sine w*sine v/4)

private theorem radius_pos : 2 ≤ radius U := by rw [radius]; exact le_max_left _ _
private theorem bounds : (2:ℝ) ≤ size U ∧ (J U:ℝ) ≤ (size U:ℝ)/2 := by
  obtain ⟨hb,_,_,hs⟩ := ConcreteGrid.numeric (U := U)
  unfold J
  push_cast
  constructor <;> linarith

private theorem y_bound (w : Pnt U) : |y w| ≤ size U := by
  have hm := (bounds (U := U)).1
  have hN : 0 < size U := by exact_mod_cast (by linarith : (0:ℝ)<size U)
  have hp := Wallis.approxPi_ratio ((size U)^4) (pow_pos hN _)
  have hpi := (lt_div_iff₀ pi_pos).mp hp.1
  unfold y
  rw [(observation_formulas w).1, sub_sub_cancel_left, abs_neg, abs_div, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (by linarith [pi_gt_three] : 0<2*Wallis.approxPi ((size U)^4))]
  apply (div_le_iff₀ (by linarith [pi_gt_three])).2
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  linarith [abs_le.mpr ⟨neg_one_le_cos (2*π*((roots U w).val:ℝ)/(size U:ℝ)), cos_le_one _⟩,pi_gt_three]

private theorem l_range (z w u v : Pnt U) :
    |(1/4-(residual z w u v)^2)/(8*(size U:ℝ)^4)| ≤ 1 := by
  let M : ℝ := size U
  have hm : 2 ≤ M := bounds.1
  have hj := (bounds (U := U)).2
  have hJ : 0 ≤ (J U:ℝ) := Nat.cast_nonneg _
  have hres : |residual z w u v| ≤ 2*M^2 := by
    calc
      _ ≤ |(observed U).x z*y w-(J U:ℝ)*y u| + |y v| := abs_sub _ _
      _ ≤ (|(observed U).x z| * |y w| + |(J U:ℝ)| * |y u|) + |y v| := by
        rw [← abs_mul,← abs_mul]; exact add_le_add_right (abs_sub _ _) _
      _ ≤ (M*M+(M/2)*M)+M := by
        rw [abs_of_nonneg hJ]
        exact add_le_add (add_le_add (mul_le_mul ((observed U).x_bound _) (y_bound _) (abs_nonneg _) (Nat.cast_nonneg _))
          (mul_le_mul hj (y_bound _) (abs_nonneg _) (by positivity))) (y_bound _)
      _ ≤ _ := by nlinarith [mul_nonneg (by linarith : 0≤M-2) (by linarith : 0≤M)]
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤2*M^2)).2 hres
  rw [sq_abs] at hs
  change |(1/4-(residual z w u v)^2)/(8*M^4)| ≤ 1
  have hpow : 1 ≤ M^4 := one_le_pow₀ (by linarith)
  rw [abs_div, abs_of_pos (by positivity : 0<8*M^4), div_le_one (by positivity), abs_le]
  constructor <;> nlinarith [sq_nonneg (residual z w u v)]

theorem L_unit (z w u v : Pnt U) : UnitValue (L z w u v) :=
  (gate U).unit _ (abs_le.mp (l_range z w u v)).1 (abs_le.mp (l_range z w u v)).2

private theorem close_y (w : Sel U) : |y (.inl w) - (label w:ℝ)| ≤ error U := by
  let p := selectedEquiv U w
  have h := rootX_close p.1 p.2
  change |(observed U).x (.inl w) - ((p.1.val:ℕ):ℝ)| ≤ error U at h
  unfold y label centered
  push_cast
  convert h using 2
  ring

private theorem more_precision :
    (5*(radius U:ℝ)+3)*error U ≤ 1/8 := by
  obtain ⟨hb,_,hlarge,hm⟩ := ConcreteGrid.numeric (U := U)
  let B : ℝ := radius U
  let M : ℝ := size U
  change 2 ≤ B at hb
  change 512*(B+1)^3 ≤ M at hlarge
  change 32*(B+1) ≤ M at hm
  have hp : 1 ≤ M := by linarith
  have hm3 : M ≤ M^3 := by simpa using pow_le_pow_right₀ hp (by decide : 1 ≤ 3)
  have hp0 : 0<M := by linarith
  have h₁ : 32*B^3/M^2 ≤ 1/(2*M) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hg : 64*B^3 ≤ M := by nlinarith [sq_nonneg B, show 0≤B^3 by positivity]
    nlinarith [mul_le_mul_of_nonneg_right hg hp0.le]
  have h₂ : B/M^4 ≤ 1/(2*M) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : 2*B ≤ M^3) hp0.le]
  have he : error U ≤ 1/M := by
    unfold error
    change 32*B^3/M^2+B/M^4 ≤ _
    have : 1/(2*M)+1/(2*M) = 1/M := by field_simp; norm_num
    linarith
  refine (mul_le_mul_of_nonneg_left he (by linarith : 0≤5*B+3)).trans ?_
  rw [← mul_div_assoc,mul_one,div_le_div_iff₀ hp0 (by norm_num)]
  nlinarith [sq_nonneg B, show 0≤B^3 by positivity]

private theorem residual_error (i : Fin U) (b : Bool) (w u v : Sel U) :
    |residual (.inl (.inl (i,b))) (.inl w) (.inl u) (.inl v) -
        (((i.val:ℤ)*label w-(J U:ℤ)*label u-label v : ℤ):ℝ)| ≤ 1/8 := by
  let x := (observed U).x (.inl (.inl (i,b)))
  let B : ℝ := radius U
  let E := error U
  have he0 : 0≤E := (error_small U).1
  have he1 : E ≤ 1 := ((error_small U).2.1).trans (by norm_num)
  have hx : |x-(i.val:ℝ)| ≤ E := (observed U).close_valid i b
  have hU : U ≤ radius U := by rw [radius]; exact le_max_right _ _
  have hi : (i.val:ℝ) ≤ B := by dsimp [B]; exact_mod_cast i.isLt.le.trans hU
  have hk : |(label w:ℝ)| ≤ B := by unfold B label; exact_mod_cast c_bound (selectedEquiv U w).1
  have hwy := close_y w
  have hwa : |y (.inl w)| ≤ B+1 := by
    have ht := abs_sub_le (y (.inl w)) (label w:ℝ) 0
    simp only [sub_zero] at ht
    change _ ≤ E at hwy
    linarith
  have hprod : |x*y (.inl w)-(i.val:ℝ)*(label w:ℝ)| ≤ (2*B+1)*E := by
    calc
      _ = |(x-(i.val:ℝ))*y (.inl w)+(i.val:ℝ)*(y (.inl w)-(label w:ℝ))| := by congr 1; ring
      _ ≤ |x-(i.val:ℝ)| * |y (.inl w)| + (i.val:ℝ) * |y (.inl w)-(label w:ℝ)| := by
        simpa only [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) i.val)] using
          abs_add_le ((x-(i.val:ℝ))*y (.inl w)) ((i.val:ℝ)*(y (.inl w)-(label w:ℝ)))
      _ ≤ E*(B+1)+B*E := add_le_add (mul_le_mul hx hwa (abs_nonneg _) he0)
          (mul_le_mul hi hwy (abs_nonneg _) (Nat.cast_nonneg _))
      _ = _ := by ring
  have hJ : (J U:ℝ) = 2*B+1 := by unfold J B; push_cast; rfl
  have hlin := mul_le_mul_of_nonneg_left (close_y u) (Nat.cast_nonneg (α := ℝ) (J U))
  push_cast
  change |x*y (.inl w)-_ - _ - _| ≤ _
  calc
    _ = |(x*y (.inl w)-(i.val:ℝ)*(label w:ℝ)) - (J U:ℝ)*(y (.inl u)-(label u:ℝ)) -
        (y (.inl v)-(label v:ℝ))| := by congr 1; ring
    _ ≤ |x*y (.inl w)-(i.val:ℝ)*(label w:ℝ)| +
        (J U:ℝ) * |y (.inl u)-(label u:ℝ)| + |y (.inl v)-(label v:ℝ)| := by
      apply (abs_sub _ _).trans
      apply add_le_add_right
      simpa only [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (J U))] using abs_sub
        (x*y (.inl w)-(i.val:ℝ)*(label w:ℝ)) ((J U:ℝ)*(y (.inl u)-(label u:ℝ)))
    _ ≤ (5*B+3)*E := by
      have hE := close_y v
      rw [hJ] at hlin
      rw [hJ]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (radius U)) he0]
    _ ≤ _ := more_precision

theorem L_selected (i : Fin U) (b : Bool) (w u v : Sel U) :
    |L (.inl (.inl (i,b))) (.inl w) (.inl u) (.inl v) -
       bit (decide ((i.val:ℤ)*label w=(J U:ℤ)*label u+label v))| ≤ epsilon U := by
  have hr := abs_le.mp (l_range (.inl (.inl (i,b))) (.inl w) (.inl u) (.inl v))
  have he := Counting.eq_arg_error (gate U) (by linarith [(bounds (U:=U)).1])
    (((i.val:ℤ)*label w-(J U:ℤ)*label u-label v)) (residual_error i b w u v) hr.1 hr.2
  have h : ((i.val:ℤ)*label w-(J U:ℤ)*label u-label v=0) ↔
      (i.val:ℤ)*label w=(J U:ℤ)*label u+label v := by omega
  simpa only [L, h] using he

private theorem s_range (w v : Pnt U) : |sine w*sine v/4| ≤ 1 := by
  rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4), div_le_one (by norm_num)]
  have hs (p : Pnt U) : |sine p| ≤ 1 := abs_le.mpr ⟨neg_one_le_sin _,sin_le_one _⟩
  have h := mul_le_mul (hs w) (hs v) (abs_nonneg _) zero_le_one
  linarith

theorem S_unit (w v : Pnt U) : UnitValue (S w v) :=
  (gate U).unit _ (abs_le.mp (s_range w v)).1 (abs_le.mp (s_range w v)).2

private def centeredAngle (w : Sel U) : ℝ := 2*π*(label w:ℝ)/(size U:ℝ)

private theorem sine_on_arc (w : Sel U) :
    sine (.inl w) = if arcSign w then -cos (centeredAngle w) else cos (centeredAngle w) := by
  let p := selectedEquiv U w
  have hh : ((roots U (.inl w)).val:ℤ) = atArc p.1 p.2 := by
    rw [roots_selected]; exact arc_val _ _
  have he : ((roots U (.inl w)).val:ℝ) = (atArc p.1 p.2:ℝ) := by exact_mod_cast hh
  have hq : 0 < Q U := by have := radius_lt_Q U; omega
  have hQr : (0:ℝ)<Q U := by exact_mod_cast hq
  have hm : (size U:ℝ) = 4*(Q U:ℝ) := by exact_mod_cast (fourQ U).symm
  have ha : 2*π*((Q U:ℝ)+(label w:ℝ))/(size U:ℝ) = centeredAngle w + π/2 := by
    unfold centeredAngle; rw [hm]; field_simp; ring
  have hb : 2*π*(4*(Q U:ℝ)-((Q U:ℝ)+(label w:ℝ)))/(size U:ℝ) =
      2*π-(centeredAngle w+π/2) := by
    rw [← ha,hm]; field_simp
  unfold sine
  rw [he]
  change _ = if p.2 then _ else _
  cases p.2 <;> simp only [atArc, Bool.false_eq_true, ↓reduceIte]
  · push_cast
    change sin (2*π*((Q U:ℝ)+(label w:ℝ))/(size U:ℝ)) = _
    rw [ha,sin_add_pi_div_two]
  · push_cast
    change sin (2*π*(4*(Q U:ℝ)-((Q U:ℝ)+(label w:ℝ)))/(size U:ℝ)) = _
    rw [hb,sin_two_pi_sub,sin_add_pi_div_two]

private theorem cos_on_arc (w : Sel U) : 1/2 ≤ cos (centeredAngle w) := by
  have hl : |(label w:ℝ)| ≤ (radius U:ℝ) := by unfold label; exact_mod_cast c_bound (selectedEquiv U w).1
  have hM0 : (0:ℝ)<size U := by linarith [(bounds (U:=U)).1]
  have hθ : |centeredAngle w| ≤ 1 := by
    rw [centeredAngle,abs_div,abs_mul,abs_of_pos hM0,abs_of_pos (by positivity : 0<2*π),div_le_one hM0]
    apply (mul_le_mul_of_nonneg_left hl (by positivity)).trans
    have h := mul_le_mul_of_nonneg_right pi_lt_four.le (Nat.cast_nonneg (α:=ℝ) (radius U))
    linarith [(ConcreteGrid.numeric (U:=U)).2.2.2]
  rw [← cos_pi_div_three, ← Real.cos_abs (centeredAngle w)]
  apply cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos])
  linarith [pi_gt_three]

theorem S_selected (w v : Sel U) :
    |S (.inl w) (.inl v) - bit (decide (arcSign w = arcSign v))| ≤ epsilon U := by
  have hr := abs_le.mp (s_range (.inl w) (.inl v))
  have hd := (delta_bounds U).1
  have hmul := mul_le_mul (cos_on_arc w) (cos_on_arc v) (by norm_num : (0:ℝ)≤1/2)
    (by linarith [cos_on_arc w])
  cases hw : arcSign w <;> cases hv : arcSign v <;>
    simp only [decide_true,decide_false,bit,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte] <;>
    first
    | apply (gate U).high _ _ hr.2
    | apply (gate U).low _ hr.1
  all_goals
    simp only [sine_on_arc,hw,hv,Bool.false_eq_true,↓reduceIte,neg_mul,mul_neg,neg_neg]
    linarith

end
end DiophantineNP.KernelSelectors
