import DiophantineNP.FourGridKernel
import DiophantineNP.KernelSelectors

/-! # Certified rounding on the four concrete cyclic grids -/
namespace DiophantineNP.FourGrid
open ConcreteGrid Counting KernelSelectors Finset
noncomputable section
attribute [local irreducible] L S output observed

abbrev Four (U : ℕ) := Point U × Point U × Point U × Point U

variable {k U : ℕ}
abbrev window (z : Point U) := (observed U).tests.window z

/-- The seven real factors multiplying the geometric-series carrier. -/
def actual (φ : Formula (k+1)) (t : Fin k → Fin U) (z w u v : Point U) : ℝ :=
  output φ t z * window z * window w * window u * window v * L z w u v * S w v

private def intendedOutput (φ : Formula (k+1)) (t : Fin k → Fin U) : Point U → ℝ
  | .inl (.inl (i,_)) => bit (φ.eval (Fin.cases i t))
  | .inl (.inr _) => 0
  | .inr o => output φ t (.inr o)

private def intendedWindow : Point U → ℝ
  | .inl _ => 1
  | .inr _ => 0

private def intendedL : Point U → Point U → Point U → Point U → ℝ
  | .inl (.inl (i,_)), .inl w, .inl u, .inl v => bit (decide ((i.val:ℤ)*label w=(J U:ℤ)*label u+label v))
  | z, w, u, v => L z w u v

private def intendedS : Point U → Point U → ℝ
  | .inl w, .inl v => bit (decide (arcSign w=arcSign v))
  | w, v => S w v

private theorem unit_bit (b : Bool) : UnitValue (bit b) := by cases b <;> norm_num [bit,UnitValue]

private theorem intended_output (φ : Formula (k+1)) (t : Fin k → Fin U) (z : Point U) :
    UnitValue (intendedOutput φ t z) ∧ |output φ t z-intendedOutput φ t z| ≤ epsilon U := by
  rcases z with ((⟨i,b⟩|a)|o)
  · exact ⟨unit_bit _,output_valid φ t i b⟩
  · exact ⟨⟨le_rfl,zero_le_one⟩,output_invalid φ t a⟩
  · exact ⟨output_unit φ t _,by simp [intendedOutput,epsilon]⟩

private theorem intended_window (z : Point U) :
    UnitValue (intendedWindow z) ∧ |window z-intendedWindow z| ≤ epsilon U := by
  cases z with
  | inl a => exact ⟨⟨zero_le_one,le_rfl⟩,(observed U).tests.window_selected a⟩
  | inr o => exact ⟨⟨le_rfl,zero_le_one⟩,(observed U).tests.window_off o⟩

private theorem intended_l (z w u v : Point U) :
    UnitValue (intendedL z w u v) ∧ |L z w u v-intendedL z w u v| ≤ epsilon U := by
  rcases z with ((⟨i,b⟩|a)|o) <;> cases w <;> cases u <;> cases v
  · exact ⟨unit_bit _,L_selected _ _ _ _ _⟩
  all_goals exact ⟨L_unit _ _ _ _,by change |L _ _ _ _-L _ _ _ _| ≤ _; rw [sub_self,abs_zero]; exact (observed U).tests.eps_nonneg⟩

private theorem intended_s (w v : Point U) :
    UnitValue (intendedS w v) ∧ |S w v-intendedS w v| ≤ epsilon U := by
  cases w <;> cases v
  case inl.inl => exact ⟨unit_bit _,S_selected _ _⟩
  all_goals exact ⟨S_unit _ _,by change |S _ _ - S _ _| ≤ _; rw [sub_self,abs_zero]; exact (observed U).tests.eps_nonneg⟩

private theorem bit_and (a b : Bool) : bit (a && b) = bit a * bit b := by cases a <;> cases b <;> simp [bit]

private theorem selected_bits (a b c : Bool) :
    bit a * 1 * 1 * 1 * 1 * bit c * bit b = bit (a && b && c) := by
  simp only [mul_one, bit_and, mul_right_comm]

private theorem intended_product (φ : Formula (k+1)) (t : Fin k → Fin U) (z w u v : Point U) :
    intendedOutput φ t z * intendedWindow z * intendedWindow w * intendedWindow u * intendedWindow v *
      intendedL z w u v * intendedS w v = bit (ideal (fun i => φ.eval (Fin.cases i t)) z w u v) := by
  rcases z with ((⟨i,b⟩|a)|o)
  · rcases w with w | o
    · rcases u with u | o
      · rcases v with v | o
        · exact selected_bits _ _ _
        · change _ * 0 * _ * _ = 0
          rw [mul_zero,zero_mul,zero_mul]
      · change _ * 0 * _ * _ * _ = 0
        rw [mul_zero,zero_mul,zero_mul,zero_mul]
    · change _ * 0 * _ * _ * _ * _ = 0
      rw [mul_zero,zero_mul,zero_mul,zero_mul,zero_mul]
  · change 0 * _ * _ * _ * _ * _ * _ = 0
    simp only [zero_mul]
  · change _ * 0 * _ * _ * _ * _ * _ = 0
    simp only [mul_zero,zero_mul]

private structure Close (ε a b : ℝ) : Prop where
  left : UnitValue a
  right : UnitValue b
  error : |a-b| ≤ ε

private theorem Close.mul {ε δ a b c d : ℝ} (h : Close ε a b) (g : Close δ c d) :
    Close (ε+δ) (a*c) (b*d) := by
  refine ⟨⟨mul_nonneg h.left.1 g.left.1,mul_le_one₀ h.left.2 g.left.1 g.left.2⟩,
    ⟨mul_nonneg h.right.1 g.right.1,mul_le_one₀ h.right.2 g.right.1 g.right.2⟩,?_⟩
  calc
    _ = |(a-b)*c+b*(c-d)| := by congr 1; ring
    _ ≤ |(a-b)*c|+|b*(c-d)| := abs_add_le _ _
    _ ≤ ε+δ := by
      rw [abs_mul,abs_mul,abs_of_nonneg h.right.1,abs_of_nonneg g.left.1]
      exact add_le_add ((mul_le_of_le_one_right (abs_nonneg _) g.left.2).trans h.error)
        ((mul_le_of_le_one_left (abs_nonneg _) h.right.2).trans g.error)

/-- All grid points obey the same estimate, including points outside a window. -/
theorem selector_error (φ : Formula (k+1)) (t : Fin k → Fin U) (z w u v : Point U) :
    |actual φ t z w u v-bit (ideal (fun i => φ.eval (Fin.cases i t)) z w u v)| ≤ 7*epsilon U := by
  have hO : Close (epsilon U) (output φ t z) (intendedOutput φ t z) :=
    ⟨output_unit _ _ _,(intended_output _ _ _).1,(intended_output _ _ _).2⟩
  have hW (p : Point U) : Close (epsilon U) (window p) (intendedWindow p) :=
    ⟨(observed U).tests.window_unit _,(intended_window _).1,(intended_window _).2⟩
  have hL : Close (epsilon U) (L z w u v) (intendedL z w u v) :=
    ⟨L_unit _ _ _ _,(intended_l _ _ _ _).1,(intended_l _ _ _ _).2⟩
  have hS : Close (epsilon U) (S w v) (intendedS w v) :=
    ⟨S_unit _ _,(intended_s _ _).1,(intended_s _ _).2⟩
  have h := ((((((hO.mul (hW z)).mul (hW w)).mul (hW u)).mul (hW v)).mul hL).mul hS).error
  rw [← intended_product,actual]
  exact h.trans_eq (by ring)

/-- The manuscript's unnormalized fourfold sum, divided by the exact
multiplicity of its native output digits. -/
def readout (φ : Formula (k+1)) (t : Fin k → Fin U) : ℂ :=
  (∑ z, ∑ w, ∑ u, ∑ v, (actual φ t z w u v:ℂ)*carrier w v)/(8*(J U:ℂ))

/-- The explicit finite complex sum is within one quarter of the native word. -/
theorem readout_close (φ : Formula (k+1)) (t : Fin k → Fin U) :
    ‖readout φ t-(Packing.packed φ t:ℂ)‖ < 1/4 := by
  let a (p : Four U) := actual φ t p.1 p.2.1 p.2.2.1 p.2.2.2
  let b (p : Four U) := bit (ideal (fun i => φ.eval (Fin.cases i t)) p.1 p.2.1 p.2.2.1 p.2.2.2)
  let c (p : Four U) := carrier p.2.1 p.2.2.2
  have hg := BinaryKernel.grid_sum_error a b c (ε:=epsilon U) (K:=(2:ℝ)^(J U))
    (by unfold epsilon; positivity) (fun p => selector_error φ t _ _ _ _) (fun p => carrier_bound _ _)
  have hcard : Fintype.card (Four U) = size U ^ 4 := by
    simp only [Four,Fintype.card_prod,(observed U).card_eq]
    ring
  have hb (q : Bool) (x : ℂ) : (bit q:ℂ)*x = if q then x else 0 := by cases q <;> simp [bit]
  simp only [a,b,c,Fintype.sum_prod_type,hcard,Nat.cast_pow,hb] at hg
  rw [ideal_sum] at hg
  have hJ : 0 < J U := by unfold J; omega
  have hpos : (0:ℝ) < 8*(J U:ℝ) := by positivity
  have hn : 8*(J U:ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hr := BinaryKernel.readout_precision (size U) (J U) (precision U) hJ (by unfold J precision; omega)
  rw [readout, div_sub' hn, norm_div]
  rw [norm_mul, Complex.norm_natCast, Complex.norm_ofNat]
  apply lt_of_le_of_lt (div_le_div_of_nonneg_right hg hpos.le)
  convert hr using 1
  unfold epsilon
  ring

end
end DiophantineNP.FourGrid
