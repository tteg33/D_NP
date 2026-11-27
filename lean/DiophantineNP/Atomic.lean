import DiophantineNP.Counting

/-! # Finite arithmetic atoms evaluated on approximate labels

The equality and order polynomials here are the exact expressions of §3.3.
Their input hypotheses are numerical label estimates from §3.2. In
particular, each occurrence of multiplication is interpreted in the integers.
-/

namespace DiophantineNP.Counting

noncomputable section

/-- The integer residual of an atomic formula, or the real residual obtained by
substituting approximate labels. Order is represented by a nonnegative value. -/
def Atom.residual {S : Type*} [Ring S] {k : ℕ} (a : Atom k) (z : Fin k → S) : S :=
  match a with
  | .eqv i j => z i - z j
  | .leq i j => z j - z i
  | .add i j l => z i + z j - z l
  | .mul i j l => z i * z j - z l

def Atom.isOrder {k : ℕ} : Atom k → Bool
  | .leq _ _ => true
  | _ => false

theorem Atom.eval_residual {k U : ℕ} (a : Atom k) (u : Fin k → Fin U) :
    a.eval u =
      if a.isOrder then decide (0 ≤ a.residual (fun i => ((u i : ℕ) : ℤ)))
      else decide (a.residual (fun i => ((u i : ℕ) : ℤ)) = 0) := by
  cases a <;> simp only [Atom.isOrder, Atom.eval, Atom.residual, Bool.false_eq_true, ↓reduceIte,
    sub_nonneg, sub_eq_zero, ← Nat.cast_add, ← Nat.cast_mul, Int.ofNat_le, Int.natCast_inj,
    Fin.ext_iff, Fin.le_def]

private theorem residual_bound {k : ℕ} (a : Atom k) (z : Fin k → ℝ) {M : ℝ}
    (hM : 2 ≤ M) (hz : ∀ i, |z i| ≤ M) :
    |a.residual z| ≤ 2*M^2 := by
  have hm : M ≤ M^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ M-1) (by linarith : 0 ≤ M)]
  have h3 : 3*M ≤ 2*M^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ M-2) (by linarith : 0 ≤ M)]
  cases a with
  | eqv i j | leq j i =>
    exact (abs_sub_le (z i) 0 (z j)).trans (by simp only [sub_zero, zero_sub, abs_neg]; linarith [hz i, hz j])
  | add i j l =>
    calc
      _ ≤ |z i + z j| + |z l| := abs_sub _ _
      _ ≤ 2*M^2 := by linarith [abs_add_le (z i) (z j), hz i, hz j, hz l]
  | mul i j l =>
    calc
      _ ≤ |z i*z j| + |z l| := abs_sub _ _
      _ ≤ 2*M^2 := by
        rw [abs_mul]
        have := mul_le_mul (hz i) (hz j) (abs_nonneg _) (by linarith : 0 ≤ M)
        nlinarith [hz l]

private theorem residual_close {k : ℕ} (a : Atom k) (z u : Fin k → ℝ) {B E : ℝ}
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hle : E ≤ 1)
    (hu : ∀ i, |u i| ≤ B) (hz : ∀ i, |z i-u i| ≤ E) :
    |a.residual z - a.residual u| ≤ (2*B+3)*E := by
  have he : 0 ≤ B*E := mul_nonneg hB hE
  have addbound (i : Fin k) : |z i| ≤ B+E := by
    calc
      _ ≤ |z i-u i| + |u i| := by simpa only [sub_zero] using abs_sub_le (z i) (u i) 0
      _ ≤ _ := by linarith [hu i, hz i]
  have diff (i j : Fin k) : |(z i - z j) - (u i - u j)| ≤ (2*B+3)*E := by
    rw [show (z i-z j)-(u i-u j)=(z i-u i)-(z j-u j) by ring]
    nlinarith [abs_sub (z i-u i) (z j-u j), hz i, hz j]
  cases a with
  | eqv i j | leq j i => exact diff i j
  | add i j l =>
    change |(z i+z j-z l)-(u i+u j-u l)| ≤ _
    rw [show (z i+z j-z l)-(u i+u j-u l)=(z i-u i)+(z j-u j)-(z l-u l) by ring]
    nlinarith [abs_sub ((z i-u i)+(z j-u j)) (z l-u l), abs_add_le (z i-u i) (z j-u j),
      hz i, hz j, hz l]
  | mul i j l =>
    change |(z i*z j-z l)-(u i*u j-u l)| ≤ _
    rw [show (z i*z j-z l)-(u i*u j-u l)=(z i-u i)*z j + u i*(z j-u j) - (z l-u l) by ring]
    have h₁ := mul_le_mul (hz i) (addbound j) (abs_nonneg _) hE
    have h₂ := mul_le_mul (hu i) (hz j) (abs_nonneg _) hB
    have h₃ := abs_sub ((z i-u i)*z j + u i*(z j-u j)) (z l-u l)
    have h₄ := abs_add_le ((z i-u i)*z j) (u i*(z j-u j))
    simp only [abs_mul] at h₄
    nlinarith [hz l, mul_nonneg hE (sub_nonneg.mpr hle)]

/-- The normalized test used in the arithmetic atoms. -/
def atomArgument {k : ℕ} (a : Atom k) (z : Fin k → ℝ) (M : ℝ) : ℝ :=
  if a.isOrder then (a.residual z + 1/2)/(8*M^4)
  else (1/4 - (a.residual z)^2)/(8*M^4)

private theorem argument_range {k : ℕ} (a : Atom k) (z : Fin k → ℝ) {M : ℝ}
    (hM : 2 ≤ M) (hz : ∀ i, |z i| ≤ M) : |atomArgument a z M| ≤ 1 := by
  have hp : 0 < 8*M^4 := by positivity
  have hm2 : 1 ≤ M^2 := one_le_pow₀ (by linarith) (n := 2)
  have hm4 : M^2 ≤ M^4 := by nlinarith [mul_nonneg (sq_nonneg M) (by linarith : 0 ≤ M^2 - 1), sq_nonneg M]
  have hA := residual_bound a z hM hz
  have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2*M^2)).2 hA
  rw [sq_abs] at hsq
  obtain ⟨ha,hb⟩ := abs_le.mp hA
  unfold atomArgument
  split <;> apply abs_le.mpr <;> constructor
  all_goals first | apply (le_div_iff₀ hp).mpr | apply (div_le_iff₀ hp).mpr
  all_goals nlinarith [sq_nonneg (a.residual z)]

theorem eq_arg_error {ε M A : ℝ} (T : Threshold ε (1/(64*M^4))) (hM : 0 < M)
    (j : ℤ) (near : |A - (j : ℝ)| ≤ 1/8)
    (lo : -1 ≤ (1/4-A^2)/(8*M^4)) (hi : (1/4-A^2)/(8*M^4) ≤ 1) :
    |T.H ((1/4-A^2)/(8*M^4)) - bit (decide (j=0))| ≤ ε := by
  have hp : 0 < 8*M^4 := by positivity
  have hd : 1/(64*M^4) = (1/8)/(8*M^4) := by field_simp; ring
  by_cases h : j=0
  · subst j
    simp only [decide_true, bit, ↓reduceIte]
    apply T.high _ _ hi
    rw [hd, div_le_div_iff_of_pos_right hp]
    have h' : |A| ≤ 1/8 := by simpa using near
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/8)).2 h'
    rw [sq_abs] at hsq
    nlinarith
  · simp only [h, decide_false, bit, Bool.false_eq_true, ↓reduceIte]
    apply T.low _ lo
    rw [hd, ← neg_div, div_le_div_iff_of_pos_right hp]
    have habs : (1:ℝ) ≤ |(j:ℝ)| := by
      by_cases hj : 0 < j
      · rw [abs_of_nonneg (by exact_mod_cast hj.le)]
        exact_mod_cast (show 1 ≤ j by omega)
      · have hj' : j < 0 := by omega
        rw [abs_of_neg (by exact_mod_cast hj')]
        exact_mod_cast (show 1 ≤ -j by omega)
    have close := abs_sub_le (j:ℝ) A 0
    rw [sub_zero, sub_zero, abs_sub_comm (j:ℝ) A] at close
    have h' : 7/8 ≤ |A| := by linarith
    have hsq := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 7/8) (abs_nonneg _)).2 h'
    rw [sq_abs] at hsq
    nlinarith

theorem le_arg_error {ε M A : ℝ} (T : Threshold ε (1/(64*M^4))) (hM : 0 < M)
    (j : ℤ) (near : |A - (j : ℝ)| ≤ 1/8)
    (lo : -1 ≤ (A+1/2)/(8*M^4)) (hi : (A+1/2)/(8*M^4) ≤ 1) :
    |T.H ((A+1/2)/(8*M^4)) - bit (decide (0≤j))| ≤ ε := by
  have hp : 0 < 8*M^4 := by positivity
  have hd : 1/(64*M^4) = (1/8)/(8*M^4) := by field_simp; ring
  obtain ⟨_,_⟩ := abs_le.mp near
  by_cases h : 0 ≤ j
  · simp only [h, decide_true, bit, ↓reduceIte]
    apply T.high _ _ hi
    rw [hd, div_le_div_iff_of_pos_right hp]
    have : (0:ℝ) ≤ j := by exact_mod_cast h
    linarith
  · simp only [h, decide_false, bit, Bool.false_eq_true, ↓reduceIte]
    apply T.low _ lo
    rw [hd, ← neg_div, div_le_div_iff_of_pos_right hp]
    have : (j:ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
    linarith

/-- Uniform global boundedness on the entire grid. -/
theorem atom_unit {k : ℕ} (a : Atom k) (z : Fin k → ℝ) {M ε : ℝ}
    (T : Threshold ε (1/(64*M^4))) (hM : 2 ≤ M) (hz : ∀ i, |z i| ≤ M) :
    UnitValue (T.H (atomArgument a z M)) :=
  T.unit _ (abs_le.mp (argument_range a z hM hz)).1 (abs_le.mp (argument_range a z hM hz)).2

/-- Assuming the numerical label bounds, the exact atom polynomial returns
the indicator of the finite arithmetic relation to error at most ε. -/
theorem atom_error {k U : ℕ} (a : Atom k) (u : Fin k → Fin U) (z : Fin k → ℝ)
    {M B E ε : ℝ} (T : Threshold ε (1/(64*M^4))) (hM : 2 ≤ M) (hz : ∀ i, |z i| ≤ M)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hle : E ≤ 1) (small : (2*B+3)*E ≤ 1/8)
    (hu : ∀ i, ((u i : ℕ):ℝ) ≤ B) (close : ∀ i, |z i - ((u i:ℕ):ℝ)| ≤ E) :
    |T.H (atomArgument a z M) - bit (a.eval u)| ≤ ε := by
  let r := a.residual (fun i => ((u i : ℕ):ℤ))
  have hr : (r:ℝ) = a.residual (fun i => ((u i : ℕ):ℝ)) := by
    cases a <;> simp [r, Atom.residual]
  have near : |a.residual z - (r:ℝ)| ≤ 1/8 := by
    rw [hr]
    refine (residual_close a _ _ hB hE hle (fun i => ?_) close).trans small
    simpa only [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (u i).val)] using hu i
  have ⟨lo,hi⟩ := abs_le.mp (argument_range a z hM hz)
  rw [Atom.eval_residual]
  unfold atomArgument at *
  cases h : a.isOrder <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at *
  · exact eq_arg_error T (by linarith) r near lo hi
  · exact le_arg_error T (by linarith) r near lo hi

end
end DiophantineNP.Counting
