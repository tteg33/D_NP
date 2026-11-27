import DiophantineNP.Curve37

/-! The quadratic scaling law for powers of two, and a numerical bound
on the canonical height of the proposed generator, both hold unconditionally. -/

namespace DiophantineNP.Curve37

open Filter

theorem canonical_double (Q : E.Point) :
    canonicalHeight (Q+Q) = 4*canonicalHeight Q := by
  apply tendsto_nhds_unique (canonical_limit (Q+Q))
  have h := (canonical_limit Q).comp (tendsto_add_atTop_nat 1)
  refine (h.const_mul 4).congr' (Eventually.of_forall (fun n => ?_))
  change 4*(logHeight ((2^(n+1) : ℕ) • Q)/(4 : ℝ)^(n+1)) =
    logHeight ((2^n : ℕ) • (Q+Q))/(4 : ℝ)^n
  rw [pow_succ 2 n,Nat.mul_two,add_nsmul,nsmul_add,pow_succ]
  field_simp

theorem canonical_two_pow (Q : E.Point) (n : ℕ) :
    canonicalHeight ((2^n : ℕ) • Q) = 4^n*canonicalHeight Q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ 2 n,Nat.mul_two,add_nsmul,canonical_double,ih,pow_succ]
    ring

theorem canonical_generator_bounds :
    1/20 < canonicalHeight P ∧ canonicalHeight P < 1/10 := by
  have h := canonical_comparison ((16 : ℕ) • P)
  have hc := canonical_two_pow P 4
  norm_num at hc
  rw [hc] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  have ⟨hb₁,hb₂⟩ := logHeight_sixteen
  change (18:ℝ) < logHeight ((16 : ℕ) • P) at hb₁
  change logHeight ((16 : ℕ) • P) < (19:ℝ) at hb₂
  constructor <;> linarith

/-- The generator candidate has infinite order. This establishes injectivity
of the multiples parameterization, leaving surjectivity as a separate input. -/
theorem generator_infinite_order : ¬ IsOfFinAddOrder P := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  rintro ⟨m,hm,hzero⟩
  let M : ℕ := (Finset.range m).sup (fun i : ℕ => height (i • P))
  have hred (k : ℕ) : k • P = (k%m) • P := by
    calc k • P = ((k%m)+m*(k/m)) • P := congrArg (fun i : ℕ => i • P) (Nat.mod_add_div k m).symm
         _ = _ := by rw [add_nsmul,mul_nsmul,hzero,nsmul_zero,add_zero]
  have hM (k : ℕ) : height (k • P) ≤ M := by
    rw [hred k]
    exact Finset.le_sup (s := Finset.range m) (f := fun i : ℕ => height (i • P)) (Finset.mem_range.mpr (Nat.mod_lt _ hm))
  let C := Real.logb 2 (M : ℝ)
  have hlim : Tendsto (fun n : ℕ => C/(4 : ℝ)^n) atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 4⁻¹) (by norm_num)).const_mul C
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using h
  have hn := le_of_tendsto_of_tendsto' (canonical_limit P) hlim (fun n => by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast height_pos ((2^n : ℕ) • P))
      (by exact_mod_cast hM (2^n)))
  linarith only [hn, canonical_generator_bounds.1]

end DiophantineNP.Curve37
