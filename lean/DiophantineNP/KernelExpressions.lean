import DiophantineNP.FormulaGrowth
import DiophantineNP.KernelSelectors

/-! # Laurent expressions for the two Fourier selectors and the carrier -/
namespace DiophantineNP.FormulaLaurent
open Counting ConcreteGrid LaurentBounds
open scoped BigOperators
noncomputable section
variable {U d : ℕ}

/-- The integer `size / J`, in the explicit factored parametrization. -/
def stride (U : ℕ) := 4*(2*radius U+2)^30

def centeredExpr (U : ℕ) (j : Fin d) : Expr d := sub (xLeaf U j) (const (radius U))
def eqResidual (U : ℕ) (z w u v : Fin d) : Expr d :=
  sub (sub ((xLeaf U z).mul (centeredExpr U w)) ((const (J U)).mul (centeredExpr U u))) (centeredExpr U v)

def LExpr (U : ℕ) (z w u v : Fin d) : Expr d :=
  tail U (normalize U (sub (const (1/4)) ((eqResidual U z w u v).pow 2)))
def diffExpr (j : Fin d) : Expr d := sub (mono j 1) (mono j (-1))
def SExpr (U : ℕ) (w v : Fin d) : Expr d :=
  tail U (((diffExpr w).mul (diffExpr v)).mul (const (-1/16)))
def carrierExpr (U : ℕ) (w v : Fin d) : Expr d :=
  ((mono v 1).pow (stride U)).mul (.geometric w (stride U) (J U))

private theorem eval_centered (a : Fin d → Point U) (j : Fin d) :
    (centeredExpr U j).evaluate (gridChar a) = (KernelSelectors.y (a j) : ℂ) := by
  simp [centeredExpr, eval_sub, KernelSelectors.y]
  exact (concreteBackend U d).eval_x j a

theorem eval_LExpr (a : Fin d → Point U) (z w u v : Fin d) :
    (LExpr U z w u v).evaluate (gridChar a) = (KernelSelectors.L (a z) (a w) (a u) (a v) : ℂ) := by
  unfold LExpr KernelSelectors.L
  apply eval_tail
  unfold normalize
  rw [Expr.evaluate_mul, eval_sub, Expr.evaluate_pow, eval_const, eval_const]
  simp only [eqResidual, eval_sub, Expr.evaluate_mul, eval_const, eval_centered]
  rw [show (xLeaf U z).evaluate (gridChar a) = ((observed U).x (a z):ℂ) from (concreteBackend U d).eval_x z a]
  unfold KernelSelectors.residual
  push_cast
  ring

private theorem exp_difference {M : ℕ} [NeZero M] (l : ℕ) :
    ZMod.stdAddChar ((l:ℤ): ZMod M)-ZMod.stdAddChar ((-(l:ℤ)): ZMod M) =
     (2*Complex.I)*(Real.sin (2*Real.pi*(l:ℝ)/M):ℂ) := by
  let θ : ℂ := ((2*Real.pi*(l:ℝ)/M:ℝ):ℂ)
  have pos : ZMod.stdAddChar ((l:ℤ):ZMod M) = Complex.exp (θ*Complex.I) := by
    rw [ZMod.stdAddChar_coe]
    unfold θ; push_cast; congr 1; ring
  have neg : ZMod.stdAddChar ((-(l:ℤ)):ZMod M) = Complex.exp (-θ*Complex.I) := by
    calc
      _ = Complex.exp (2*(Real.pi:ℂ)*Complex.I*((-(l:ℤ)):ℂ)/M) := by
        simpa only [Int.cast_neg] using ZMod.stdAddChar_coe (N := M) (-(l:ℤ))
      _ = _ := by unfold θ; push_cast; congr 1; ring
  rw [pos,neg,Complex.ofReal_sin,Complex.sin]
  change _ = (2*Complex.I)*((Complex.exp (-θ*Complex.I)-Complex.exp (θ*Complex.I))*Complex.I/2)
  linear_combination (Complex.exp (θ*Complex.I)-Complex.exp (-θ*Complex.I))*Complex.I_sq

private theorem eval_diff (a : Fin d → Point U) (j : Fin d) :
    (diffExpr j).evaluate (gridChar a) = 2*Complex.I*(KernelSelectors.sine (a j):ℂ) := by
  simp only [diffExpr, eval_sub, mono_eval, gridChar_single, one_mul, neg_one_mul]
  simpa only [Int.cast_neg, KernelSelectors.sine] using exp_difference (M := size U) (roots U (a j)).val

theorem eval_SExpr (a : Fin d → Point U) (w v : Fin d) :
    (SExpr U w v).evaluate (gridChar a) = (KernelSelectors.S (a w) (a v):ℂ) := by
  unfold SExpr KernelSelectors.S
  apply eval_tail
  rw [Expr.evaluate_mul, Expr.evaluate_mul, eval_diff, eval_diff, eval_const]
  push_cast
  linear_combination (-(KernelSelectors.sine (a w):ℂ)*(KernelSelectors.sine (a v):ℂ)/4) * Complex.I_sq

private theorem eval_geom_sum (a : Fin d → Point U) (w : Fin d) (d' J' : ℕ) :
    (Expr.geometric w d' J').evaluate (gridChar a) = ∑ b ∈ Finset.range J',
      (2*(ZMod.stdAddChar (rootIndex (a w))^d')⁻¹)^b := by
  let r : ℂ := 2*(ZMod.stdAddChar (rootIndex (a w))^d')⁻¹
  have hs : Raw.step w d' = Pi.single w (-(d':ℤ)) := by
    funext j
    by_cases h : j=w
    · subst j; simp [Raw.step]
    · simp [Raw.step, h]
  have hh : (gridChar a (Raw.step w d')).toMul = (ZMod.stdAddChar (rootIndex (a w))^d')⁻¹ := by
    rw [hs, gridChar_single]
    simp only [neg_mul, Int.cast_neg, Int.cast_mul, Int.cast_natCast, AddChar.map_neg_eq_inv]
    congr 1
    rw [← AddChar.map_nsmul_eq_pow]
    simp [rootIndex, nsmul_eq_mul]
  rw [Expr.evaluate_geometric, hh]
  change (if r=1 then (J':ℂ) else (r^J'-1)/(r-1)) = ∑ b ∈ Finset.range J', r^b
  by_cases hr : r=1
  · simp [hr]
  · rw [if_neg hr, div_eq_iff (sub_ne_zero.mpr hr), geom_sum_mul]

theorem eval_carrierExpr (a : Fin d → Point U) (w v : Fin d) :
    (carrierExpr U w v).evaluate (gridChar a) =
      ∑ b : Fin (J U), ZMod.stdAddChar (rootIndex (a v)) ^ stride U *
        (2*(ZMod.stdAddChar (rootIndex (a w))^stride U)⁻¹)^b.val := by
  have hmono : (mono v 1).evaluate (gridChar a) = ZMod.stdAddChar (rootIndex (a v)) := by
    rw [mono_eval, gridChar_single, one_mul]; simp only [Int.cast_natCast, rootIndex]
  rw [carrierExpr, Expr.evaluate_mul, Expr.evaluate_pow, hmono, eval_geom_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun b => (2*(ZMod.stdAddChar (rootIndex (a w))^stride U)⁻¹)^b)]
  rw [Finset.mul_sum]

end
end DiophantineNP.FormulaLaurent
