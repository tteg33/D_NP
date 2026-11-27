import DiophantineNP.FormulaBackend

/-! # Rational Laurent syntax for the native grid's two observations -/
namespace DiophantineNP.FormulaLaurent

open ConcreteGrid LaurentBounds
open scoped BigOperators

noncomputable section

/-- The Wallis approximation as a rational scalar in the expression tree. -/
def piRational (n : ℕ) : ℚ := 16^n/((n:ℚ)*((2*n).choose n:ℚ)^2)

theorem piRational_real (n : ℕ) : ((piRational n:ℚ):ℝ) = Wallis.approxPi n := by
  simp [piRational, Wallis.approxPi]

def rational {d : ℕ} (q : ℚ) : Expr d := .scalar q.num ⟨q.den,q.den_pos⟩

theorem rational_eval {d : ℕ} (q : ℚ) (χ : Character d ℂ) :
    (rational q).evaluate χ = (q:ℂ) := by
  simp [rational, Expr.evaluate, Expr.expand, Expr.bounds, Raw.evaluate_atom,
    ← Pi.zero_def, Rat.cast_def]

def mono {d : ℕ} (j : Fin d) (s : ℤ) : Expr d := .monomial (Pi.single j s)

theorem mono_eval {d : ℕ} (j : Fin d) (s : ℤ) (χ : Character d ℂ) :
    (mono j s).evaluate χ = (χ (Pi.single j s)).toMul := by
  simp [mono, Expr.evaluate, Expr.expand, Expr.bounds, Raw.evaluate_atom]

def cosineLeaf {d : ℕ} (j : Fin d) : Expr d :=
  .mul (rational (1/2)) (.add (mono j 1) (mono j (-1)))

def xLeaf {d : ℕ} (U : ℕ) (j : Fin d) : Expr d :=
  .add (rational (radius U:ℚ))
    (.mul (rational (-(size U:ℚ)/(2*piRational ((size U)^4)))) (cosineLeaf j))

def yLeaf {d : ℕ} (U : ℕ) (j : Fin d) : Expr d :=
  .add (rational ((piRational ((size U)^4)*(2*(radius U:ℚ)+1)/(size U:ℚ))^2/4))
    (.mul (rational (-1/4)) (.pow (cosineLeaf j) 2))

/-- The complex standard character and its conjugate sum to twice the real
cosine at the corresponding grid angle. -/
theorem cosine_on_root {M : ℕ} [NeZero M] (l : ℕ) :
    (1/2:ℂ)*(ZMod.stdAddChar ((l:ℤ): ZMod M) +
      ZMod.stdAddChar ((-(l:ℤ)):ZMod M)) = (Real.cos (2*Real.pi*(l:ℝ)/M):ℂ) := by
  let θ : ℂ := ((2*Real.pi*(l:ℝ)/M : ℝ):ℂ)
  have hpos : ZMod.stdAddChar ((l:ℤ):ZMod M) = Complex.exp (θ*Complex.I) := by
    rw [ZMod.stdAddChar_coe]
    unfold θ
    push_cast
    congr 1
    ring
  have hneg : ZMod.stdAddChar ((-(l:ℤ)):ZMod M) = Complex.exp (-θ*Complex.I) := by
    calc
      _ = Complex.exp (2*(Real.pi:ℂ)*Complex.I*((-(l:ℤ)):ℂ)/M) :=
        by simpa only [Int.cast_neg] using ZMod.stdAddChar_coe (N := M) (-(l:ℤ))
      _ = _ := by unfold θ; push_cast; congr 1; ring
  rw [hpos,hneg,Complex.ofReal_cos,Complex.cos]
  change (1/2)*(Complex.exp (θ*Complex.I)+Complex.exp (-θ*Complex.I)) = _
  ring

/-- Leaf recovery requires only the two unit coordinate monomials. -/
theorem leaves_on_root {d U : ℕ} [NeZero (size U)] (j : Fin d) (p : Point U)
    (χ : Character d ℂ) (hmono : ∀ s : ℤ, (χ (Pi.single j s)).toMul =
      ZMod.stdAddChar ((s*(roots U p).val:ℤ):ZMod (size U))) :
    (xLeaf U j).evaluate χ = ((observed U).x p : ℂ) ∧
    (yLeaf U j).evaluate χ = ((observed U).Y p : ℂ) := by
  let c : ℝ := Real.cos (2*Real.pi*((roots U p).val:ℝ)/(size U:ℝ))
  have hcos : (cosineLeaf j).evaluate χ = (c:ℂ) := by
    rw [cosineLeaf, Expr.evaluate_mul, Expr.evaluate_add, rational_eval, mono_eval, mono_eval,
      hmono, hmono]
    simpa [c] using cosine_on_root (M := size U) (roots U p).val
  obtain ⟨hx,hy⟩ := observation_formulas p
  change (observed U).x p = (radius U:ℝ)-(size U:ℝ)*c/(2*Wallis.approxPi ((size U)^4)) at hx
  change (observed U).Y p =
    ((Wallis.approxPi ((size U)^4)*(2*(radius U:ℝ)+1)/(size U:ℝ))^2-c^2)/4 at hy
  have hp : ((piRational ((size U)^4)):ℂ) = (Wallis.approxPi ((size U)^4):ℂ) := by
    rw [← piRational_real]; norm_cast
  constructor
  · rw [xLeaf, Expr.evaluate_add, Expr.evaluate_mul, rational_eval, rational_eval, hcos,hx]
    push_cast
    rw [hp]
    ring
  · rw [yLeaf, Expr.evaluate_add, Expr.evaluate_mul, Expr.evaluate_pow, rational_eval, rational_eval,hcos,hy]
    push_cast
    rw [hp]
    ring

end
end DiophantineNP.FormulaLaurent
