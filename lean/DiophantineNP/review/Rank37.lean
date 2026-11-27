import DiophantineNP.CubicDescent
import Lean.Util.CollectAxioms

/-! # The rational points on the curve 37a1

The Weierstrass coefficients below give `y² + y = x³ - x`. The two conclusions
specify its algebraic Mordell–Weil rank and the point generating its rational
point group.
-/

namespace Review.Rank37

abbrev curve : WeierstrassCurve.Affine ℚ := ⟨0, 0, 1, -1, 0⟩

def generator : curve.Point :=
  .some (x := 0) (y := 0)
    (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
      WeierstrassCurve.Affine.equation_iff, curve])

theorem rank_and_generator :
    Module.rank ℤ curve.Point = 1 ∧ ∀ Q : curve.Point, ∃ m : ℤ, m • generator = Q :=
  ⟨DiophantineNP.Curve37.rank_one, DiophantineNP.Curve37.rational_points_cyclic⟩

open Lean Elab Command in
run_cmd do
  let axioms ← collectAxioms ``rank_and_generator
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "Unexpected axiom in the rank or generator theorem: {axioms}"
  logInfo m!"Rank and generator use {axioms}."

end Review.Rank37
