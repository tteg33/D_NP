import DiophantineNP.CubicDescent
import DiophantineNP.CubicIntegralReduction

/-! # The native verifier and class equality from one finite arithmetic formula -/
namespace DiophantineNP

/-- The generator (0,0) spans the rational points of the specified Weierstrass curve. -/
theorem Curve37.rational_points_cyclic : PowerTests.Cyclic :=
  Curve37.Kummer.cyclic_of_unitTimesSquare Curve37.Kummer.image_eq_unit_mul_square

/-- The algebraic Mordell–Weil rank on the actual mathlib point type. -/
theorem Curve37.rank_one : Module.rank ℤ Curve37.E.Point = 1 :=
  Curve37.cyclic_iff_rank_one.mp Curve37.rational_points_cyclic

/-- One finite formula for the low bits of the iterated product suffices for
an unrestricted-sound bit-inclusion verifier with polynomial honest witnesses. -/
theorem nativeVerifier_of_product (product : FiniteArithmeticGap.ProductTemplate) :
    NativeVerifier :=
  nativeVerifier_of_rank_and_product Curve37.rank_one.le product

/-- All machine and arithmetic steps except for the uniform product template
have been discharged on the pinned model. -/
theorem classEquality_of_product (product : FiniteArithmeticGap.ProductTemplate) :
    Classes.D = Classes.NP :=
  classEquality_of_native (nativeVerifier_of_product product)

end DiophantineNP
