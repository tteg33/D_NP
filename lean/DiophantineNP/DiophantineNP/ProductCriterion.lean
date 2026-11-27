import DiophantineNP.CubicDescent
import DiophantineNP.VerifiedCompilers

/-! # The native verifier and class equality from one finite arithmetic formula -/
namespace DiophantineNP

/-- One finite formula for the low bits of the iterated product suffices for
an unrestricted-sound bit-inclusion verifier with polynomial honest witnesses. -/
theorem nativeVerifier_of_product (product : FiniteArithmeticGap.ProductTemplate) :
    NativeVerifier :=
  nativeVerifier_of_rank_and_product Curve37.rank_one.le product

/-- The class equality from an arbitrary uniform product template. `HABVerified.lean`
instantiates the corresponding finite-logic theorem for the unconditional result. -/
theorem classEquality_of_product (product : FiniteArithmeticGap.ProductTemplate) :
    Classes.D = Classes.NP :=
  classEquality_of_native (nativeVerifier_of_product product)

end DiophantineNP
