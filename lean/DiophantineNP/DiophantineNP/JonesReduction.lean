import DiophantineNP.CurveSaturation
import DiophantineNP.EvaluatorPacked
import DiophantineNP.JonesLength
import DiophantineNP.JonesNormalForm
import DiophantineNP.WidthProductOnly

/-! # From the Jones–Matiyasevich normal form to the bounded class equality -/
namespace DiophantineNP

/-- A rank upper bound and one uniform product formula suffice for the native verifier. -/
theorem nativeVerifier_of_rank_and_product
    (rank : Module.rank ℤ Curve37.E.Point ≤ 1)
    (product : FiniteArithmeticGap.ProductTemplate) : NativeVerifier :=
  Assembly.nativeVerifier_of_packing
    (packing_of_packedScalarSystems (packedScalarSystems_of_programs
      (Blueprint.packedScalarPrograms (Curve37.cyclic_of_rank_le_one rank)
        (Curve37.canonicalHeight_zsmul Curve37.P))))
    product.widthDescriptions

/-- The encoding-specific direction of equation (53), p. 827. -/
def JonesSourceDirection : Prop :=
  ∀ L : Classes.Language, L ∈ Classes.NP → Classes.Jones.NormalForm L

/-- Equations in the source normal form compile to a single bounded polynomial. -/
theorem np_subset_d_of_rank_product_normalForm
    (rank : Module.rank ℤ Curve37.E.Point ≤ 1)
    (product : FiniteArithmeticGap.ProductTemplate)
    (source : JonesSourceDirection) : Classes.NP ⊆ Classes.D :=
  fun L hL => Classes.Jones.mem_D_of_normalForm (source L hL)
    (nativeVerifier_of_rank_and_product rank product)
    (Classes.Jones.lengthGraph_of_curve (Curve37.cyclic_of_rank_le_one rank)
      (Curve37.canonicalHeight_zsmul Curve37.P))

/-- Class equality along the route through the single-mask source normal form. -/
theorem classEquality_of_rank_product_normalForm
    (rank : Module.rank ℤ Curve37.E.Point ≤ 1)
    (product : FiniteArithmeticGap.ProductTemplate)
    (source : JonesSourceDirection)
    (evaluation : Classes.PolynomialEvaluationInP) : Classes.D = Classes.NP :=
  Set.Subset.antisymm (Classes.D_subset_NP evaluation)
    (np_subset_d_of_rank_product_normalForm rank product source)

end DiophantineNP
