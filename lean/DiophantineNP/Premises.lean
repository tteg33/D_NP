import DiophantineNP.HABVerified
import DiophantineNP.ProductCriterion
import DiophantineNP.EvaluatorPremises
import DiophantineNP.RegisterReduction

/-! # Inspecting the proof statements

The first group prints the specifications used in intermediate reductions.
The final commands display the closed conclusions from `HABVerified.lean`
and the axioms used by the numerical class equality. -/

#print DiophantineNP.PackedScalarPrograms
#print DiophantineNP.PowerTests.Cyclic
#print DiophantineNP.PowerTests.Quadratic
#print DiophantineNP.WidthFormula.LiteratureFormulas
#print DiophantineNP.Classes.JonesMatiyasevichDirection
#print DiophantineNP.Classes.PolynomialEvaluationInP
#print DiophantineNP.Classes.D
#print DiophantineNP.Classes.NP
#print DiophantineNP.NativeVerifier

#print axioms DiophantineNP.classEquality_of_evaluator
#print axioms DiophantineNP.nativeVerifier_of_evaluator

#print axioms DiophantineNP.classEquality_of_external
#print axioms DiophantineNP.nativeVerifier_of_external

#print DiophantineNP.FiniteArithmeticGap.ProductTemplate
#print DiophantineNP.Classes.Jones.NormalForm
#print DiophantineNP.JonesSourceDirection
#print DiophantineNP.boundedTraceLanguage
#print DiophantineNP.RegisterTraceNormalForm
#print DiophantineNP.Classes.FramedCircuitSimulation
#check DiophantineNP.nativeVerifier_of_rank_and_product
#check DiophantineNP.classEquality_of_rank_product_normalForm
#check DiophantineNP.classEquality_of_rank_product_compilers
#print axioms DiophantineNP.classEquality_of_rank_product_compilers

#check DiophantineNP.Classes.d_subset_np
#check DiophantineNP.Curve37.rank_one
#check DiophantineNP.classEquality_of_native
#check DiophantineNP.nativeVerifier_of_product
#check DiophantineNP.classEquality_of_product
#print axioms DiophantineNP.classEquality_of_product

#print DiophantineNP.HAB.ImultInFOM
#check DiophantineNP.classEquality_of_hab

#check DiophantineNP.HAB.corollary63
#check DiophantineNP.classEquality
#print axioms DiophantineNP.classEquality
