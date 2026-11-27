import DiophantineNP
import Lean.Util.CollectAxioms

#check DiophantineNP.WidthData.native_certificate_iff
#check DiophantineNP.ModularPolynomial.native_natural_complete
#check DiophantineNP.MathlibPower.exponential_witness
#check DiophantineNP.Assembly.nativeVerifier_of_packing
#check DiophantineNP.classEquality_of_packing
#check DiophantineNP.classEquality_of_templates
#check DiophantineNP.FormulaLaurent.truthExpr_uniform_size
#check DiophantineNP.ScalarProjection.scalarRecipe_expr
#check DiophantineNP.PowerPolynomial.witness_arity
#check DiophantineNP.PowerPolynomial.exact_over_integers
#check DiophantineNP.PowerPolynomial.complete_quartic
#check DiophantineNP.FormulaLaurent.packedExpr_uniform_size
#check DiophantineNP.FormulaLaurent.packedScalar_short_fraction
#check DiophantineNP.FormulaLaurent.packedScalar_close
#check DiophantineNP.packedScalarSystems_of_programs
#check DiophantineNP.PackedScalarSystems
#check DiophantineNP.packing_of_packedScalarSystems
#check DiophantineNP.nativeVerifier_of_packedScalarSystems
#check DiophantineNP.classEquality_of_packedScalarSystems
#print axioms DiophantineNP.classEquality_of_packedScalarSystems

#check DiophantineNP.Curve37.generator_infinite_order
#check DiophantineNP.Curve37.quadratic_of_naive_error
#check DiophantineNP.Classes.tape_length_bounds
#check DiophantineNP.Blueprint.clearedNum_spec
#check DiophantineNP.Blueprint.packedExpr_evaluated
#print axioms DiophantineNP.Blueprint.packedScalarPrograms
#print axioms DiophantineNP.nativeVerifier_of_external
#print axioms DiophantineNP.classEquality_of_external

#check DiophantineNP.Curve37.canonicalHeight_zsmul
#check DiophantineNP.Curve37.cyclic_iff_rank_one
#check DiophantineNP.FiniteArithmeticGap.bitAt_eval
#check DiophantineNP.FiniteArithmeticGap.ProductTemplate.fullSum_correct
#check DiophantineNP.FiniteArithmeticGap.ProductTemplate.widthDescriptions
#check DiophantineNP.JMTableau.printed_half_mask_wrong_quotient
#check DiophantineNP.JMTableau.printed_half_mask_counterexample
#check DiophantineNP.JMTableau.halfConditions_iff
#check DiophantineNP.JMTableau.branchChecks_iff
#check DiophantineNP.JMTableau.shiftTrace_iff
#check DiophantineNP.Classes.Jones.Machine.regStep_affine_iff
#check DiophantineNP.Classes.Jones.Machine.readTape_iff
#check DiophantineNP.Classes.Jones.Machine.acceptingTrace_fields_iff
#check DiophantineNP.Classes.Jones.Machine.np_has_bounded_register_verifier
#check DiophantineNP.Classes.Jones.mem_D_of_normalForm
#check DiophantineNP.Classes.MachinePolynomial.evaluator
#check DiophantineNP.Classes.polynomialEvaluationInP_of_framedCircuitSimulation
#check DiophantineNP.nativeVerifier_of_rank_and_product
#check DiophantineNP.classEquality_of_rank_product_normalForm
#check DiophantineNP.classEquality_of_rank_product_compilers
#print axioms DiophantineNP.classEquality_of_rank_product_compilers

#check DiophantineNP.Classes.d_subset_np
#check DiophantineNP.Classes.np_subset_d_of_native
#check DiophantineNP.Classes.framedCircuitSimulation
#check DiophantineNP.JMTableau.TraceTable.run_short
#check DiophantineNP.Curve37.Kummer.class_number_one
#check DiophantineNP.Curve37.Kummer.image_eq_unit_mul_square
#check DiophantineNP.Curve37.rank_one
#check DiophantineNP.classEquality_of_native
#check DiophantineNP.nativeVerifier_of_product
#check DiophantineNP.classEquality_of_product
#print axioms DiophantineNP.Curve37.rank_one
#print axioms DiophantineNP.classEquality_of_product

#check DiophantineNP.Classes.Dcoord_eq_D
#check DiophantineNP.Classes.Dpower_eq_D
#check DiophantineNP.classEquality_powerCutoff_of_hab
#check DiophantineNP.ShortResidue.productResidue_spec
#check DiophantineNP.WidthPrimeResidue.description_correct
#check DiophantineNP.HAB.Form.translate_correct
#check DiophantineNP.HAB.productTemplate_of_imult
#check DiophantineNP.classEquality_of_hab
#print axioms DiophantineNP.classEquality_of_hab

#check DiophantineNP.HAB.toSource_correct
#check DiophantineNP.HAB.Form.onPrefix_correct
#check DiophantineNP.HABPairInterpretation.compile_correct
#check DiophantineNP.HABIndependentSum.formula_correct
#check DiophantineNP.HABIndependentSum.multiply_correct
#check DiophantineNP.HABProductBlocks.binaryProduct_spec
#check DiophantineNP.HABProductBlocks.padded_short_prime_collision
#check DiophantineNP.HABPolylogRange.block_covered
#check DiophantineNP.HABBoundedProduct.checkFactors_exact
#check DiophantineNP.HABPolynomialProduct.polynomial_value
#check DiophantineNP.HABPrimeBlocks.blockMember_by_rank
#check DiophantineNP.HABCRTCoefficients.coefficient_spec
#check DiophantineNP.HABCRTShift.matrix_product_bit
#check DiophantineNP.HABCRTRecovery.quotientField_of_square_le
#check DiophantineNP.HABCRTLeading.residueLt_correct
#check DiophantineNP.HABCRTExtend.formula_correct
#check DiophantineNP.HABCRTDot.readout_correct
#check DiophantineNP.HABGroupPower.prime_power_iff
#check DiophantineNP.HABPowerReduction.source_correct
#check DiophantineNP.HABDivisionGraph.formula_correct
#check DiophantineNP.HABGeometricDivision.division_in_FOM_of_imult
#check DiophantineNP.HAB.imult_iff_productTemplate
#check DiophantineNP.HAB.corollary63_iff_productTemplate
#print axioms DiophantineNP.HAB.corollary63_iff_productTemplate
#print axioms DiophantineNP.HABPolynomialProduct.polynomial_value
#print axioms DiophantineNP.HABPowerReduction.source_correct

#check DiophantineNP.HABCRTBitDecision.matrixBit_correct
#check DiophantineNP.HABPolylogProduct.formula_correct
#check DiophantineNP.HABShortProducts.ofPolylogProduct
#check DiophantineNP.HABModularArithmetic.prime_power
#check DiophantineNP.HABLargePrimeProduct.source_correct
#check DiophantineNP.HABWideBitDecision.localSpec
#check DiophantineNP.HABWideOutput.imult_of_local
#check DiophantineNP.HAB.imultInFOM
#check DiophantineNP.HAB.corollary63
#check DiophantineNP.nativeVerifier
#check DiophantineNP.classEquality
#check DiophantineNP.classEquality_powerCutoff
#print axioms DiophantineNP.HAB.imultInFOM
#print axioms DiophantineNP.HAB.corollary63
#print axioms DiophantineNP.nativeVerifier
#print axioms DiophantineNP.classEquality
#print axioms DiophantineNP.classEquality_powerCutoff

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut theoremCount : Nat := 0
  for (n, decl) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      if (`DiophantineNP).isPrefixOf env.header.moduleNames[idx]! then
        names := names.push n
        if decl matches .thmInfo _ then theoremCount := theoremCount + 1
  if theoremCount == 0 then throwError "The audit found no imported project theorems."
  let (_, result) := ((names.forM CollectAxioms.collect).run env).run {}
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let extra := result.axioms.filter (fun a => !allowed.contains a)
  unless extra.isEmpty do throwError "Unexpected dependencies in project declarations: {extra}"
  logInfo m!"Checked dependencies of {names.size} project declarations, including {theoremCount} theorem declarations. Axioms: {result.axioms}."
