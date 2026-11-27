import DiophantineNP.MachineCircuitPair
import DiophantineNP.MachineStackAddGate
import DiophantineNP.MachineStackMultiply
import DiophantineNP.MachineFrameAdapter
import DiophantineNP.NativeComplexity
import DiophantineNP.RegisterTableReduction
import DiophantineNP.TraceChecker
import DiophantineNP.JonesReduction

/-! # The two machine inclusions and their composition -/
namespace DiophantineNP
open Classes

theorem Classes.framedCircuitSimulation : FramedCircuitSimulation := by
  classical
  intro r a b
  let W := StackModel.Allocation.scratch a b
  have gates : StackModel.WordGates W :=
    ⟨StackModel.gateLiteral W,StackModel.gateCopy W,StackModel.gateAdd W,StackModel.gateMul W⟩
  obtain ⟨p,time,space,run⟩ := StackModel.Allocation.pairProgram a b gates
  exact StackModel.framed_of_wordProgram a b _ p _ _ time space run

/-- On the project's framed binary tapes every fixed integer polynomial has
a total polynomial-time equality test, including on malformed raw input. -/
theorem Classes.polynomialEvaluationInP : PolynomialEvaluationInP :=
  polynomialEvaluationInP_of_framedCircuitSimulation framedCircuitSimulation

theorem Classes.d_subset_np : D ⊆ NP := D_subset_NP polynomialEvaluationInP

/-- No external Jones–Matiyasevich implication enters this direction. The
proof uses as many native bit masks as the fixed trace machine needs. -/
theorem np_subset_d_of_native_curve (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (native : NativeVerifier) : Classes.NP ⊆ Classes.D :=
  Classes.Jones.Machine.np_subset_d_of_table_compiler hc hq (fun T => T.run_short native)

/-- A single fixed, globally sound, short-witness native bit-inclusion verifier
suffices for the equality, independently of the draft's construction of that verifier. -/
theorem classEquality_of_native (native : NativeVerifier) : Classes.D = Classes.NP :=
  Set.Subset.antisymm Classes.d_subset_np (Classes.np_subset_d_of_native native)

/-- The curve's rank upper bound and one fixed iterated-product formula suffice
for the full equality of the numerical complexity classes. -/
theorem classEquality_of_rank_and_product (rank : Module.rank ℤ Curve37.E.Point ≤ 1)
    (product : FiniteArithmeticGap.ProductTemplate) : Classes.D = Classes.NP :=
  classEquality_of_native (nativeVerifier_of_rank_and_product rank product)

end DiophantineNP
