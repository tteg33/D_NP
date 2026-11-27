import DiophantineNP.JonesReduction
import DiophantineNP.JonesRegisterVerifier
import DiophantineNP.MachineCircuitBridge

/-! # The two machine compilation steps in the class equality -/
namespace DiophantineNP
open Classes Classes.Jones.Machine

/-- The bounded accepting traces of one fixed register verifier, with its input
framing, true-output configuration, certificate budget, time and space bounds. -/
def boundedTraceLanguage (r : ℕ) (q : Polynomial ℕ) (M : VerifierMachine)
    (T S : Polynomial ℕ) : Classes.Language :=
  {x | ∃ (w : Fin r → ℕ) (n : ℕ), natCost w ≤ q.eval (bits x) ∧
    n ≤ T.eval (bits x) ∧ AcceptingRegisterTrace M (tape x w) n (S.eval (bits x))}

/-- Compile bounded register traces into the exact polynomial-and-mask form of (53). -/
def RegisterTraceNormalForm : Prop :=
  ∀ r q M T S, Classes.Jones.NormalForm (boundedTraceLanguage r q M T S)

/-- The passage from native NP verifiers to bounded register traces is checked. -/
theorem jonesSource_of_registerTraceNormalForm (compile : RegisterTraceNormalForm) :
    JonesSourceDirection := by
  intro L hL
  obtain ⟨r,q,M,T,S,h⟩ := np_has_bounded_register_verifier hL
  have eqL : L = boundedTraceLanguage r q M T S := Set.ext h
  exact eqL ▸ compile r q M T S

/-- A route to the class equality with only arithmetic and machine-compilation inputs. -/
theorem classEquality_of_rank_product_compilers
    (rank : Module.rank ℤ Curve37.E.Point ≤ 1)
    (product : FiniteArithmeticGap.ProductTemplate)
    (traceCompiler : RegisterTraceNormalForm)
    (circuitCompiler : Classes.FramedCircuitSimulation) : Classes.D = Classes.NP :=
  classEquality_of_rank_product_normalForm rank product
    (jonesSource_of_registerTraceNormalForm traceCompiler)
    (Classes.polynomialEvaluationInP_of_framedCircuitSimulation circuitCompiler)

end DiophantineNP
