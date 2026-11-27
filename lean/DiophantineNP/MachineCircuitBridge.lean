import DiophantineNP.MachinePolynomial

/-! # From simulation of binary arithmetic circuits to the machine-model obligation

The simulation interface accepts two fixed unsigned circuits and requires a total
TM2 implementation on all tapes. The bound permits polynomial simulation overhead
in the explicit bit-word work. -/
namespace DiophantineNP.Classes

open Turing Computability MachinePolynomial

/-- The number tested by a circuit machine is represented by its little-endian word. -/
def circuitDecision {r : ℕ} (a b : Circuit (Option (Fin r))) (s : List (Option Bool)) : Bool :=
  equalWords (a.word (fieldAt s)) (b.word (fieldAt s))

/-- Cost of parsing, reading the fixed fields, computing both words, and comparing them. -/
def circuitWork {r : ℕ} (a b : Circuit (Option (Fin r))) (s : List (Option Bool)) : ℕ :=
  let words := fieldAt (r := r) s
  (s.length+1)*(r+2) + a.work words + b.work words +
    ((a.word words).length + (b.word words).length + 1)

/-- A specific TM2 realization with polynomial overhead on every raw tape. -/
structure FramedCircuitMachine {r : ℕ} (a b : Circuit (Option (Fin r))) extends
    TM2ComputableAux tapeEncoding.Γ finEncodingBoolBool.Γ where
  overhead : Polynomial ℕ
  outputs : ∀ s : List (Option Bool),
    TM2OutputsInTime tm ((tapeEncoding.encode s).map inputAlphabet.invFun)
      (some ((finEncodingBoolBool.encode (circuitDecision a b s)).map outputAlphabet.invFun))
      (overhead.eval (circuitWork a b s))

/-- The low-level simulation obligation for fixed unsigned binary circuits. -/
def FramedCircuitSimulation : Prop :=
  ∀ (r : ℕ) (a b : Circuit (Option (Fin r))), Nonempty (FramedCircuitMachine a b)

private theorem monotone_time (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b h
  induction p using Polynomial.induction_on' with
  | monomial n c => simpa using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)
  | add p q hp hq => simpa using Nat.add_le_add hp hq

/-- An implementation of unsigned circuit simulation suffices to decide the native
integer polynomial equation on the framed input and certificate fields. -/
theorem polynomialEvaluationInP_of_framedCircuitSimulation
    (sim : FramedCircuitSimulation) : PolynomialEvaluationInP := by
  intro r P
  obtain ⟨a,b,p,hcost,hcorrect⟩ := evaluator P
  obtain ⟨M⟩ := sim r a b
  refine ⟨circuitDecision a b, ⟨{
    toTM2ComputableAux := M.toTM2ComputableAux
    time := M.overhead.comp p
    outputsFun := ?_ }⟩, ?_⟩
  · intro s
    let run := M.outputs s
    refine ⟨run.toEvalsTo, run.steps_le_m.trans ?_⟩
    change M.overhead.eval (circuitWork a b s) ≤ (M.overhead.comp p).eval s.length
    rw [Polynomial.eval_comp]
    exact monotone_time _ (hcost s)
  · intro x w
    have h := hcorrect x w
    change circuitDecision a b (tape x w) = true ↔ polyValue P x w = 0 at h
    cases hb : circuitDecision a b (tape x w) <;> simp_all

end DiophantineNP.Classes
