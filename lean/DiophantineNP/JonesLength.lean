import DiophantineNP.JonesInterface
import DiophantineNP.EncodingFacts
import DiophantineNP.EvaluatorGrowth

/-! # A polynomial graph for the binary length used in equation (53)

Doubling a positive integer shifts its top bit up by one position. Taking
floor-logarithm after doubling also gives the desired value zero at zero.
The graph checks the length of every proposed witness, independently of
the bound on the total cost of an honest assignment.
-/
namespace DiophantineNP.Classes.Jones
open MvPolynomial ScalarProgram

theorem log2_double_eq_size (a : ℕ) : (2*a).log2 = a.size := by
  by_cases ha : a = 0
  · simp [ha, Nat.size_zero]
  · rw [Nat.log2_two_mul ha, ← encodeNat_length, encodeNat_length_eq_bits ha]
    rfl

private noncomputable def lengthEquation (op : Operation) : Equation op.W :=
  bind₁ (Sum.elim (fun i : Option Bool => match i with
    | none => X (.inl true)
    | some false => (2 : Equation op.W) * X (.inl false)
    | some true => 0) (fun j => X (.inr j))) op.polynomial

private theorem lengthEquation_value (op : Operation) (a l : ℕ) (w : op.W → ℤ) :
    value (lengthEquation op) a l w =
      eval (Sum.elim (opInputs (2*(a:ℤ)) 0 l) w) op.polynomial := by
  unfold lengthEquation value
  rw [aeval_bind₁]
  change eval _ _ = _
  apply congrArg (fun f => eval f op.polynomial)
  funext i
  rcases i with ( (_ | _ | _) | j) <;> simp [opInputs]

private theorem lengthCost (a : ℕ) :
    signedBits (2*(a:ℤ)) + signedBits 0 + signedBits (a.size : ℤ) + 2 ≤ (bits a+2)^3 := by
  have hl : a.size ≤ bits a := by
    by_cases ha : a=0
    · simp [ha,Nat.size_zero]
    · rw [← encodeNat_length,encodeNat_length_eq_bits ha]
  have ha : a.size.log2 ≤ a.size := Nat.log2_le_self _
  have db : (2*(a:ℤ)).natAbs = 2*a := by simp [Int.natAbs_mul]
  simp only [signedBits, db, Int.natAbs_natCast, bits, log2_double_eq_size, Int.natAbs_zero, Nat.log2_zero]
  unfold bits at hl
  nlinarith [Nat.zero_le (a.log2^2), Nat.zero_le (a.log2^3)]

/-- The paper's length convention, with unrestricted soundness and a
polynomial bound on the total bit length of the auxiliary witnesses. -/
theorem lengthGraph_of_curve (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) : LengthGraph := by
  classical
  obtain ⟨op,hop,_⟩ := Blueprint.exists_log2Operation hc hq
  have happ (a : ℕ) : op.apply (2*(a:ℤ)) 0 = (a.size:ℤ) := by
    rw [hop, show (2*(a:ℤ)).toNat = 2*a by omega, log2_double_eq_size]
  obtain ⟨C,hC⟩ := op.complete
  let S := op.W ⊕ op.W
  let E := Fintype.equivFin S
  let Q := splitEquation (lengthEquation op)
  let P := rename (Sum.map id E) Q
  have evaluate (a l : ℕ) (v : Fin (Fintype.card S) → ℕ) :
      value P a l (fun i => (v i:ℤ)) =
        eval (Sum.elim (opInputs (2*(a:ℤ)) 0 l) (decodeWitness (v ∘ E))) op.polynomial := by
    have hrename : value P a l (fun i => (v i:ℤ)) = value Q a l (fun i => (v (E i):ℤ)) := by
      unfold P value
      rw [aeval_rename]
      apply congrArg (fun f => aeval f Q)
      funext i
      cases i <;> rfl
    exact hrename.trans ((value_split (lengthEquation op) a l (v ∘ E)).trans (lengthEquation_value ..))
  refine ⟨_,3*C,P, ?_, ?_⟩
  · intro a l w hw
    rw [evaluate] at hw
    exact_mod_cast (op.sound _ _ _ _ hw).trans (happ a)
  · intro a
    obtain ⟨w,hcost,hzero⟩ := hC (2*(a:ℤ)) 0
    rw [happ] at hcost hzero
    let v := splitWitness w ∘ E.symm
    refine ⟨v, ?_, ?_⟩
    · have he : natCost v = natCost (splitWitness w) :=
        E.symm.sum_comp (fun i => bits (splitWitness w i))
      rw [he,cost_split]
      exact (hcost.trans (Nat.pow_le_pow_left (lengthCost a) C)).trans_eq (pow_mul _ 3 C).symm
    · rw [evaluate]
      have he : v ∘ E = splitWitness w := by funext i; simp [v]
      simpa only [he,decode_split] using hzero

end DiophantineNP.Classes.Jones
