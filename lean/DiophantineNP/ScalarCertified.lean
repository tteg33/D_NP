import DiophantineNP.ScalarProgram
import DiophantineNP.ConstraintCost

/-! # Bounded integer constraint systems as scalar primitives

A fixed formula may store some primary integer registers of its own. A
polynomial total bit bound on those registers suffices to build a primitive
of `ScalarProgram`, including the auxiliary cost of every constraint gate.
-/

namespace DiophantineNP.ScalarProgram

open MvPolynomial Compiler

noncomputable section

private theorem single_cost {τ : Type} [Fintype τ] (w : τ → ℤ) (i : τ) :
    bits (w i).natAbs ≤ intCost w :=
  (Nat.le_succ _).trans (Finset.single_le_sum (f := fun j => bits (w j).natAbs+1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

/-- Convert a primary witness bound `K L^p` into the exact scalar-operation
interface. All primary and gate slots enter the operation's total bit cost. -/
def Operation.ofShortFormula {τ : Type} [Fintype τ] (f : ℤ → ℤ → ℤ)
    (F : Compiler.Formula (Option Bool ⊕ τ))
    (correct : ∀ a b y w, F.Holds (Sum.elim (opInputs a b y) w) → y = f a b)
    (short : ∃ K p : ℕ, ∀ a b, ∃ w : τ → ℤ,
      intCost w ≤ K*(signedBits a+signedBits b+signedBits (f a b)+2)^p ∧
      F.Holds (Sum.elim (opInputs a b (f a b)) w)) : Operation := by
  letI : Fintype F.Aux := Fintype.ofFinite _
  let P := rename (Equiv.sumAssoc (Option Bool) τ F.Aux) F.compile
  have heval (a b y : ℤ) (w : τ ⊕ F.Aux → ℤ) :
      eval (Sum.elim (opInputs a b y) w) P =
        eval (Sum.elim (Sum.elim (opInputs a b y) (w ∘ Sum.inl)) (w ∘ Sum.inr)) F.compile := by
    dsimp only [P]
    rw [eval_rename]
    congr 2
    funext i
    rcases i with (i|i)|i <;> rfl
  refine ⟨f, τ ⊕ F.Aux, inferInstance, P, ?_, ?_⟩
  · intro a b y w hw
    exact correct a b y (w ∘ Sum.inl) ((F.compile_exact _).1 ⟨w ∘ Sum.inr, (heval ..).symm.trans hw⟩)
  obtain ⟨A,hA⟩ := F.compile_linear_cost
  obtain ⟨K,p,hK⟩ := short
  let S := K + A*(K+2)
  refine ⟨p+1+S, fun a b => ?_⟩
  let L := signedBits a+signedBits b+signedBits (f a b)+2
  have hL : 2 ≤ L := by dsimp [L]; omega
  let M := L^(p+1)
  have hLM : L ≤ M := Nat.le_self_pow (Nat.succ_ne_zero p) _
  obtain ⟨w,hw,hf⟩ := hK a b
  have hcost : intCost w ≤ K*M :=
    hw.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_succ p)))
  let h := L+intCost w
  have hx (i : Option Bool ⊕ τ) : bits ((Sum.elim (opInputs a b (f a b)) w i).natAbs) ≤ h := by
    rcases i with (⟨⟩|⟨t⟩)|i
    · change bits (f a b).natAbs ≤ h; dsimp [h,L,signedBits]; omega
    · cases t <;> simp [opInputs,h,L,signedBits] <;> omega
    · exact (single_cost w i).trans (Nat.le_add_left _ _)
  obtain ⟨z,hz,hzcost⟩ := hA h _ hx hf
  refine ⟨Sum.elim w z, ?_, ?_⟩
  · have hz' : h+1 ≤ (K+2)*M := by dsimp [h]; rw [Nat.add_mul]; omega
    have hc : S ≤ L^S := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hL _)
    have hww : intCost (Sum.elim w z) = intCost w + intCost z := by simp [intCost,Fintype.sum_sum_type]
    rw [hww]
    change _ ≤ L^(p+1+S)
    calc
      _ ≤ K*M + A*((K+2)*M) := Nat.add_le_add hcost (hzcost.trans (Nat.mul_le_mul_left _ hz'))
      _ = M*S := by dsimp [S]; ring
      _ ≤ _ := by rw [pow_add]; exact Nat.mul_le_mul_left _ hc
  · rw [heval]; exact hz

end
end DiophantineNP.ScalarProgram
