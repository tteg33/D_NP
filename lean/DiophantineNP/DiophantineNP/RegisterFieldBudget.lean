import DiophantineNP.BoundedClass
import DiophantineNP.JonesRegisterVerifier

/-! # Certifying the original NP verifier's numerical budgets

Both the certificate budget and the machine's numerical clock bound use the
input bit length. The length gate includes the charge of one bit for zero.
-/
namespace DiophantineNP.Classes.Jones.Machine
open BoundedRelation MvPolynomial
noncomputable section

private def polyAt {σ : Type} (p : Polynomial ℕ) (i : σ) : MvPolynomial σ ℤ :=
  p.eval₂ (Nat.castRingHom _) (X i)

private theorem polyAt_eval {σ : Type} (p : Polynomial ℕ) (i : σ) (z : Env σ) :
    eval (ints z) (polyAt p i) = Int.ofNat (p.eval (z i)) := by
  induction p using Polynomial.induction_on' with
  | monomial n c => simp [polyAt,ints]
  | add p q hp hq => simpa [polyAt,Polynomial.eval₂_add] using congrArg₂ (·+·) hp hq

private theorem shortLe {σ : Type} (p q : MvPolynomial σ ℤ) :
    Short (fun z => eval (ints z) p ≤ eval (ints z) q) :=
  (Short.formula (.nonnegative (q-p))).congr (fun z => by simp [Compiler.Formula.Holds])

private theorem bits_le_succ (n : ℕ) : bits n ≤ n+1 := Nat.succ_le_succ (Nat.log2_le_self n)

/-- Impose the budget for the caller-supplied certificate fields before using
the machine's Boolean acceptance. This includes all zero-valued witnesses. -/
theorem certCut_short_of_length
    (length : ∀ {τ : Type} (a l : τ), Short (fun z : Env τ => z l = bits (z a))) {σ : Type}
    (x : σ) {r : ℕ} (w : Fin r → σ) (q : Polynomial ℕ) :
    Short (fun z : Env σ => natCost (z ∘ w) ≤ q.eval (bits (z x))) := by
  let a : Option (Fin r) → σ := Option.elim' x w
  let S : Relation (σ ⊕ Option (Fin r)) := fun z =>
    (∀ i, z (.inr i) = bits (z (.inl (a i)))) ∧ (∑ j : Fin r, z (.inr (some j))) ≤ q.eval (z (.inr none))
  have hs : Short S := by
    dsimp only [S]
    refine Short.and ?_ ?_
    · exact Short.all (fun i => length (Sum.inl (a i)) (Sum.inr i))
    · let P : MvPolynomial (σ ⊕ Option (Fin r)) ℤ := ∑ j : Fin r, X (.inr (some j))
      apply (shortLe P (polyAt q (.inr none))).congr
      intro z
      simp [P,polyAt_eval,ints,← Nat.cast_sum]
  apply Short.exists_of S hs (Polynomial.X+1)
  · rintro z u ⟨h,e⟩
    change ∀ i, u i = bits (z (a i)) at h
    change (∑ i, u (some i)) ≤ q.eval (u none) at e
    simpa only [h,natCost,Function.comp_apply,a,Option.elim'] using e
  · intro H z hz he
    refine ⟨fun i => bits (z (a i)),fun i => ?_,fun _ => rfl,he⟩
    simpa using (bits_le_succ _).trans (Nat.succ_le_succ (hz (a i)))

theorem certCut_short (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) {σ : Type}
    (x : σ) {r : ℕ} (w : Fin r → σ) (q : Polynomial ℕ) :
    Short (fun z : Env σ => natCost (z ∘ w) ≤ q.eval (bits (z x))) :=
  certCut_short_of_length (Short.binaryLength hc hq) x w q

/-- Numerical time or space bounded by a polynomial of the input bit length. -/
theorem bitPolyBound_short (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) {σ : Type}
    (x y : σ) (q : Polynomial ℕ) : Short (fun z : Env σ => z y ≤ q.eval (bits (z x))) := by
  let S : Relation (σ ⊕ Unit) := fun z => z (.inr ())=bits (z (.inl x)) ∧ z (.inl y) ≤ q.eval (z (.inr ()))
  have hs : Short S := by
    dsimp only [S]
    refine Short.and (Short.binaryLength hc hq (Sum.inl x) (Sum.inr ())) ?_
    exact (shortLe (X (.inl y)) (polyAt q (.inr ()))).congr (fun z => by simp [polyAt_eval,ints])
  apply Short.exists_of S hs (Polynomial.X+1)
  · rintro z u ⟨h,e⟩; change u ()=bits (z x) at h; change z y ≤ q.eval (u ()) at e; rwa [h] at e
  · intro H z hz he
    refine ⟨fun _ => bits (z x),fun _ => ?_,rfl,he⟩
    simpa using (bits_le_succ _).trans (Nat.succ_le_succ (hz x))

end
end DiophantineNP.Classes.Jones.Machine
