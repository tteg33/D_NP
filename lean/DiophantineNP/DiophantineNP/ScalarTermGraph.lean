import DiophantineNP.ScalarProgram
import DiophantineNP.ScalarSystems

/-! # Two fixed integer terms give a short rational evaluation graph

The input slot `none` is the universe size and `some i` is parameter `i`.
Each term is fixed before the universe is chosen. Its polynomial and all
intermediate witnesses are provided by `ScalarProgram.Term`. A pair of terms
with polynomially bounded peak bit length yields a single `ShortScalarSystem`
for their rational quotient, with an explicit positive-denominator gate.
-/

namespace DiophantineNP.Packing

open MvPolynomial ScalarProgram

noncomputable section

/-- Inputs available to the numerator and denominator programs. -/
def termInputs {k U : ℕ} (t : Fin k → Fin U) : Option (Fin k) → ℤ
  | none => U
  | some i => (t i).val

abbrev IntegerTerm (k : ℕ) := ScalarProgram.Term (Option (Fin k))

/-- Rational value represented by the outputs of the two terms. -/
def termRatio {k : ℕ} (num den : IntegerTerm k) : Scalar k :=
  fun _ t => (num.run (termInputs t) : ℚ) / (den.run (termInputs t) : ℚ)

private def place {k r : ℕ} {τ : Type} (out : RatVar k) (slot : τ → Fin r) :
    Option (Option (Fin k)) ⊕ τ → RatVar k ⊕ Fin r
  | .inl none => .inl out
  | .inl (some none) => .inl (.inl .universeSize)
  | .inl (some (some i)) => .inl (.inl (.parameter i))
  | .inr j => .inr (slot j)

private def pairFormula {k r : ℕ} (num den : IntegerTerm k)
    (nslot : num.W → Fin r) (dslot : den.W → Fin r) : Compiler.Formula (RatVar k ⊕ Fin r) :=
  .both (.zero (rename (place (.inl .output) nslot) num.polynomial))
    (.both (.zero (rename (place (.inr ()) dslot) den.polynomial))
      (.nonnegative (X (.inl (.inr ())) - 1)))

private theorem eval_placed {k r U : ℕ} (e : IntegerTerm k) (t : Fin k → Fin U)
    (out : RatVar k) (slot : e.W → Fin r) (p q : ℤ) (w : Fin r → ℤ) :
    eval (Sum.elim (ratArguments t p q) w) (rename (place out slot) e.polynomial) =
      e.value (termInputs t) (ratArguments t p q out) (w ∘ slot) := by
  unfold Term.value
  rw [eval_rename]
  congr 2
  funext j
  rcases j with (_|(_|i))|j <;> rfl

private theorem pairFormula_iff {k r U : ℕ} (num den : IntegerTerm k)
    (nslot : num.W → Fin r) (dslot : den.W → Fin r) (t : Fin k → Fin U)
    (p q : ℤ) (w : Fin r → ℤ) :
    (pairFormula num den nslot dslot).Holds (Sum.elim (ratArguments t p q) w) ↔
    num.value (termInputs t) p (w ∘ nslot) = 0 ∧
    den.value (termInputs t) q (w ∘ dslot) = 0 ∧ 0 < q := by
  simp only [pairFormula,Compiler.Formula.Holds,eval_placed,map_sub,eval_X,map_one,Sum.elim_inl]
  change (_ ∧ _ ∧ 0 ≤ q-1) ↔ (_ ∧ _ ∧ 0<q)
  rw [show 0 ≤ q - 1 ↔ 0 < q by omega]
  rfl

private theorem peak_cost {B peak : ℕ} (hB : 2 ≤ B) {c : ℕ} (h : peak ≤ B^c) (a : ℕ) :
    (peak+3)^a ≤ B^((c+2)*a) := by
  have hp : 1 ≤ B^c := Nat.one_le_pow _ _ (by omega)
  have h4 : 4 ≤ B^2 := by nlinarith [Nat.pow_le_pow_left hB 2]
  have hsum : peak+3 ≤ B^(c+2) := by
    rw [pow_add]
    exact (by omega : peak+3 ≤ B^c*4).trans (Nat.mul_le_mul_left _ h4)
  exact (Nat.pow_le_pow_left hsum a).trans_eq (pow_mul B (c+2) a).symm

/-- A concrete finite-arity system, an honest *total* bit bound, and
unrestricted soundness for both output coordinates. -/
theorem scalarSystem_of_terms {k : ℕ} (num den : IntegerTerm k)
    (pos : ∀ U, 0<U → ∀ t : Fin k → Fin U, 0 < den.run (termInputs t))
    (small : ∃ c : ℕ, ∀ U, 0<U → ∀ t : Fin k → Fin U,
      max (num.peak (termInputs t)) (den.peak (termInputs t)) ≤ (1+U)^c) :
    ShortScalarSystem (termRatio num den) := by
  classical
  obtain ⟨a,ha⟩ := num.complete
  obtain ⟨b,hb⟩ := den.complete
  obtain ⟨c,hc⟩ := small
  let E := Fintype.equivFin (num.W ⊕ den.W)
  let z := (c+2)*(a+b+1)
  refine ⟨_, z+2, pairFormula num den (fun i => E (.inl i)) (fun j => E (.inr j)), ?_⟩
  intro U hU t
  let x := termInputs t
  let B := 1+U
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hp := hc U hU t
  obtain ⟨wn,hn,hen⟩ := ha x
  obtain ⟨wd,hd,hed⟩ := hb x
  have hpn : num.peak x ≤ B^c := (le_max_left ..).trans hp
  have hpd : den.peak x ≤ B^c := (le_max_right ..).trans hp
  have hcc : c ≤ z := by
    dsimp [z]; have := Nat.le_mul_of_pos_right (c+2) (show 0 < a+b+1 by omega); omega
  have hn' : intCost wn ≤ B^z := (hn.trans (peak_cost hB hpn a)).trans
    (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (by omega : a ≤ a+b+1)))
  have hd' : intCost wd ≤ B^z := (hd.trans (peak_cost hB hpd b)).trans
    (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (by omega : b ≤ a+b+1)))
  have hsize := Nat.pow_le_pow_right (n:=B) (by omega) hcc
  have hout := (num.result_le_peak x).trans (hpn.trans hsize)
  have hdout := (den.result_le_peak x).trans (hpd.trans hsize)
  constructor
  · let w := Sum.elim wn wd ∘ E.symm
    have hw : intCost w = intCost wn + intCost wd := by
      unfold intCost
      rw [show (∑ i, (bits (w i).natAbs+1)) =
        ∑ j : num.W ⊕ den.W, (bits ((Sum.elim wn wd j).natAbs)+1) from
          E.symm.sum_comp (fun j => bits ((Sum.elim wn wd j).natAbs)+1)]
      simp [Fintype.sum_sum_type]
    refine ⟨num.run x,den.run x,w,?_,(pairFormula_iff ..).2 ?_⟩
    · rw [hw]
      change _ + signedBits (num.run x) + signedBits (den.run x) ≤ B^(z+2)
      rw [pow_add]
      have h4 : 4 ≤ B^2 := by nlinarith [Nat.pow_le_pow_left hB 2]
      exact (by omega : _ ≤ B^z*4).trans (Nat.mul_le_mul_left _ h4)
    · simpa [w,Function.comp_def] using And.intro hen (And.intro hed (pos U hU t))
  · intro p q w hw
    obtain ⟨hn,hd,hp⟩ := (pairFormula_iff ..).1 hw
    exact ⟨hp, by rw [num.sound _ _ _ hn, den.sound _ _ _ hd]; rfl⟩

/-- An evaluator specification sufficient for packing. Its witnesses are
fixed numerator and denominator programs for each finite-arithmetic formula. -/
def FixedTermEvaluators : Prop :=
  ∀ (k : ℕ) (φ : Counting.Formula (k+1)), ∃ num den : IntegerTerm k,
    (∀ U, 0<U → ∀ t : Fin k → Fin U, 0 < den.run (termInputs t)) ∧
    (∃ c : ℕ, ∀ U, 0<U → ∀ t : Fin k → Fin U,
      max (num.peak (termInputs t)) (den.peak (termInputs t)) ≤ (1+U)^c) ∧
    RoundsTo (termRatio num den) φ

theorem packing_of_fixed_term_evaluators (h : FixedTermEvaluators) : PackingClaim :=
  packing_of_scalar_systems fun k φ => by
    obtain ⟨num,den,pos,small,correct⟩ := h k φ
    exact ⟨_,scalarSystem_of_terms num den pos small,correct⟩

end
end DiophantineNP.Packing
