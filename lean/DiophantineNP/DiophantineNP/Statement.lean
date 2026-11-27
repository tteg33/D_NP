import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

/-!
# The native-bit theorem and its bounded Diophantine consequence

The proposition `NativeVerifier` is the target of Theorem 1.1 of the manuscript.
`nativeVerifier_implies_boundedD` derives bounded Diophantine membership from this
specification. `DiophantineNP.nativeVerifier` in `HABVerified.lean` proves it.
-/

namespace DiophantineNP

open MvPolynomial

/-- Ones of the first native integer are also ones of the second. -/
def BitIncl (a b : ℕ) : Prop := ∀ i, a.testBit i = true → b.testBit i = true

theorem bitIncl_iff_and (a b : ℕ) : BitIncl a b ↔ a &&& b = a := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases ha : a.testBit i with
    | false => rfl
    | true => simp [h i ha]
  · intro h i ha
    have ht := congrArg (fun x : ℕ => x.testBit i) h
    simp [Nat.testBit_and, ha] at ht
    exact ht

/-- Magnitude length in base two, including one digit for zero. -/
def bits (x : ℕ) : ℕ := x.log2 + 1

def width (a b : ℕ) : ℕ := max (bits a) (bits b)

def intCost {W : Type} [Fintype W] (w : W → ℤ) : ℕ :=
  ∑ i, (bits (w i).natAbs + 1)

def natCost {W : Type} [Fintype W] (w : W → ℕ) : ℕ := ∑ i, bits (w i)

abbrev Equation (W : Type) := MvPolynomial (Bool ⊕ W) ℤ

/-- The input slots are false for a and true for b. -/
noncomputable def value {W : Type} (P : Equation W) (a b : ℕ) (w : W → ℤ) : ℤ :=
  aeval (Sum.elim (fun t : Bool => if t then (b : ℤ) else (a : ℤ)) w) P

/-- One fixed polynomial for all widths, with unrestricted soundness. -/
def NativeVerifier : Prop :=
  ∃ r C : ℕ, 0 < r ∧ 0 < C ∧ ∃ P : Equation (Fin r),
    ∀ n a b : ℕ, 1 ≤ n → a < 2 ^ n → b < 2 ^ n →
      (BitIncl a b → ∃ w, intCost w ≤ (n + 2) ^ C ∧ value P a b w = 0) ∧
      (∀ w, value P a b w = 0 → BitIncl a b)

/-- Bounded Diophantine membership for a binary numerical relation. The size
cutoff is taken at the actual input width so false inputs may have longer zeros.
An arbitrary fixed finite type of witness slots is equivalent to a fixed arity. -/
def InBoundedD (R : ℕ → ℕ → Prop) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (C : ℕ) (P : Equation W), 0 < C ∧
    ∀ a b, R a b ↔ ∃ w : W → ℕ,
      natCost w ≤ (width a b + 2) ^ C ∧ value P a b (fun i => (w i : ℤ)) = 0

/-- Substitute a difference of natural-witness slots for each signed slot. -/
noncomputable def splitEquation {W : Type} (P : Equation W) : Equation (W ⊕ W) :=
  bind₁ (Sum.elim (fun t => X (.inl t))
           (fun i => X (R := ℤ) (Sum.inr (Sum.inl i) : Bool ⊕ (W ⊕ W)) - X (R := ℤ) (Sum.inr (Sum.inr i) : Bool ⊕ (W ⊕ W)))) P

def splitWitness {W : Type} (w : W → ℤ) : W ⊕ W → ℕ :=
  Sum.elim (fun i => (w i).toNat) (fun i => (-(w i)).toNat)

def decodeWitness {W : Type} (u : W ⊕ W → ℕ) (i : W) : ℤ :=
  (u (.inl i) : ℤ) - (u (.inr i) : ℤ)

theorem decode_split {W : Type} (w : W → ℤ) : decodeWitness (splitWitness w) = w := by
  funext i
  simp only [decodeWitness, splitWitness, Sum.elim_inl, Sum.elim_inr]
  omega

/-- The zero part uses exactly the extra bit charged for the sign. -/
theorem cost_split {W : Type} [Fintype W] (w : W → ℤ) :
    natCost (splitWitness w) = intCost w := by
  unfold natCost intCost
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change bits (w i).toNat + bits (-(w i)).toNat = bits (w i).natAbs + 1
  cases h : w i with
  | ofNat k => simp [bits, Int.toNat_neg_natCast]
  | negSucc k => simp [bits]; omega

theorem value_split {W : Type} (P : Equation W) (a b : ℕ) (u : W ⊕ W → ℕ) :
    value (splitEquation P) a b (fun i => (u i : ℤ)) =
      value P a b (decodeWitness u) := by
  unfold value splitEquation
  rw [aeval_bind₁]
  apply congrArg (fun f : Bool ⊕ W → ℤ => aeval f P)
  funext i
  cases i <;> simp [decodeWitness]

theorem width_spec (a b : ℕ) :
    1 ≤ width a b ∧ a < 2 ^ width a b ∧ b < 2 ^ width a b := by
  refine ⟨?_, ?_, ?_⟩
  · unfold width bits
    omega
  · exact Nat.lt_log2_self.trans_le
      (Nat.pow_le_pow_right (by decide) (le_max_left (bits a) (bits b)))
  · exact Nat.lt_log2_self.trans_le
      (Nat.pow_le_pow_right (by decide) (le_max_right (bits a) (bits b)))

/-- Corollary 1.2 up to the published Jones–Matiyasevich criterion. -/
theorem nativeVerifier_implies_boundedD (h : NativeVerifier) : InBoundedD BitIncl := by
  obtain ⟨r, C, _, hC, P, hP⟩ := h
  refine ⟨Fin r ⊕ Fin r, inferInstance, C, splitEquation P, hC, ?_⟩
  intro a b
  obtain ⟨hn, ha, hb⟩ := width_spec a b
  obtain ⟨complete, sound⟩ := hP (width a b) a b hn ha hb
  constructor
  · intro yes
    obtain ⟨w, short, zero⟩ := complete yes
    refine ⟨splitWitness w, (cost_split w).le.trans short, ?_⟩
    rw [value_split, decode_split, zero]
  · rintro ⟨u, _, zero⟩
    rw [value_split] at zero
    exact sound _ zero

end DiophantineNP
