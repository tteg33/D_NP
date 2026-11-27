import DiophantineNP.Statement
import DiophantineNP.Gates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Passing from a globally sound natural verifier to signed witnesses

Replace every natural witness by a sum of four integer squares. The polynomial
and its arity are chosen before any input width. One dummy slot also covers an
empty original witness type. -/

namespace DiophantineNP
open MvPolynomial
open scoped BigOperators

/-- Strong natural-witness version of Theorem 1.1, with arbitrary finite arity. -/
def StrongNatVerifier : Prop :=
  ∃ (W : Type) (_ : Fintype W) (C : ℕ) (P : Equation W),
    ∀ n a b : ℕ, 1 ≤ n → a < 2^n → b < 2^n →
      (BitIncl a b → ∃ w : W → ℕ, natCost w ≤ (n+2)^C ∧
        value P a b (fun i => (w i : ℤ)) = 0) ∧
      (∀ w : W → ℕ, value P a b (fun i => (w i : ℤ)) = 0 → BitIncl a b)

namespace FourSquare

def total {R : Type*} [CommRing R] (s : Fin 4 → R) : R :=
  s 0^2 + s 1^2 + s 2^2 + s 3^2

def decoded {W : Type} (v : W × Fin 4 → ℤ) (w : W) : ℕ :=
  (total (fun k => v (w,k))).toNat

theorem decoded_cast {W : Type} (v : W × Fin 4 → ℤ) (w : W) :
    (decoded v w : ℤ) = total (fun k => v (w,k)) := by
  apply Int.toNat_of_nonneg
  unfold total
  positivity

theorem pack {W : Type} (w : W → ℕ) :
    ∃ v : W × Fin 4 → ℤ, decoded v = w ∧ ∀ i, (v i).natAbs ≤ w i.1 := by
  choose a b c d h using fun i => Nat.sum_four_squares (w i)
  let v : W × Fin 4 → ℤ := fun (i,k) => match k.val with
    | 0 => a i | 1 => b i | 2 => c i | _ => d i
  refine ⟨v, ?_, ?_⟩
  · funext i
    have he : total (fun k => v (i,k)) = (w i : ℤ) := by
      change (a i : ℤ)^2 + (b i : ℤ)^2 + (c i : ℤ)^2 + (d i : ℤ)^2 = (w i : ℤ)
      exact_mod_cast h i
    simp [decoded, he]
  · intro ⟨i,k⟩
    have e := h i
    have a' := Nat.le_self_pow (by decide : 2 ≠ 0) (a i)
    have b' := Nat.le_self_pow (by decide : 2 ≠ 0) (b i)
    have c' := Nat.le_self_pow (by decide : 2 ≠ 0) (c i)
    have d' := Nat.le_self_pow (by decide : 2 ≠ 0) (d i)
    fin_cases k <;> dsimp [v] <;> omega

theorem bits_mono {a b : ℕ} (hab : a ≤ b) : bits a ≤ bits b := by
  by_cases ha : a = 0
  · simp [ha, bits]
  · have hb : b ≠ 0 := by omega
    exact Nat.add_le_add_right ((Nat.le_log2 hb).2 ((Nat.log2_self_le ha).trans hab)) 1

abbrev Slots (W : Type) := (W × Fin 4) ⊕ Unit

private noncomputable def substSlot {W : Type} [Fintype W] :
    Bool ⊕ W → MvPolynomial (Bool ⊕ Fin (Fintype.card (Slots W))) ℤ :=
  Sum.elim (fun b => X (.inl b)) (fun w => total (fun i =>
    X (.inr (Fintype.equivFin (Slots W) (.inl (w,i))))))

noncomputable def equation {W : Type} [Fintype W] (P : Equation W) :
    Equation (Fin (Fintype.card (Slots W))) := bind₁ substSlot P

private noncomputable def unpackFin {W : Type} [Fintype W]
    (v : Fin (Fintype.card (Slots W)) → ℤ) : W → ℕ :=
  decoded (fun wk => v (Fintype.equivFin (Slots W) (.inl wk)))

private noncomputable def extendFin {W : Type} [Fintype W] (v : W × Fin 4 → ℤ) :
    Fin (Fintype.card (Slots W)) → ℤ :=
  (Sum.elim v (fun _ => 0)) ∘ (Fintype.equivFin (Slots W)).symm

theorem value_equation {W : Type} [Fintype W] (P : Equation W) (a b : ℕ) (v) :
    value (equation P) a b v = value P a b (fun i => (unpackFin v i : ℤ)) := by
  unfold value equation
  rw [aeval_bind₁]
  apply congrArg (fun f : Bool ⊕ W → ℤ => aeval f P)
  funext s
  cases s with
  | inl b => simp [substSlot]
  | inr w => simp [substSlot, unpackFin, decoded_cast, total]

private theorem unpack_extend {W : Type} [Fintype W] (v : W × Fin 4 → ℤ) :
    unpackFin (extendFin v) = decoded v := by
  simp [unpackFin, extendFin]

private theorem honest_cost {W : Type} [Fintype W] (w : W → ℕ) (v : W × Fin 4 → ℤ)
    (h : ∀ i, (v i).natAbs ≤ w i.1) : intCost (extendFin v) ≤ 8*natCost w + 2 := by
  classical
  let u : Slots W → ℤ := Sum.elim v (fun _ => 0)
  have reindex : intCost (extendFin v) = ∑ j : Slots W, (bits (u j).natAbs+1) :=
    (Fintype.equivFin (Slots W)).symm.sum_comp (fun j => bits (u j).natAbs + 1)
  rw [reindex, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [u, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique, Int.natAbs_zero]
  change (∑ i : W, ∑ k : Fin 4, (bits (v (i,k)).natAbs + 1)) + 2 ≤ _
  apply Nat.add_le_add_right
  unfold natCost
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ∑ _k : Fin 4, (2*bits (w i)) := by
      apply Finset.sum_le_sum
      intro k _
      have hb : bits (v (i,k)).natAbs ≤ bits (w i) := bits_mono (h (i,k))
      have hbits : 1 ≤ bits (w i) := by unfold bits; omega
      omega
    _ = 8*bits (w i) := by simp; omega

end FourSquare

theorem strongNatVerifier_implies_nativeVerifier (h : StrongNatVerifier) : NativeVerifier := by
  obtain ⟨W, inst, C, P, spec⟩ := h
  letI : Fintype W := inst
  refine ⟨Fintype.card (FourSquare.Slots W), C+3, Fintype.card_pos, by omega,
    FourSquare.equation P, ?_⟩
  intro n a b hn ha hb
  obtain ⟨complete,sound⟩ := spec n a b hn ha hb
  constructor
  · intro yes
    obtain ⟨w, size, hw⟩ := complete yes
    obtain ⟨v, dec, bound⟩ := FourSquare.pack w
    refine ⟨FourSquare.extendFin v, (FourSquare.honest_cost w v bound).trans ?_, ?_⟩
    · rw [pow_add]
      have hX : 1 ≤ (n+2)^C := Nat.one_le_pow _ _ (by omega)
      have hX3 : 10 ≤ (n+2)^3 := by nlinarith [Nat.zero_le (n^2), Nat.zero_le (n^3)]
      have hlarge := Nat.mul_le_mul_left ((n+2)^C) hX3
      omega
    · rw [FourSquare.value_equation, FourSquare.unpack_extend, dec]
      exact hw
  · intro v hv
    rw [FourSquare.value_equation] at hv
    exact sound _ hv

end DiophantineNP
