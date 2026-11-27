import DiophantineNP.Classes
import Mathlib.Data.Num.Lemmas
import Mathlib.Algebra.BigOperators.Fin

/-! # Framing and certificate lengths in the machine model -/
namespace DiophantineNP.Classes
open Computability
open scoped BigOperators

private theorem pos_length (n : PosNum) : (encodePosNum n).length = n.natSize := by
  induction n <;> simp_all [encodePosNum, PosNum.natSize]

theorem encodeNat_length (n : ℕ) : (encodeNat n).length = n.size := by
  have h (p : Num) : (encodeNum p).length = p.natSize := by
    cases p with
    | zero => rfl
    | pos p => exact pos_length p
  rw [encodeNat, h, Num.natSize_to_nat, Num.to_of_nat]

/-- Mathlib uses the empty binary word for zero. The manuscript charges one bit. -/
theorem encodeNat_length_eq_bits {n : ℕ} (hn : n ≠ 0) : (encodeNat n).length = bits n := by
  rw [encodeNat_length]
  exact Nat.le_antisymm (Nat.size_le.mpr Nat.lt_log2_self)
    (Nat.succ_le_of_lt (Nat.lt_size.mpr (Nat.log2_self_le hn)))

theorem field_length (n : ℕ) : bits n ≤ (field n).length ∧ (field n).length ≤ bits n + 1 := by
  change bits n ≤ ((encodeNat n).map some ++ [none]).length ∧
    ((encodeNat n).map some ++ [none]).length ≤ bits n+1
  by_cases h : n=0
  · subst n; simp [encodeNat_length, bits, Nat.size_zero]
  · simp [encodeNat_length_eq_bits h]

private theorem fields_length {r : ℕ} (w : Fin r → ℕ) :
    ((List.ofFn (fun i => field (w i))).flatten).length = ∑ i, (field (w i)).length := by
  induction r with
  | zero => simp
  | succ r ih => simp [List.ofFn_succ, Fin.sum_univ_succ, ih]

/-- Framing each field costs at most one symbol beyond its charged bit length. -/
theorem tape_length_bounds {r : ℕ} (x : ℕ) (w : Fin r → ℕ) :
    bits x + natCost w ≤ (tape x w).length ∧
    (tape x w).length ≤ bits x + natCost w + (r+1) := by
  rw [tape, List.length_append, fields_length, natCost]
  refine ⟨Nat.add_le_add (field_length x).1 (Finset.sum_le_sum (fun i _ => (field_length (w i)).1)), ?_⟩
  have h := Nat.add_le_add (field_length x).2 (Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => (field_length (w i)).2))
  simpa [Finset.sum_add_distrib, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- A high sentinel preserves every input bit, including zeroes, when a binary
certificate is stored in one natural-number register. -/
def wordSentinel : List Bool → PosNum
  | [] => .one
  | false :: s => .bit0 (wordSentinel s)
  | true :: s => .bit1 (wordSentinel s)

theorem encode_wordSentinel (s : List Bool) : encodeNat (wordSentinel s : ℕ) = s ++ [true] := by
  rw [encodeNat, PosNum.of_to_nat]
  change encodePosNum (wordSentinel s) = s ++ [true]
  induction s with
  | nil => rfl
  | cons b tail ih => cases b <;> simp [wordSentinel, encodePosNum, ih]

theorem bits_wordSentinel (s : List Bool) : bits (wordSentinel s : ℕ) = s.length + 1 := by
  have nn := (wordSentinel s).to_nat_pos.ne'
  rw [← encodeNat_length_eq_bits nn, encode_wordSentinel]
  simp

end DiophantineNP.Classes
