import DiophantineNP.JonesRegisterInput
import DiophantineNP.JonesAffineRows
import DiophantineNP.TraceTable
import Mathlib.Tactic.FinCases

/-! # Fixed affine transition table for binary input fields

The field reader consumes one low-order binary digit and one symbol of the
initial stack. Its three equations select the low bit, match the alphabet
digit and enforce a strictly positive current input by a nonnegative slack.
-/
namespace DiophantineNP.Classes.Jones.Machine
open Turing Computability JMTableau
noncomputable section

/-- Numeric code of a symbol of the framed input alphabet. -/
def inputDigit (M : VerifierMachine) (b : Option Bool) :=
  digit M.tm ⟨M.tm.k₀,M.inputAlphabet.symm b⟩

def fieldBranch (M : VerifierMachine) (i : Fin 2) : List (Equation 5) :=
  [(linear 0 1 0,linear 2 2 i.val),
   (linear 1 1 0,linear 3 (radix M.tm) (inputDigit M (some (i.val=1)))),
   (linear 0 1 0,linear 4 1 1)]

/-- Five column words are sufficient: old value, old stack, new value,
new stack, and the predecessor of the old nonzero value. -/
def fieldTable (M : VerifierMachine) : TraceTable where
  m := 5
  b := 2
  k := 2
  P := fieldBranch M
  old := ![0,1]
  new := ![2,3]

def pairRegs (x y : ℕ) : Fin 2 → ℕ := ![x,y]

private theorem branch_iff (M : VerifierMachine) (i : Fin 2) (x : Fin 5 → ℕ) :
    Satisfies (fieldBranch M i) x ↔
      x 0 = i.val+2*x 2 ∧ x 1 = inputDigit M (some (i.val=1)) + radix M.tm * x 3 ∧
      x 0 = 1+x 4 := by
  simp [fieldBranch,Satisfies]

private theorem row_iff (M : VerifierMachine) (x : Fin 5 → ℕ) :
    (∃ i, Satisfies (fieldBranch M i) x) ↔ ReadBit M (x 0,x 1) (x 2,x 3) ∧ x 0=1+x 4 := by
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨a,b,c⟩ := (branch_iff M i x).mp hi
    refine ⟨⟨by change 0 < x 0; omega,decide (i.val=1),?_,b⟩,c⟩
    fin_cases i <;> simp_all [Nat.add_comm]
  · rintro ⟨⟨_,b,ha,hb⟩,hc⟩
    cases b with
    | false => exact ⟨0,(branch_iff ..).mpr ⟨by simpa [Nat.add_comm] using ha,hb,hc⟩⟩
    | true => exact ⟨1,(branch_iff ..).mpr ⟨by simpa [Nat.add_comm] using ha,hb,hc⟩⟩

/-- Soundness imposes no a priori bit budget on the external endpoints. -/
theorem fieldTable_sound (M : VerifierMachine) {n v : ℕ} {a b : ℕ×ℕ}
    (h : (fieldTable M).Run n v (pairRegs a.1 a.2) (pairRegs b.1 b.2)) : ReaderRows M n a b := by
  obtain ⟨R,_,hB,hs⟩ := h
  obtain ⟨v₀,h₀,t₀,o₀,n₀⟩ := hs (0 : Fin 2)
  obtain ⟨v₁,h₁,t₁,o₁,n₁⟩ := hs (1 : Fin 2)
  refine ⟨fun j => (v₀ j,v₁ j),Prod.ext h₀ h₁,Prod.ext t₀ t₁,?_⟩
  intro j
  have h := ((row_iff M (fun i => R i j)).mp (hB j)).1
  change ReadBit M (v₀ j.castSucc,v₁ j.castSucc) (v₀ j.succ,v₁ j.succ)
  rw [o₀,o₁,n₀,n₁]; exact h

/-- A lane that fits the two initial registers fits every local value,
including the positivity slack, independently of the number of steps. -/
theorem fieldTable_complete (M : VerifierMachine) {n v : ℕ} {a b : ℕ×ℕ}
    (h : ReaderRows M n a b) (ha : a.1 < 2^v) (hb : a.2 < 2^v) :
    (fieldTable M).Run n v (pairRegs a.1 a.2) (pairRegs b.1 b.2) := by
  obtain ⟨row,h0,hn,hs⟩ := h
  let R (i : Fin 5) (t : Fin n) := (![ (row t.castSucc).1, (row t.castSucc).2,
    (row t.succ).1,(row t.succ).2,(row t.castSucc).1-1] : Fin 5 → ℕ) i
  have hbound (j : Fin (n+1)) := readerRows_bound M row hs j
  simp only [h0] at hbound
  refine ⟨R,?_,?_,?_⟩
  · intro i t
    have ho := hbound t.castSucc
    have hi := hbound t.succ
    change Fin 5 at i
    fin_cases i <;> dsimp [R] <;> omega
  · intro t
    apply (row_iff M (fun i => R i t)).mpr
    refine ⟨hs t,?_⟩
    have h := (hs t).1
    change (row t.castSucc).1 = 1+((row t.castSucc).1-1); omega
  · intro j
    change Fin 2 at j
    fin_cases j
    · exact ⟨fun k => (row k).1,congrArg Prod.fst h0,congrArg Prod.fst hn,fun _ => rfl,fun _ => rfl⟩
    · exact ⟨fun k => (row k).2,congrArg Prod.snd h0,congrArg Prod.snd hn,fun _ => rfl,fun _ => rfl⟩

/-- Fixed-table characterization of a single field, for arbitrary ending
tail and including the zero field with no bit transitions. -/
theorem fieldTable_iff (M : VerifierMachine) (n v x start tail : ℕ)
    (hx : x < 2^v) (hs : start < 2^v) :
    (fieldTable M).Run n v (pairRegs x start) (pairRegs 0 (inputDigit M none+radix M.tm*tail)) ↔
      n=x.size ∧ start=prefixCode M (field x) tail := by
  rw [← fieldRows_iff M n x start tail]
  exact ⟨fun h => fieldTable_sound M (a:=(x,start)) (b:=(0,_)) h,
    fun h => fieldTable_complete M h hx hs⟩

end
end DiophantineNP.Classes.Jones.Machine
