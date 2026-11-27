import DiophantineNP.MachineAddition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # A bit-word evaluator for every fixed multivariate integer polynomial

Multiplication uses binary shift-and-add. Negative coefficients are handled by
comparing two ordinary natural-number computations. The work recurrence charges
the adder's proven machine time, input copies, and a linear allowance for stack
reversals. It is a bit-word cost theorem. -/
namespace DiophantineNP.Classes.MachinePolynomial

open Computability MachineAddition
open scoped Polynomial

/-- Schoolbook multiplication on little-endian words, valid with high zeroes. -/
def multiply (x : List Bool) : List Bool → List Bool
  | [] => []
  | b :: bs =>
    let shifted := false :: multiply x bs
    if b then addWords x shifted false else shifted

theorem value_multiply (x y : List Bool) : MachineAddition.value (multiply x y) = MachineAddition.value x * MachineAddition.value y := by
  induction y with
  | nil => simp [multiply,MachineAddition.value]
  | cons b y ih => cases b <;> simp [multiply,MachineAddition.value,value_addWords,ih] <;> ring

theorem length_multiply (x y : List Bool) :
    (multiply x y).length ≤ x.length + 2*y.length := by
  induction y with
  | nil => simp [multiply]
  | cons b y ih =>
    cases b
    · simp only [multiply,Bool.false_eq_true,↓reduceIte,List.length_cons]; omega
    · have h := length_addWords x (false::multiply x y) false
      simp only [multiply,↓reduceIte,List.length_cons] at h ⊢
      omega

/-- Allow a full traversal of both words, in both directions, on every row of the
multiplication, even when the selected multiplier digit is zero. -/
def multiplyWork (x : List Bool) : List Bool → ℕ
  | [] => 1
  | _::bs => multiplyWork x bs + 4 * (x.length + (multiply x bs).length + 3)

theorem multiplyWork_bound (x y : List Bool) :
    multiplyWork x y ≤ (y.length+1) * (8*(x.length+y.length)+13) := by
  induction y with
  | nil => simp [multiplyWork]
  | cons b y ih =>
    have h := length_multiply x y
    simp only [multiplyWork, List.length_cons]
    nlinarith

/-- Compare binary words numerically without first converting them to unbounded integers. -/
def equalWords : List Bool → List Bool → Bool
  | [], t => t.all (!·)
  | h::t, [] => !(h || t.any id)
  | h::t, b::bs => (h == b) && equalWords t bs

private theorem all_zero_iff (t : List Bool) : t.all (!·) = true ↔ MachineAddition.value t = 0 := by
  induction t with
  | nil => simp [MachineAddition.value]
  | cons b t ih => cases b <;> simp_all [MachineAddition.value]

private theorem any_iff (t : List Bool) : t.any id = false ↔ MachineAddition.value t = 0 := by
  induction t with
  | nil => simp [MachineAddition.value]
  | cons b t ih => cases b <;> simp_all [MachineAddition.value]

theorem equalWords_exact (x y : List Bool) : equalWords x y = true ↔ MachineAddition.value x = MachineAddition.value y := by
  induction x generalizing y with
  | nil => rw [equalWords,all_zero_iff,MachineAddition.value,eq_comm]
  | cons a x ih =>
    cases y with
    | nil => cases a <;> simp [equalWords,MachineAddition.value]; simpa using any_iff x
    | cons b y => cases a <;> cases b <;> simp [equalWords,MachineAddition.value,ih] <;> omega

private theorem value_encodePos (p : PosNum) : MachineAddition.value (encodePosNum p) = (p : ℕ) := by
  induction p <;> simp_all [encodePosNum,MachineAddition.value,PosNum.cast_bit0,PosNum.cast_bit1] <;> omega

theorem value_encode (n : ℕ) : MachineAddition.value (encodeNat n) = n := by
  rw [← Num.to_of_nat n]
  generalize (n : Num) = a
  rw [encodeNat, Num.of_to_nat]
  cases a with
  | zero => rfl
  | pos a => exact value_encodePos a

/-- Fixed arithmetic expression over nonnegative integers. -/
inductive Circuit (I : Type) where
  | literal (n : ℕ)
  | input (i : I)
  | add (left right : Circuit I)
  | mul (left right : Circuit I)

def Circuit.word {I : Type} (w : I → List Bool) : Circuit I → List Bool
  | .literal n => encodeNat n
  | .input i => w i
  | .add a b => addWords (a.word w) (b.word w) false
  | .mul a b => multiply (a.word w) (b.word w)

/-- Work on the word data, with an explicit linear allowance for reading and copying. -/
def Circuit.work {I : Type} (w : I → List Bool) : Circuit I → ℕ
  | .literal n => (encodeNat n).length + 1
  | .input i => (w i).length + 1
  | .add a b => a.work w + b.work w + 4*((a.word w).length+(b.word w).length+2)
  | .mul a b => a.work w + b.work w + multiplyWork (a.word w) (b.word w)

theorem Circuit.polynomialBound {I : Type} (a : Circuit I) :
    ∃ p : Polynomial ℕ, ∀ (N : ℕ) (w : I → List Bool), (∀ i, (w i).length ≤ N) →
      (a.word w).length + a.work w ≤ p.eval N := by
  induction a with
  | literal n => refine ⟨Polynomial.C (2*(encodeNat n).length+1), ?_⟩; intro N w _; simp [word,work]; omega
  | input i => refine ⟨2*Polynomial.X+1, ?_⟩; intro N w h; simp [word,work]; have := h i; omega
  | add a b ha hb =>
    obtain ⟨p,hp⟩ := ha
    obtain ⟨q,hq⟩ := hb
    refine ⟨6*(p+q+2), ?_⟩
    intro N w hw
    have h₁ := hp N w hw
    have h₂ := hq N w hw
    have h₃ := length_addWords (a.word w) (b.word w) false
    simp [word,work]; omega
  | mul a b ha hb =>
    obtain ⟨p,hp⟩ := ha
    obtain ⟨q,hq⟩ := hb
    refine ⟨3*(p+q)+(q+1)*(8*(p+q)+13), ?_⟩
    intro N w hw
    have h₁ := hp N w hw
    have h₂ := hq N w hw
    have h₃ := length_multiply (a.word w) (b.word w)
    have h₄ := multiplyWork_bound (a.word w) (b.word w)
    have h₅ : ((b.word w).length+1)*(8*((a.word w).length+(b.word w).length)+13) ≤
        (q.eval N+1)*(8*(p.eval N+q.eval N)+13) :=
      Nat.mul_le_mul (by omega) (by omega)
    simp [word,work]; omega

/-- Compile signed coefficients by accumulating the positive and negative sides in
separate binary arithmetic circuits. The two circuits depend only on the polynomial. -/
theorem compile {I : Type} (P : MvPolynomial I ℤ) :
    ∃ a b : Circuit I, ∀ w : I → List Bool,
      (MachineAddition.value (a.word w) : ℤ) - MachineAddition.value (b.word w) =
        MvPolynomial.aeval (fun i => (MachineAddition.value (w i) : ℤ)) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨.literal c.toNat, .literal (-c).toNat, ?_⟩
    intro w
    simp [Circuit.word,value_encode]; omega
  | add _ _ hp hq =>
    obtain ⟨a,b,hab⟩ := hp
    obtain ⟨c,d,hcd⟩ := hq
    refine ⟨.add a c,.add b d,?_⟩
    intro w
    simp [Circuit.word,value_addWords]
    linarith [hab w,hcd w]
  | mul_X _ i h =>
    obtain ⟨a,b,hab⟩ := h
    refine ⟨.mul a (.input i), .mul b (.input i), ?_⟩
    intro w
    simp [Circuit.word,value_multiply]
    linear_combination (MachineAddition.value (w i) : ℤ) * hab w

/-- Split a tape into little-endian binary words. The empty suffix forms a final
empty field, and malformed tapes are assigned the same total parsing convention. -/
def splitWords : List (Option Bool) → List (List Bool)
  | [] => [[]]
  | none :: s => [] :: splitWords s
  | some b :: s => match splitWords s with
    | [] => [[b]]
    | w :: ws => (b::w) :: ws

private theorem split_prefix (bs : List Bool) (s : List (Option Bool)) :
    splitWords (bs.map some ++ none::s) = bs :: splitWords s := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [splitWords,ih]

private theorem split_fields (ns : List ℕ) :
    splitWords ((ns.map field).flatten) = ns.map encodeNat ++ [[]] := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.map_cons,List.flatten_cons,List.cons_append]
    rw [show field n = (encodeNat n).map (some : Bool → Option Bool) ++ [none] by rfl, List.append_assoc, List.singleton_append, split_prefix, ih]

private theorem split_tape {r : ℕ} (x : ℕ) (w : Fin r → ℕ) :
    splitWords (tape x w) = encodeNat x :: (List.ofFn (fun i => encodeNat (w i)) ++ [[]]) := by
  have h := split_fields (x::List.ofFn w)
  simpa [tape, List.map_ofFn,Function.comp_def] using h

private theorem length_field_le (s : List (Option Bool)) :
    ∀ w ∈ splitWords s, w.length ≤ s.length := by
  induction s with
  | nil => simp [splitWords]
  | cons c s ih =>
    cases c with
    | none => simp [splitWords]; intro w hw; have := ih w hw; omega
    | some b =>
      generalize hs : splitWords s = t at *
      cases t with
      | nil => simp [splitWords,hs]
      | cons w ws =>
        simp [splitWords,hs] at *
        exact ⟨ih.1, fun y hy => by have := ih.2 y hy; omega⟩

/-- Register lookup after framing. A missing field denotes zero. -/
def fieldAt {r : ℕ} (s : List (Option Bool)) : Option (Fin r) → List Bool
  | none => (splitWords s)[0]?.getD []
  | some i => (splitWords s)[i.val+1]?.getD []

private theorem fieldAt_tape {r : ℕ} (x : ℕ) (w : Fin r → ℕ) (i : Option (Fin r)) :
    fieldAt (tape x w) i = encodeNat (match i with | none => x | some j => w j) := by
  cases i with
  | none => simp [fieldAt,split_tape]
  | some j =>
    simp only [fieldAt,split_tape,List.getElem?_cons_succ]
    rw [List.getElem?_append_left (by simp), List.getElem?_eq_getElem (by simp)]
    simp

theorem length_fieldAt {r : ℕ} (s : List (Option Bool)) (i : Option (Fin r)) :
    (fieldAt s i).length ≤ s.length := by
  let idx : ℕ := i.elim 0 (fun j => j.val+1)
  have h : fieldAt s i = (splitWords s)[idx]?.getD [] := by cases i <;> rfl
  rw [h]
  cases he : (splitWords s)[idx]? with
  | none => simp
  | some w => exact length_field_le s w (List.mem_of_getElem? he)

/-- Total decision and work bound on arbitrary tapes. The cost counts reading
the input, field lookups with fixed arity, binary arithmetic, and the final digit
comparison. The equality is required only on the valid framed tuple. -/
theorem evaluator {r : ℕ} (P : MvPolynomial (Option (Fin r)) ℤ) :
    ∃ a b : Circuit (Option (Fin r)), ∃ p : Polynomial ℕ,
      (∀ s : List (Option Bool), let words := fieldAt (r := r) s
        (s.length+1)*(r+2) + a.work words + b.work words +
          ((a.word words).length + (b.word words).length + 1) ≤ p.eval s.length) ∧
      (∀ x w, let words := fieldAt (tape x w)
        equalWords (a.word words) (b.word words) = true ↔ polyValue P x w = 0) := by
  obtain ⟨a,b,hab⟩ := compile P
  obtain ⟨p,hp⟩ := a.polynomialBound
  obtain ⟨q,hq⟩ := b.polynomialBound
  refine ⟨a,b,(Polynomial.X+1)*Polynomial.C (r+2)+p+q+1,?_,?_⟩
  · intro s
    have h₁ := hp s.length (fieldAt (r := r) s) (length_fieldAt s)
    have h₂ := hq s.length (fieldAt (r := r) s) (length_fieldAt s)
    simp; omega
  · intro x w
    dsimp only
    rw [equalWords_exact]
    have h : (MachineAddition.value (a.word (fieldAt (tape x w))) : ℤ) -
        MachineAddition.value (b.word (fieldAt (tape x w))) = polyValue P x w := by
      rw [hab]
      unfold polyValue
      congr 2
      funext i
      cases i <;> simp [fieldAt_tape,value_encode]
    rw [← h, sub_eq_zero, Int.natCast_inj]

end DiophantineNP.Classes.MachinePolynomial
