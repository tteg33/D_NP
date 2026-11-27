import DiophantineNP.GeneralSumTemplate
import Mathlib.Data.Nat.ModEq

/-! # Binary multiplication from iterated addition

One input row is a shifted copy of the first word when the corresponding bit
of the second is set. Summing these rows computes the low bits of the product.
The fixed formula applies to any two definable words over the same input table.
-/
namespace DiophantineNP.HABMultiplyWords
open Counting WidthFormula FiniteArithmeticGap

private def atBit {k : ℕ} (p : Template 1) (i : Fin k) : Template k :=
  rewriteMatrix (fun r c => .entry r c) p (fun _ => i)

private theorem atBit_eval {U k : ℕ} (p : Template 1) (i : Fin k)
    (e : Fin U→Fin U→Bool) (env : Fin k→Fin U) :
    (atBit p i).eval e env = p.eval e (fun _ => env i) :=
  rewriteMatrix_eval _ e e (by intros; rfl) _ _ _

private def cell {k : ℕ} (a b : Template 1) (r c : Fin k) : Template k :=
  .conj (atBit b r) (.ex (.conj (.atom (.add r.succ 0 c.succ)) (atBit a 0)))

private def part (x y : ℕ) (i : ℕ) : ℕ := (y.testBit i).toNat * 2^i * x

private theorem cell_eval {U k : ℕ} (a b : Template 1) (r c : Fin k)
    (e : Fin U→Fin U→Bool) (env : Fin k→Fin U) (x y : ℕ)
    (ha : ∀ i : Fin U, a.eval e (fun _ => i) = x.testBit i.val)
    (hb : ∀ i : Fin U, b.eval e (fun _ => i) = y.testBit i.val) :
    (cell a b r c).eval e env = (part x y (env r).val).testBit (env c).val := by
  apply Bool.eq_iff_iff.mpr
  simp only [cell,Tconj_true,Tex_true,atBit_eval,ha,hb]
  simp only [Template.eval,Atom.eval,decide_eq_true_eq,
    Fin.cases_succ,Fin.cases_zero]
  cases h : y.testBit (env r).val with
  | false => simp [part,h]
  | true =>
    simp only [part,h,Bool.toNat_true,one_mul,Nat.testBit_two_pow_mul,
      Bool.and_eq_true,decide_eq_true_eq, true_and]
    constructor
    · rintro ⟨d,he,hd⟩
      exact ⟨by omega,by simpa [show (env c).val-(env r).val=d.val by omega] using hd⟩
    · rintro ⟨hle,hd⟩
      refine ⟨⟨_,(Nat.sub_le (env c).val (env r).val).trans_lt (env c).isLt⟩,by dsimp; omega,hd⟩

private theorem sum_part (x y n : ℕ) :
    Readout.prefixSum (part x y) n = Readout.word y.testBit n * x := by
  induction n with
  | zero => simp [Readout.prefixSum,Readout.word]
  | succ n ih =>
    change Readout.prefixSum _ n + _ = (Readout.word _ n + _) * x
    rw [ih,Nat.add_mul]
    rfl

private theorem word_mod (x n : ℕ) : Readout.word x.testBit n = x % 2^n := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<n
  · simp [Readout.word_testBit _ hj,Nat.testBit_mod_two_pow,hj]
  · have hle : 2^n≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow ((Readout.word_lt _ _).trans_le hle)]
    simp [Nat.testBit_mod_two_pow,hj]

private theorem sum_trim (f : ℕ→ℕ) (m n : ℕ) :
    Readout.prefixSum (fun i => f i%m) n ≡ Readout.prefixSum f n [MOD m] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact ih.add (Nat.mod_modEq _ _)

/-- The schoolbook partial product matrix can be supplied to any sum query. -/
def multiply (sum a b : Template 1) : Template 1 :=
  rewriteMatrix (fun r c => cell a b r c) sum id

/-- The only formula used as a subroutine is a sum; the arguments may stand
for any naturals, as only their low bits are observed. -/
theorem multiply_correct (sum a b : Template 1)
    (hsum : ∀ {U : ℕ} (f : ℕ→ℕ), (∀ r<U, f r<2^U) → ∀ j : Fin U,
      sum.eval (fun r c => (f r.val).testBit c.val) (fun _ => j) = (Readout.prefixSum f U).testBit j.val)
    {U : ℕ} (e : Fin U→Fin U→Bool) (x y : ℕ)
    (ha : ∀ i : Fin U, a.eval e (fun _ => i) = x.testBit i.val)
    (hb : ∀ i : Fin U, b.eval e (fun _ => i) = y.testBit i.val) (j : Fin U) :
    (multiply sum a b).eval e (fun _ => j) = (x*y).testBit j.val := by
  let f := fun i => part x y i % 2^U
  have tab {k : ℕ} (r c : Fin k) (env : Fin k→Fin U) :
      (cell a b r c).eval e env = (f (env r).val).testBit (env c).val := by
    simpa [f,Nat.testBit_mod_two_pow,(env c).isLt] using cell_eval a b r c e env x y ha hb
  rw [multiply,rewriteMatrix_eval _ e (fun r c => (f r.val).testBit c.val) (fun r c env => tab r c env)]
  change sum.eval (fun r c => (f r.val).testBit c.val) (fun _ => j) = _
  rw [hsum f (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos U))]
  have hm : Readout.prefixSum f U ≡ x*y [MOD 2^U] := by
    apply (sum_trim _ _ _).trans
    rw [sum_part,word_mod,Nat.mul_comm x y]
    exact (Nat.mod_modEq _ _).mul_right x
  have ht := congrArg (fun v : ℕ => v.testBit j.val) hm
  simpa [Nat.testBit_mod_two_pow,j.isLt] using ht

end DiophantineNP.HABMultiplyWords
