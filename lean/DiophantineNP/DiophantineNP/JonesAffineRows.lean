import DiophantineNP.JonesVariants
import DiophantineNP.JMTableau

/-! # Affine equation lists for the finite branches of a TM2 macrostep -/
namespace DiophantineNP.Classes.Jones.Machine
open Turing JMTableau
open scoped Classical
attribute [local instance] FinTM2.kFin

abbrev Equation (m : ℕ) := Affine m × Affine m

def linear {m : ℕ} (i : Fin m) (c d : ℕ) : Affine m :=
  ⟨d,fun j => if i=j then c else 0⟩

@[simp] theorem linear_eval {m : ℕ} (i : Fin m) (c d : ℕ) (x : Fin m → ℕ) :
    (linear i c d).eval x = d + c * x i := by
  simp [linear,Affine.eval,ite_mul]

def Satisfies {m : ℕ} (P : List (Equation m)) (x : Fin m → ℕ) : Prop :=
  ∀ p ∈ P, p.1.eval x = p.2.eval x

private noncomputable def writes (tm : FinTM2) {m : ℕ} (after : tm.K → Fin m) (rhs : tm.K → Affine m) :
    List (Equation m) := Finset.univ.toList.map fun k => (linear (after k) 1 0,rhs k)

private theorem writes_iff (tm : FinTM2) {m} (after : tm.K → Fin m) (rhs : tm.K → Affine m) (x) :
    Satisfies (writes tm after rhs) x ↔ ∀ k, x (after k) = (rhs k).eval x := by
  simp [Satisfies,writes]

/-- Compile one constant branch operation into a fixed finite list of affine
equalities on the old cells, the new cells, and one quotient cell. -/
noncomputable def opEquations (tm : FinTM2) {m : ℕ} (before after : tm.K → Fin m) (quot : Fin m) :
    Op tm → List (Equation m)
  | .push k d => writes tm after (fun j => if j=k then linear (before k) (radix tm) d else linear (before j) 1 0)
  | .read k d drop => (linear (before k) 1 0,linear quot (radix tm) d.val) ::
      writes tm after (fun j => if drop ∧ j=k then linear quot 1 0 else linear (before j) 1 0)

/-- The explicit quotient cell has the same role as the existential witness
of `Op.Holds`. Unused quotient cells of push operations may be set to zero. -/
def Op.HoldsWith (tm : FinTM2) : Op tm → File tm → File tm → ℕ → Prop
  | .push k d, R,T,_ => T=Function.update R k (d+radix tm * R k)
  | .read k d drop, R,T,q => R k = radix tm*q+d.val ∧ T=(if drop then Function.update R k q else R)

theorem holdsWith_iff (tm : FinTM2) (op : Op tm) (R T : File tm) :
    (∃ q, op.HoldsWith tm R T q) ↔ op.Holds tm R T := by
  cases op <;> simp [Op.HoldsWith,Op.Holds]

theorem opEquations_exact (tm : FinTM2) {m : ℕ} (before after : tm.K → Fin m) (quot : Fin m)
    (op : Op tm) (x : Fin m → ℕ) :
    Satisfies (opEquations tm before after quot op) x ↔
      op.HoldsWith tm (x ∘ before) (x ∘ after) (x quot) := by
  cases op with
  | push k d =>
    rw [opEquations,writes_iff]
    simp only [Op.HoldsWith,funext_iff,Function.comp_apply]
    apply forall_congr'; intro j
    by_cases e : j=k
    · subst j; simp
    · simp [e,Function.update_of_ne]
  | read k d drop =>
    have cons (p : Equation m) (P : List (Equation m)) :
        Satisfies (p :: P) x ↔ p.1.eval x = p.2.eval x ∧ Satisfies P x := by simp [Satisfies]
    rw [opEquations,cons,writes_iff]
    simp only [linear_eval,Op.HoldsWith,Function.comp_apply,one_mul,zero_add]
    rw [Nat.add_comm d.val]
    apply and_congr_right; intro _
    cases drop <;> simp only [Bool.false_eq_true,ite_false,ite_true,false_and,true_and,
      linear_eval,one_mul,zero_add,funext_iff,Function.comp_apply]
    apply forall_congr'; intro j
    by_cases e : j=k
    · subst j; simp
    · simp [e,Function.update_of_ne]

end DiophantineNP.Classes.Jones.Machine
