import DiophantineNP.Statement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Fixed scalar computations with short local certificates

Each operation has its own fixed polynomial graph. A term combining these
operations has one fixed polynomial, even when an operation takes a variable
exponent. Honest costs are bounded in the maximum length of *all* semantic
intermediate values. This formulation keeps the size obligation for an
evaluator that makes a recursive call at a larger radix.
-/
namespace DiophantineNP.ScalarProgram
open MvPolynomial

def signedBits (z : ℤ) := bits z.natAbs+1

def opInputs (a b y : ℤ) : Option Bool → ℤ
  | none => y
  | some t => if t then b else a

structure Operation where
  apply : ℤ → ℤ → ℤ
  W : Type
  fin : Fintype W
  polynomial : MvPolynomial (Option Bool ⊕ W) ℤ
  sound : ∀ a b y w, eval (Sum.elim (opInputs a b y) w) polynomial = 0 → y = apply a b
  complete : ∃ C : ℕ, ∀ a b, ∃ w : W → ℤ,
    @intCost W fin w ≤ (signedBits a + signedBits b + signedBits (apply a b) + 2)^C ∧
    eval (Sum.elim (opInputs a b (apply a b)) w) polynomial = 0

attribute [instance] Operation.fin

/-- Every fixed bivariate integer polynomial is a scalar operation. -/
noncomputable def ofPolynomial (p : MvPolynomial Bool ℤ) : Operation where
  apply a b := eval (fun t : Bool => if t then b else a) p
  W := Empty
  fin := inferInstance
  polynomial := X (Sum.inl none) - rename (fun b => Sum.inl (some b)) p
  sound a b y w h := by
    simpa [eval_rename, Function.comp_def, opInputs, sub_eq_zero] using h
  complete := by
    refine ⟨0, fun a b => ⟨Empty.elim, by simp [intCost], ?_⟩⟩
    simp [eval_rename, Function.comp_def, opInputs]

inductive Term (I : Type) where
  | input (i : I)
  | literal (z : ℤ)
  | app (op : Operation) (left right : Term I)

namespace Term
variable {I : Type}

def run (x : I → ℤ) : Term I → ℤ
  | .input i => x i
  | .literal z => z
  | .app op l r => op.apply (run x l) (run x r)

def peak (x : I → ℤ) : Term I → ℕ
  | .input i => signedBits (x i)
  | .literal z => signedBits z
  | .app op l r => max (signedBits (op.apply (run x l) (run x r))) (max (peak x l) (peak x r))

lemma result_le_peak (e : Term I) (x : I → ℤ) : signedBits (e.run x) ≤ e.peak x := by
  cases e <;> simp [run,peak]

def W : Term I → Type
  | .input _ | .literal _ => Empty
  | .app op l r => Bool ⊕ (l.W ⊕ (r.W ⊕ op.W))

instance termFin : (e : Term I) → Fintype e.W
  | .input _ | .literal _ => inferInstanceAs (Fintype Empty)
  | .app op l r => by
    letI := termFin l
    letI := termFin r
    exact inferInstanceAs (Fintype (Bool ⊕ (l.W ⊕ (r.W ⊕ op.W))))

private def arg (x : I → ℤ) (y : ℤ) : Option I → ℤ
  | none => y
  | some i => x i

private def childSlot {W A : Type} (tag : Bool) (place : A → W) :
    Option I ⊕ A → Option I ⊕ (Bool ⊕ W)
  | .inl none => .inr (.inl tag)
  | .inl (some i) => .inl (some i)
  | .inr a => .inr (.inr (place a))

private def primitiveSlot {L R W : Type} :
    Option Bool ⊕ W → Option I ⊕ (Bool ⊕ (L ⊕ (R ⊕ W)))
  | .inl none => .inl none
  | .inl (some b) => .inr (.inl b)
  | .inr w => .inr (.inr (.inr (.inr w)))

noncomputable def polynomial : (e : Term I) → MvPolynomial (Option I ⊕ e.W) ℤ
  | .input i => X (.inl none) - X (.inl (some i))
  | .literal z => X (.inl none) - C z
  | .app op l r =>
    (rename (childSlot false Sum.inl) l.polynomial)^2 +
    (rename (childSlot true (Sum.inr ∘ Sum.inl)) r.polynomial)^2 +
    (rename primitiveSlot op.polynomial)^2

noncomputable def value (e : Term I) (x : I → ℤ) (y : ℤ) (v : e.W → ℤ) :=
  eval (Sum.elim (arg x y) v) e.polynomial

private theorem app_zero (op : Operation) (l r : Term I) (x : I → ℤ) (y : ℤ)
    (w : (app op l r).W → ℤ) : (app op l r).value x y w=0 ↔
    l.value x (w (.inl false)) (fun i => w (.inr (.inl i)))=0 ∧
    r.value x (w (.inl true)) (fun i => w (.inr (.inr (.inl i))))=0 ∧
    eval (Sum.elim (opInputs (w (.inl false)) (w (.inl true)) y)
      (fun i => w (.inr (.inr (.inr i))))) op.polynomial=0 := by
  unfold value
  simp only [polynomial, map_add, map_pow]
  simp only [W] at w ⊢
  rw [eval_rename,eval_rename,eval_rename]
  have fix (A : Type) (tag : Bool) (place : A → l.W ⊕ (r.W ⊕ op.W)) :
      (Sum.elim (arg x y) w) ∘ (childSlot tag place) =
        Sum.elim (arg x (w (.inl tag))) (fun i => w (.inr (place i))) := by
    funext i; rcases i with (i|i); cases i <;> rfl; rfl
  rw [fix,fix]
  have opfix : (Sum.elim (arg x y) w) ∘ primitiveSlot =
      Sum.elim (opInputs (w (.inl false)) (w (.inl true)) y) (fun i => w (.inr (.inr (.inr i)))) := by
    funext i; rcases i with (i|i)
    · cases i with
      | none => rfl
      | some b => cases b <;> rfl
    · rfl
  rw [opfix]
  rw [add_eq_zero_iff_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _),
    add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)]
  simp [and_assoc]

/-- Soundness is independent of the sizes of all guessed intermediates. -/
theorem sound (e : Term I) (x : I → ℤ) (y : ℤ) (w : e.W → ℤ)
    (h : e.value x y w=0) : y=e.run x := by
  induction e generalizing y with
  | input i => simpa [value,polynomial,run,arg,sub_eq_zero] using h
  | literal z => simpa [value,polynomial,run,arg,sub_eq_zero] using h
  | app op l r il ir =>
    obtain ⟨hl,hr,hop⟩ := (app_zero ..).mp h
    have z := op.sound _ _ _ _ hop
    rw [il _ _ hl, ir _ _ hr] at z
    exact z

/-- A polynomial bound on the peak intermediate bit length suffices for the
entire finite trace and all auxiliary witnesses introduced by composition. -/
theorem complete (e : Term I) : ∃ c : ℕ, ∀ x, ∃ w : e.W → ℤ,
    intCost w ≤ (e.peak x+3)^c ∧ e.value x (e.run x) w=0 := by
  induction e with
  | input i =>
    exact ⟨0,fun x => ⟨Empty.elim, by change @intCost Empty _ _ ≤ _; simp [intCost], by simp [value,polynomial,run,arg]⟩⟩
  | literal z =>
    exact ⟨0,fun x => ⟨Empty.elim, by change @intCost Empty _ _ ≤ _; simp [intCost], by simp [value,polynomial,run,arg]⟩⟩
  | app op l r hl hr =>
    obtain ⟨a,ha⟩ := hl
    obtain ⟨b,hb⟩ := hr
    obtain ⟨c,hc⟩ := op.complete
    let k := max 1 (max a (max b (2*c)))
    refine ⟨k+2,?_⟩
    intro x
    obtain ⟨u,hu,eu⟩ := ha x
    obtain ⟨v,hv,ev⟩ := hb x
    obtain ⟨z,hz,ez⟩ := hc (l.run x) (r.run x)
    let h := (app op l r).peak x
    let B := h+3
    have hB : 3≤B := by dsimp [B]; omega
    have hlp : l.peak x ≤ h := (le_max_left ..).trans (le_max_right ..)
    have hrp : r.peak x ≤ h := (le_max_right ..).trans (le_max_right ..)
    have lp := (l.result_le_peak x).trans hlp
    have rp := (r.result_le_peak x).trans hrp
    have hp : signedBits (op.apply (l.run x) (r.run x)) ≤ h := le_max_left .. 
    have up : intCost u ≤ B^k := hu.trans <|
      (Nat.pow_le_pow_left (by dsimp [B]; omega) a).trans (Nat.pow_le_pow_right (by omega) (by dsimp [k]; omega))
    have vp : intCost v ≤ B^k := hv.trans <|
      (Nat.pow_le_pow_left (by dsimp [B]; omega) b).trans (Nat.pow_le_pow_right (by omega) (by dsimp [k]; omega))
    have zp : intCost z ≤ B^k := by
      have hs : signedBits (l.run x)+signedBits (r.run x)+signedBits (op.apply (l.run x) (r.run x))+2 ≤ B^2 := by
        have hh := Nat.mul_le_mul_left B hB
        dsimp only [B] at hh ⊢
        nlinarith
      exact hz.trans ((Nat.pow_le_pow_left hs c).trans ((pow_mul B 2 c).symm.le.trans
        (Nat.pow_le_pow_right (by omega) (by dsimp [k]; omega))))
    let wf : Bool → ℤ := fun t => if t then r.run x else l.run x
    let w : (app op l r).W → ℤ := Sum.elim wf (Sum.elim u (Sum.elim v z))
    refine ⟨w,?_,(app_zero ..).2 ⟨eu,ev,ez⟩⟩
    have split : intCost w = signedBits (l.run x)+signedBits (r.run x)+intCost u+intCost v+intCost z := by
      change intCost (Sum.elim wf (Sum.elim u (Sum.elim v z))) = _
      simp [intCost,wf,signedBits,Fintype.sum_sum_type, Nat.add_comm,Nat.add_assoc,Nat.add_left_comm]
    have hlarge : B≤B^k := by simpa using (Nat.pow_le_pow_right (n:=B) (by omega) (le_max_left 1 _))
    have h5 : 5≤B^2 := (by decide : 5≤3^2).trans (Nat.pow_le_pow_left hB _)
    have hle : h ≤ B^k := (show h≤B by dsimp [B]; omega).trans hlarge
    rw [split]
    change _ ≤ B^(k+2)
    calc
      _ ≤ B^k*5 := by omega
      _ ≤ _ := by rw [pow_add]; exact Nat.mul_le_mul_left _ h5

end Term
end DiophantineNP.ScalarProgram
