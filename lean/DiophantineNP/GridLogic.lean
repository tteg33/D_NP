import DiophantineNP.ConcreteGrid
import DiophantineNP.Atomic

/-! # From the paper's geometric observations to the logical induction

The labels and windows determine the actual arithmetic, guard and quantifier
gates. This file instantiates their uniform constants, including the base-two
precision needed when the full-grid errors are summed. -/

namespace DiophantineNP.ConcreteGrid

open Counting
noncomputable section

def precision (U : ℕ) : ℕ :=
  100*((2*radius U+1) + 10*((size U).log2+1) + 20)

def epsilon (U : ℕ) : ℝ := ((2:ℝ)^(precision U))⁻¹
def delta (U : ℕ) : ℝ := 1/(64*(size U:ℝ)^4)

theorem numeric {U : ℕ} :
    (2:ℝ) ≤ radius U ∧ (U:ℝ) ≤ radius U ∧
    512*((radius U:ℝ)+1)^3 ≤ size U ∧ 32*((radius U:ℝ)+1) ≤ size U := by
  have hB : 2 ≤ radius U := by rw [radius]; exact le_max_left _ _
  have hu : U ≤ radius U := by rw [radius]; exact le_max_right _ _
  have g : 512*((radius U:ℝ)+1)^3 ≤ size U := by
    rw [size]
    exact_mod_cast Grid.period_large (radius U)
  have h : (1:ℝ) ≤ radius U+1 := by linarith [Nat.cast_nonneg (α := ℝ) (radius U)]
  have hp := pow_le_pow_right₀ h (show 1 ≤ 3 by decide)
  rw [pow_one] at hp
  exact ⟨by exact_mod_cast hB, by exact_mod_cast hu, g, by linarith⟩

theorem error_small (U : ℕ) :
    0 ≤ error U ∧ error U ≤ 1/8 ∧ (2*(radius U:ℝ)+3)*error U ≤ 1/8 := by
  let B : ℝ := radius U
  let M : ℝ := size U
  obtain ⟨hb, _, h₁,h₂⟩ := numeric (U := U)
  change 2 ≤ B at hb
  change 512*(B+1)^3 ≤ M at h₁
  change 32*(B+1) ≤ M at h₂
  have hM : 1 ≤ M := by linarith
  have hp : 0 < M := by linarith
  have hb3 : 32*B^3 ≤ M/2 := by nlinarith [sq_nonneg B, show 0 ≤ B^3 by positivity]
  have hb4 : B ≤ M^3/2 := by
    have a := pow_le_pow_right₀ hM (by decide : 1 ≤ 3)
    rw [pow_one] at a
    linarith
  have h₃ : 32*B^3/M^2 ≤ 1/(2*M) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hb3 hp.le]
  have h₄ : B/M^4 ≤ 1/(2*M) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hb4 hp.le]
  have he : error U ≤ 1/M := by
    unfold error
    change 32*B^3/M^2+B/M^4 ≤ _
    have : 1/(2*M) + 1/(2*M) = 1/M := by field_simp; norm_num
    linarith
  refine ⟨by unfold error; positivity, ?_, ?_⟩
  · exact he.trans ((div_le_iff₀ hp).mpr (by linarith))
  · change (2*B+3)*error U ≤ 1/8
    calc
      _ ≤ (2*B+3)*(1/M) := mul_le_mul_of_nonneg_left he (by linarith)
      _ ≤ 1/8 := by rw [← mul_div_assoc, mul_one, div_le_iff₀ hp]; linarith

private theorem size_large (U : ℕ) : (2:ℝ) ≤ size U := by
  obtain ⟨hb,_,_,h⟩ := numeric (U := U)
  linarith

private theorem precision_bounds (U : ℕ) :
    0 ≤ epsilon U ∧ epsilon U ≤ 1/16 ∧ (size U:ℝ)*epsilon U ≤ 1/8 := by
  have hlog : size U < 2^((size U).log2+1) := Nat.lt_log2_self
  have hpow : 8*size U ≤ 2^((size U).log2+1+3) := by rw [pow_add]; omega
  have hprec : (size U).log2+1+3 ≤ precision U := by unfold precision; omega
  have tot : 8*size U ≤ 2^(precision U) :=
    hpow.trans (Nat.pow_le_pow_right (by decide) hprec)
  have small : (16:ℝ) ≤ (2:ℝ)^(precision U) := by
    have four : 4 ≤ precision U := by unfold precision; omega
    exact_mod_cast (Nat.pow_le_pow_right (n := 2) (by decide) four)
  have real_tot : 8*(size U:ℝ) ≤ (2:ℝ)^(precision U) := by exact_mod_cast tot
  unfold epsilon
  constructor
  · positivity
  constructor
  · rw [← one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  · rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith

theorem delta_bounds (U : ℕ) :
    delta U ≤ 1/16 ∧ delta U ≤ (1/4)/((size U:ℝ)+U+2) ∧ delta U ≤ 1/(size U:ℝ)^2 := by
  have hM := size_large U
  have hM₀ : (0:ℝ) < size U := by linarith
  have hpow : (size U:ℝ) ≤ (size U:ℝ)^4 := by
    simpa using pow_le_pow_right₀ (a := (size U:ℝ)) (by linarith) (by decide : 1 ≤ 4)
  have hs := pow_le_pow_right₀ (a := (size U:ℝ)) (by linarith) (by decide : 2 ≤ 4)
  obtain ⟨_,hU,_,h₂⟩ := numeric (U := U)
  unfold delta
  refine ⟨?_,?_,?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith

def gate (U : ℕ) : Counting.Threshold (epsilon U) (delta U) :=
  Counting.draftThreshold (size U) (precision U) ((size U).log2+1)
    (by have h := size_large U; exact_mod_cast (by linarith : (0:ℝ) < size U))

variable {U : ℕ} {I O : Type} [Fintype I] [Fintype O]

def guardArgument (U : ℕ) (x : ℝ) : ℝ :=
  ((U:ℝ)-1-x+1/2)/(8*(size U:ℝ)^4)

private theorem guard_bound {x : ℝ} (h : |x| ≤ size U) : |guardArgument U x| ≤ 1 := by
  have hM := size_large U
  have hM₀ : (0:ℝ) < size U := by linarith
  have hpow : (size U:ℝ) ≤ (size U:ℝ)^4 := by
    simpa using pow_le_pow_right₀ (a := (size U:ℝ)) (by linarith) (by decide : 1 ≤ 4)
  obtain ⟨_, hU, _, h₂⟩ := numeric (U := U)
  obtain ⟨_,_⟩ := abs_le.mp h
  unfold guardArgument
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) U]
  · apply (div_le_iff₀ (by positivity)).mpr
    linarith

private theorem guard_accurate {x : ℝ} {j : ℕ} (h : |x| ≤ size U)
    (close : |x-(j:ℝ)| ≤ error U) :
    |(gate U).H (guardArgument U x) - bit (decide (j < U))| ≤ epsilon U := by
  let v : ℤ := (U:ℤ)-1-j
  have hM := size_large U
  have hv : (v:ℝ) = (U:ℝ)-1-j := by simp [v]
  have near : |((U:ℝ)-1-x) - (v:ℝ)| ≤ 1/8 := by
    rw [hv, show ((U:ℝ)-1-x) - ((U:ℝ)-1-j) = (j:ℝ)-x by ring, abs_sub_comm]
    exact close.trans (error_small U).2.1
  obtain ⟨lo,hi⟩ := abs_le.mp (guard_bound h)
  have hd : (0 ≤ v) ↔ j < U := by unfold v; omega
  simpa only [hd] using le_arg_error (gate U) (by linarith : (0:ℝ) < size U) v near lo hi

/-- All hypotheses of guarded structural induction instantiated from one
reindexed grid of geometric observations with the paper's stated constants. -/
def Observed.tests (obs : Observed U I O) : GridTests U I O (epsilon U) (delta U) where
  threshold := gate U
  eps_nonneg := (precision_bounds _).1
  eps_small := (precision_bounds _).2.1
  delta_small := (delta_bounds _).1
  sum_error := by simpa [gridSize, obs.card_eq] using (precision_bounds U).2.2
  count_margin := by simpa [gridSize, obs.card_eq] using (delta_bounds U).2.1
  window := fun z => (gate U).H (obs.Y z)
  window_unit := fun z => (gate U).unit _ (abs_le.mp (obs.y_bound z)).1 (abs_le.mp (obs.y_bound z)).2
  window_selected := fun z => (gate U).high _ ((delta_bounds U).2.2.trans (obs.y_selected z))
    (abs_le.mp (obs.y_bound _)).2
  window_off := fun o => (gate U).low _ (abs_le.mp (obs.y_bound _)).1
    ((obs.y_off o).trans (neg_le_neg (delta_bounds U).2.2))
  guard := fun z => (gate U).H (guardArgument U (obs.x z))
  guard_unit := fun z => (gate U).unit _ (abs_le.mp (guard_bound (obs.x_bound z))).1
    (abs_le.mp (guard_bound (obs.x_bound z))).2
  guard_valid := fun i b => by
    have h := guard_accurate (obs.x_bound _) (obs.close_valid i b)
    simpa only [i.isLt, decide_true, bit, ↓reduceIte] using h
  guard_invalid := fun i => by
    obtain ⟨j,hj,_,close⟩ := obs.close_invalid i
    have h := guard_accurate (obs.x_bound _) close
    simpa only [Nat.not_lt.mpr hj, decide_false, bit, Bool.false_eq_true, ↓reduceIte] using h
  atom := fun a z => (gate U).H (atomArgument a (obs.x ∘ z) (size U))
  atom_unit := fun a z => Counting.atom_unit a _ _ (size_large U) (fun i => obs.x_bound (z i))
  atom_error := fun a u z h => by
    obtain ⟨_,hU,_,_⟩ := numeric (U := U)
    obtain ⟨h₀,h₁,small⟩ := error_small U
    refine Counting.atom_error a u _ _ (size_large U) (fun i => obs.x_bound (z i))
      (Nat.cast_nonneg _) h₀ (by linarith) small (fun i => ?_) (fun i => ?_)
    · exact (by exact_mod_cast (u i).isLt.le : (((u i).val:ℕ):ℝ) ≤ U).trans hU
    · obtain ⟨b,e⟩ := h i
      simpa only [Function.comp_apply, e] using obs.close_valid (u i) b

/-- An operand can be an exact integer parameter or a sampled root. -/
abbrev Operand (U : ℕ) := Fin U ⊕ LabelGrid U (Invalid U) (Outside U)

def scalar {U : ℕ} : Operand U → ℝ := Sum.elim (fun i => (i.val:ℝ)) (observed U).x

private def Represents {U : ℕ} (v : Operand U) (i : Fin U) : Prop :=
  v = .inl i ∨ ∃ b : Bool, v = .inr (.inl (.inl (i,b)))

private theorem scalar_bound (v : Operand U) : |scalar v| ≤ size U := by
  rcases v with i | z
  · obtain ⟨_,hU,_,hm⟩ := numeric (U := U)
    have hi : (i.val:ℝ) ≤ U := by exact_mod_cast i.isLt.le
    change |(i.val:ℝ)| ≤ _
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    linarith [Nat.cast_nonneg (α := ℝ) (radius U)]
  · exact (observed U).x_bound z

private theorem scalar_close {v : Operand U} {i : Fin U} (h : Represents v i) :
    |scalar v - (i.val:ℝ)| ≤ error U := by
  rcases h with rfl | ⟨b,rfl⟩
  · simpa [scalar] using (error_small U).1
  · exact (observed U).close_valid i b

/-- Concrete real-value semantics of every arithmetic/majority formula.
Free numerical parameters enter as exact real integers. At a quantifier
only the bound slot is fed through the reindexed finite cyclic grid. -/
def sampleEval {U : ℕ} : {k : ℕ} → Formula k → (Fin k → Operand U) → ℝ
  | _, .atom a, z => (gate U).H (atomArgument a (scalar ∘ z) (size U))
  | _, .neg φ, z => 1 - sampleEval φ z
  | _, .conj φ ψ, z => andGate (gate U) (sampleEval φ z) (sampleEval ψ z)
  | _, .disj φ ψ, z => orGate (gate U) (sampleEval φ z) (sampleEval ψ z)
  | _, .ex φ, z => quantify (observed U).tests 0 (fun v => sampleEval φ (Fin.cases (.inr v) z))
  | _, .maj φ, z => quantify (observed U).tests (U/2) (fun v => sampleEval φ (Fin.cases (.inr v) z))

theorem sampleEval_unit {k : ℕ} (φ : Formula k) : ∀ z : Fin k → Operand U,
    UnitValue (sampleEval φ z) := by
  induction φ with
  | atom a => exact fun z => atom_unit a _ _ (size_large U) (fun i => scalar_bound (z i))
  | neg φ ih =>
    intro z
    obtain ⟨l,r⟩ := ih z
    change 0 ≤ 1 - _ ∧ 1 - _ ≤ 1
    constructor <;> linarith
  | conj φ ψ ih jh => exact fun z => andGate_unit _ (ih z) (jh z)
  | disj φ ψ ih jh => exact fun z => orGate_unit _ (ih z) (jh z)
  | ex φ ih => exact fun _ => quantify_unit _ (Nat.zero_le U) _ (fun _ => ih _)
  | maj φ ih => exact fun _ => quantify_unit _ (Nat.div_le_self U 2) _ (fun _ => ih _)

private theorem represents_cons {k : ℕ} {u : Fin k → Fin U} {z : Fin k → Operand U}
    (h : ∀ i, Represents (z i) (u i)) (i : Fin U) (b : Bool) :
    ∀ j, Represents (Fin.cases (.inr (.inl (.inl (i,b)))) z j) (Fin.cases i u j) :=
  Fin.cases (Or.inr ⟨b,rfl⟩) (fun j => h j)

private theorem sampleEval_correct {k : ℕ} (φ : Formula k) : ∀ (u : Fin k → Fin U) (z : Fin k → Operand U),
    (∀ i, Represents (z i) (u i)) → |sampleEval φ z - bit (φ.eval u)| ≤ epsilon U := by
  obtain ⟨e0,e1,small⟩ := error_small U
  obtain ⟨_,hU,_,_⟩ := numeric (U := U)
  have e := (precision_bounds U).2.1
  have d := (delta_bounds U).1
  induction φ with
  | atom a =>
    intro u z h
    refine atom_error a u _ (gate U) (size_large U) (fun i => scalar_bound (z i))
      (Nat.cast_nonneg _) e0 (by linarith) small (fun i => ?_) (fun i => scalar_close (h i))
    exact (by exact_mod_cast (u i).isLt.le : ((u i).val:ℝ) ≤ U).trans hU
  | neg φ ih => exact fun u z h => negate_error (ih u z h)
  | conj φ ψ ih jh => exact fun u z h => andGate_error _ e d (ih u z h) (jh u z h)
  | disj φ ψ ih jh => exact fun u z h => orGate_error _ e d (ih u z h) (jh u z h)
  | ex φ ih =>
    intro u z h
    exact quantify_error (observed U).tests (Nat.zero_le U) _ _ (fun _ => sampleEval_unit φ _)
      (fun i b => ih _ _ (represents_cons h i b))
  | maj φ ih =>
    intro u z h
    exact quantify_error (observed U).tests (Nat.div_le_self U 2) _ _ (fun _ => sampleEval_unit φ _)
      (fun i b => ih _ _ (represents_cons h i b))

/-- The guarded one-coordinate output from §3.3. The parameters are exact. -/
def output {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U)
    (z : LabelGrid U (Invalid U) (Outside U)) : ℝ :=
  andGate (gate U) (sampleEval φ (Fin.cases (.inr z) (Sum.inl ∘ t))) ((observed U).tests.guard z)

theorem output_unit {k : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) (z) :
    UnitValue (output φ t z) :=
  andGate_unit _ (sampleEval_unit _ _) ((observed U).tests.guard_unit z)

/-- Both representatives approximate the exact truth bit of the arithmetic
formula, uniformly for every numerical parameter tuple and every universe. -/
theorem output_valid {k : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) (i : Fin U) (b : Bool) :
    |output φ t (.inl (.inl (i,b))) - bit (φ.eval (Fin.cases i t))| ≤ epsilon U := by
  have h := sampleEval_correct φ _ _ (represents_cons (u := t) (z := Sum.inl ∘ t) (fun _ => Or.inl rfl) i b)
  simpa only [Bool.and_true] using andGate_error (b := true) (gate U) (precision_bounds U).2.1
    (delta_bounds U).1 h ((observed U).tests.guard_valid i b)

theorem output_invalid {k : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) (i : Invalid U) :
    |output φ t (.inl (.inr i)) - 0| ≤ epsilon U :=
  andGate_false_guard (gate U) (precision_bounds U).2.1 (delta_bounds U).1
    (sampleEval_unit _ _) ((observed U).tests.guard_invalid i)

end
end DiophantineNP.ConcreteGrid
