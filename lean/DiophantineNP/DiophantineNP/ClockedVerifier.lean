import DiophantineNP.BinaryCertificates

/-! # A clocked machine characterization of the numerical verifier class

A verifier here is an actual deterministic TM2 machine and a polynomial clock.
The clock runs the transition function for exactly the given fuel, preserving
the last configuration after halting. The tape uses the project's framed binary
encoding. Both acceptance and rejection are witnessed by the machine's output.
-/

namespace DiophantineNP.Classes.Clocked
open Computability Turing

/-- A halted configuration stays in place when the clock has surplus fuel. -/
def tick {α : Type*} (step : α → Option α) (s : α) : α := (step s).getD s

private theorem some_iterate {α : Type*} (step : α → Option α) (s : α) (k : ℕ) (y : α)
    (h : (fun z : Option α => z.bind step)^[k] (some s) = some y) :
    (tick step)^[k] s = y := by
  induction k generalizing y with
  | zero => exact Option.some.inj h
  | succ k ih =>
    rw [Function.iterate_succ_apply'] at h ⊢
    cases hz : (fun z : Option α => z.bind step)^[k] (some s) with
    | none => rw [hz] at h; contradiction
    | some z =>
      rw [hz] at h
      change step z = some y at h
      rw [ih z hz]
      simp [tick, h]

private theorem reaches_iterate {α : Type*} (step : α → Option α) (s : α) (n : ℕ) :
    ∃ k ≤ n, (fun z : Option α => z.bind step)^[k] (some s) = some ((tick step)^[n] s) := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    obtain ⟨k, hk, he⟩ := ih
    rw [Function.iterate_succ_apply']
    cases h : step ((tick step)^[n] s) with
    | none => exact ⟨k, hk.trans n.le_succ, by simpa [tick, h] using he⟩
    | some y =>
      refine ⟨k+1, Nat.succ_le_succ hk, ?_⟩
      rw [Function.iterate_succ_apply', he]
      simp [tick, h]

private theorem stopped_later {α : Type*} (step : α → Option α) {s y : α}
    (hy : step y = none) {k n : ℕ} (hkn : k ≤ n) (hk : (tick step)^[k] s = y) :
    (tick step)^[n] s = y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [Nat.add_comm, Function.iterate_add_apply, hk]
  exact Function.iterate_fixed (show tick step y = y by simp [tick, hy]) d

abbrev Machine := TM2ComputableAux (Option Bool) Bool

def start (M : Machine) (u : List (Option Bool)) : M.tm.Cfg :=
  initList M.tm (u.map M.inputAlphabet.symm)

def output (M : Machine) (b : Bool) : M.tm.Cfg :=
  haltList M.tm [M.outputAlphabet.symm b]

def runFor (M : Machine) (u : List (Option Bool)) (fuel : ℕ) : M.tm.Cfg :=
  (tick M.tm.step)^[fuel] (start M u)

private theorem output_injective (M : Machine) : Function.Injective (output M) := by
  intro a b h
  have hs := congrArg (fun c : M.tm.Cfg => c.stk M.tm.k₁) h
  simpa [output, haltList] using hs

/-- Stopping at the prescribed clock time is equivalent to the bounded halting
relation used by mathlib. This includes halting exactly at the deadline. -/
theorem runFor_eq_output_iff (M : Machine) (u : List (Option Bool)) (b : Bool) (n : ℕ) :
    runFor M u n = output M b ↔
      Nonempty (TM2OutputsInTime M.tm (u.map M.inputAlphabet.symm)
        (some [M.outputAlphabet.symm b]) n) := by
  constructor
  · intro h
    obtain ⟨k, hk, he⟩ := reaches_iterate M.tm.step (start M u) n
    change _ = some (runFor M u n) at he
    rw [h] at he
    exact ⟨⟨⟨k, he⟩, hk⟩⟩
  · rintro ⟨run⟩
    exact stopped_later M.tm.step (y := output M b) rfl run.steps_le_m
      (some_iterate M.tm.step (start M u) run.steps _ run.evals_in_steps)

/-- Languages described by an explicit clocked TM2. Every raw tape, including
malformed input, reaches one of the two Boolean outputs within the clock. -/
def Languages : Set Language := {L |
  ∃ (r : ℕ) (q : Polynomial ℕ) (M : Machine) (t : Polynomial ℕ),
    (∀ u, ∃ b, runFor M u (t.eval u.length) = output M b) ∧
    ∀ x, x ∈ L ↔ ∃ w : Fin r → ℕ, natCost w ≤ q.eval (bits x) ∧
      runFor M (tape x w) (t.eval (tape x w).length) = output M true}

/-- The clocked transition-system and predicate-based verifier definitions
accept the same numerical languages with exactly the same certificate cutoff. -/
theorem languages_eq_NP : Languages = NP := by
  ext L
  constructor
  · rintro ⟨r, q, M, t, total, accept⟩
    choose f hf using total
    have computes : TM2ComputableInPolyTime tapeEncoding finEncodingBoolBool f :=
      { M with
        time := t
        outputsFun := fun u => ((runFor_eq_output_iff M u (f u) _).mp (hf u)).some }
    refine ⟨r, q, fun x w => f (tape x w), ⟨f, ⟨computes⟩, fun _ _ => rfl⟩, ?_⟩
    intro x
    rw [accept]
    apply exists_congr
    intro w
    apply and_congr_right
    intro _
    rw [hf]
    exact output_injective M |>.eq_iff
  · rintro ⟨r, q, V, ⟨f, ⟨C⟩, agrees⟩, accept⟩
    let M := C.toTM2ComputableAux
    have runs (u) : runFor M u (C.time.eval u.length) = output M (f u) :=
      (runFor_eq_output_iff M u (f u) _).mpr ⟨C.outputsFun u⟩
    refine ⟨r, q, M, C.time, fun u => ⟨f u, runs u⟩, ?_⟩
    intro x
    rw [accept]
    apply exists_congr
    intro w
    rw [runs, agrees, (output_injective M).eq_iff]

private theorem eval_monotone (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b h
  induction p using Polynomial.induction_on' with
  | monomial n c => simpa using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)
  | add p q hp hq => simpa using Nat.add_le_add hp hq

/-- A clock in the bit length of the instance alone. For every admissible
certificate it gives the identical halted configuration, even on rejection. -/
theorem instance_clock (M : Machine) (t q : Polynomial ℕ) (r : ℕ)
    (total : ∀ u, ∃ b, runFor M u (t.eval u.length) = output M b) :
    ∃ T : Polynomial ℕ, ∀ x (w : Fin r → ℕ), natCost w ≤ q.eval (bits x) →
      runFor M (tape x w) (T.eval (bits x)) =
        runFor M (tape x w) (t.eval (tape x w).length) := by
  refine ⟨t.comp (Polynomial.X + q + Polynomial.C (r+1)), ?_⟩
  intro x w hw
  obtain ⟨b, hb⟩ := total (tape x w)
  rw [hb]
  apply stopped_later M.tm.step (y := output M b) rfl _ hb
  rw [Polynomial.eval_comp]
  apply eval_monotone t
  have h := (tape_length_bounds x w).2
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  omega

/-- A malformed certificate is rejected. After decoding a single binary word,
the verifier runs on the framed numerical tape. The clock here counts TM2 steps
on that tape. -/
def acceptsWord (M : Machine) (t : Polynomial ℕ) (r x : ℕ) (s : List Bool) : Prop :=
  (BinaryCertificates.decode r s).elim False fun w =>
    runFor M (tape x w) (t.eval (tape x w).length) = output M true

/-- One binary word suffices, with its original cost test enforced exactly. The
decoder is explicit and separate from the clocked machine in this statement. -/
theorem binary_certificate_iff (L : Language) : L ∈ NP ↔
    ∃ (r : ℕ) (q : Polynomial ℕ) (M : Machine) (t : Polynomial ℕ),
      (∀ u, ∃ b, runFor M u (t.eval u.length) = output M b) ∧
      ∀ x, x ∈ L ↔ ∃ s : List Bool, s.length ≤ 2 * q.eval (bits x) + r ∧
        acceptsWord M t r x s := by
  rw [← languages_eq_NP]
  have words (r x : ℕ) (q : Polynomial ℕ) (M : Machine) (t : Polynomial ℕ) :
      (∃ w : Fin r → ℕ, natCost w ≤ q.eval (bits x) ∧
        runFor M (tape x w) (t.eval (tape x w).length) = output M true) ↔
      ∃ s : List Bool, s.length ≤ 2 * q.eval (bits x) + r ∧ acceptsWord M t r x s := by
    rw [BinaryCertificates.bounded_iff]
    apply exists_congr
    intro s
    apply and_congr_right
    intro _
    unfold acceptsWord
    cases h : BinaryCertificates.decode r s <;> simp
  constructor
  · rintro ⟨r, q, M, t, total, accept⟩
    exact ⟨r, q, M, t, total, fun x => (accept x).trans (words r x q M t)⟩
  · rintro ⟨r, q, M, t, total, accept⟩
    exact ⟨r, q, M, t, total, fun x => (accept x).trans (words r x q M t).symm⟩

end DiophantineNP.Classes.Clocked
