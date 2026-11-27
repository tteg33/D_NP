import DiophantineNP.JonesRegisters

/-! # Bounded register traces for the native verifier definition

Every native NP language has a fixed finite-control register verifier. Its
transition relation is `regStep` for the actual mathlib TM2 machine. The trace
length and the binary length of every register at every row are polynomial in
the input bit length. The original certificate cutoff is part of acceptance.
-/
namespace DiophantineNP.Classes.Jones.Machine
open Turing Computability
open scoped Classical
noncomputable section

/-- One row per configuration, including both endpoints. -/
def IsTrace {A : Type} (next : A → Option A) {n : ℕ} (row : Fin (n+1) → A) : Prop :=
  ∀ j : Fin n, next (row j.castSucc) = some (row j.succ)

private abbrev stepOpt {A : Type} (next : A → Option A) (v : Option A) := v.bind next

private theorem run_none {A : Type} (next : A → Option A) (n : ℕ) :
    (stepOpt next)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih]; rfl

private theorem run_prefix {A : Type} {next : A → Option A} {s t : A} {m n : ℕ} (hm : m ≤ n)
    (hr : (stepOpt next)^[n] (some s) = some t) : ∃ v, (stepOpt next)^[m] (some s) = some v := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hm
  rw [hd,Nat.add_comm m d,Function.iterate_add_apply] at hr
  cases hv : (stepOpt next)^[m] (some s) with
  | none => rw [hv,run_none] at hr; contradiction
  | some v => exact ⟨v,rfl⟩

/-- The executable iterate and a finite sequence satisfying the one-step
relation give exactly the same reachable endpoint. -/
theorem iterate_iff_trace {A : Type} (next : A → Option A) (s t : A) (n : ℕ) :
    (fun v : Option A => v.bind next)^[n] (some s) = some t ↔
      ∃ row : Fin (n+1) → A, row 0 = s ∧ row (Fin.last n) = t ∧ IsTrace next row := by
  change (stepOpt next)^[n] (some s) = some t ↔ _
  constructor
  · intro h
    have hv (j : Fin (n+1)) := run_prefix (Nat.le_of_lt_succ j.isLt) h
    let row (j : Fin (n+1)) := (hv j).choose
    have head (j : Fin (n+1)) : (stepOpt next)^[j.val] (some s) = some (row j) := (hv j).choose_spec
    refine ⟨row,(Option.some.inj (head 0)).symm,Option.some.inj ((head (Fin.last n)).symm.trans h),?_⟩
    intro j
    have hnext := head j.succ
    rw [Fin.val_succ,Function.iterate_succ_apply'] at hnext
    change stepOpt next ((stepOpt next)^[j.castSucc.val] (some s)) = _ at hnext
    rw [head j.castSucc] at hnext
    exact hnext
  · rintro ⟨row, h0, hn, hstep⟩
    have go (j : Fin (n+1)) : (stepOpt next)^[j.val] (some s) = some (row j) := by
      induction j using Fin.induction with
      | zero => simpa using congrArg some h0.symm
      | succ j ih =>
        rw [Fin.val_succ, Function.iterate_succ_apply']
        change stepOpt next ((stepOpt next)^[j.castSucc.val] (some s)) = _
        rw [ih]; exact hstep j
    exact (go (Fin.last n)).trans (congrArg some hn)

private theorem trace_row {A : Type} {next : A → Option A} {n : ℕ} (row : Fin (n+1) → A)
    (hstep : IsTrace next row) (j : Fin (n+1)) :
    (stepOpt next)^[j.val] (some (row 0)) = some (row j) := by
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
    rw [Fin.val_succ, Function.iterate_succ_apply']
    change stepOpt next ((stepOpt next)^[j.castSucc.val] (some (row 0))) = _
    rw [ih]; exact hstep j

private theorem ordered_halts {A : Type} (next : A → Option A) (s a b : A) (n m : ℕ)
    (ha : (stepOpt next)^[n] (some s) = some a) (hb : (stepOpt next)^[m] (some s) = some b)
    (hhalt : next a = none) (hle : n ≤ m) : a = b := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hle
  cases d with
  | zero => exact Option.some.inj (ha.symm.trans hb)
  | succ d =>
    rw [Nat.add_comm,Function.iterate_add_apply,ha,Function.iterate_succ_apply] at hb
    change (stepOpt next)^[d] (next a) = some b at hb
    rw [hhalt,run_none] at hb
    contradiction

private theorem unique_halt {A : Type} (next : A → Option A) (s a b : A) (n m : ℕ)
    (ha : (stepOpt next)^[n] (some s) = some a) (hb : (stepOpt next)^[m] (some s) = some b)
    (h₁ : next a = none) (h₂ : next b = none) : a = b := by
  rcases Nat.le_total n m with h | h
  · exact ordered_halts next s a b n m ha hb h₁ h
  · exact (ordered_halts next s b a m n hb ha h₂ h).symm

abbrev VerifierMachine := TM2ComputableAux tapeEncoding.Γ finEncodingBoolBool.Γ

def verifierInput (M : VerifierMachine) (s : List (Option Bool)) : List (M.tm.Γ M.tm.k₀) :=
  s.map M.inputAlphabet.invFun

def verifierHalt (M : VerifierMachine) (b : Bool) : M.tm.Cfg :=
  haltList M.tm [M.outputAlphabet.symm b]

private theorem verifierHalt_inj (M : VerifierMachine) {a b : Bool}
    (h : verifierHalt M a = verifierHalt M b) : a = b := by
  have e := congrArg (fun c : M.tm.Cfg => c.stk M.tm.k₁) h
  simpa [verifierHalt,haltList] using e

/-- The target halt must consist of supported symbols. The stack coding
reserves digit zero for symbols outside the machine's reachable alphabet. -/
def AcceptingRegisterTrace (M : VerifierMachine) (s : List (Option Bool)) (n B : ℕ) : Prop :=
  Supported M.tm (verifierHalt M true).stk ∧ ∃ row : Fin (n+1) → Registers M.tm,
    row 0 = encode M.tm (initList M.tm (verifierInput M s)) ∧
    row (Fin.last n) = encode M.tm (verifierHalt M true) ∧
    IsTrace (regStep M.tm) row ∧ ∀ j k, ((row j).stack k).size ≤ B

private theorem actual_run {f : List (Option Bool) → Bool}
    (M : TM2ComputableInPolyTime tapeEncoding finEncodingBoolBool f) (s : List (Option Bool)) :
    ∃ n ≤ M.time.eval s.length,
      (stepOpt M.tm.step)^[n] (some (initList M.tm (verifierInput M.toTM2ComputableAux s))) =
        some (verifierHalt M.toTM2ComputableAux (f s)) := by
  let h := M.outputsFun s
  exact ⟨h.steps,h.steps_le_m,h.evals_in_steps⟩

/-- Soundness holds for every trace length, including traces using a larger
time or space budget than the machine requires. -/
theorem acceptingTrace_sound {f : List (Option Bool) → Bool}
    (M : TM2ComputableInPolyTime tapeEncoding finEncodingBoolBool f) {s : List (Option Bool)}
    {n B : ℕ} (h : AcceptingRegisterTrace M.toTM2ComputableAux s n B) : f s = true := by
  let M' := M.toTM2ComputableAux
  obtain ⟨htarget, row, h0, hn, hstep, _⟩ := h
  have hr := (iterate_iff_trace (regStep M.tm) _ _ _).2 ⟨row,h0,hn,hstep⟩
  rw [regRun_exact] at hr
  cases he : (fun v : Option M.tm.Cfg => v.bind M.tm.step)^[n]
      (some (initList M.tm (verifierInput M' s))) with
  | none => rw [he] at hr; contradiction
  | some c =>
    rw [he] at hr
    have hc := (reachable_stacks M.tm _ n c he).1
    have ec := encode_inj_on M.tm hc htarget (Option.some.inj hr)
    obtain ⟨m,_,hm⟩ := actual_run M s
    apply verifierHalt_inj M'
    apply unique_halt M.tm.step _ _ _ m n hm (he.trans (congrArg some ec)) <;> rfl

/-- Completeness includes a bound at each intermediate row. -/
theorem acceptingTrace_complete {f : List (Option Bool) → Bool}
    (M : TM2ComputableInPolyTime tapeEncoding finEncodingBoolBool f) (s : List (Option Bool))
    (h : f s = true) : ∃ n ≤ M.time.eval s.length,
    AcceptingRegisterTrace M.toTM2ComputableAux s n
      (blockSize M.tm * (s.length + n*perStep M.tm)) := by
  let M' := M.toTM2ComputableAux
  obtain ⟨n, hn, hr⟩ := actual_run M s
  rw [h] at hr
  have hreg := (regRun_exact M.tm (verifierInput M' s) n).trans (congrArg (Option.map (encode M.tm)) hr)
  obtain ⟨row,h0,hLast,hstep⟩ := (iterate_iff_trace (regStep M.tm) _ _ n).1 hreg
  refine ⟨n,hn,(reachable_stacks M.tm _ n _ hr).1,row,h0,hLast,hstep,?_⟩
  intro j k
  have hj := trace_row row hstep j
  rw [h0] at hj
  change (fun v : Option (Registers M.tm) => v.bind (regStep M.tm))^[j.val] _ = _ at hj
  rw [regRun_exact] at hj
  cases he : (fun v : Option M.tm.Cfg => v.bind M.tm.step)^[j.val]
      (some (initList M.tm (verifierInput M' s))) with
  | none => rw [he] at hj; contradiction
  | some c =>
    rw [he] at hj
    have ec : encode M.tm c = row j := Option.some.inj hj
    rw [← ec]
    have hz := reachable_register_size M.tm _ j.val c he k
    simp only [verifierInput,List.length_map] at hz
    exact hz.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ j.isLt)) _))

private theorem nat_poly_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  induction p using Polynomial.induction_on' with
  | monomial n c => simpa using Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)
  | add p q hp hq => simpa using Nat.add_le_add hp hq

/-- The original witness bound is part of the equivalence. Time and binary
register space are bounded by fixed polynomials in `bits x` across the entire
trace; both include the cost of the framed certificate tape. -/
theorem np_has_bounded_register_verifier {L : Language} (hL : L ∈ NP) :
    ∃ (r : ℕ) (q : Polynomial ℕ) (M : VerifierMachine) (T S : Polynomial ℕ), ∀ x,
      x ∈ L ↔ ∃ (w : Fin r → ℕ) (n : ℕ), natCost w ≤ q.eval (bits x) ∧ n ≤ T.eval (bits x) ∧
        AcceptingRegisterTrace M (tape x w) n (S.eval (bits x)) := by
  obtain ⟨r,q,V,⟨f,⟨M⟩,hV⟩,hL⟩ := hL
  let p : Polynomial ℕ := Polynomial.X + q + Polynomial.C (r+1)
  let T := M.time.comp p
  let S := Polynomial.C (blockSize M.tm) * (p + T * Polynomial.C (perStep M.tm))
  refine ⟨r,q,M.toTM2ComputableAux,T,S,fun x => ?_⟩
  rw [hL]
  constructor
  · rintro ⟨w,hw,hv⟩
    have hf := (hV x w).trans hv
    obtain ⟨n,hn,ht,rows,h0,hLast,hStep,hSpace⟩ := acceptingTrace_complete M _ hf
    have hlength : (tape x w).length ≤ p.eval (bits x) := by
      simpa [p] using (tape_length_bounds x w).2.trans (Nat.add_le_add_right (Nat.add_le_add_left hw _) _)
    have htime : n ≤ T.eval (bits x) := by simpa [T,Polynomial.eval_comp] using hn.trans (nat_poly_mono M.time hlength)
    refine ⟨w,n,hw,htime,ht,rows,h0,hLast,hStep,fun j k => (hSpace j k).trans ?_⟩
    simpa [S] using Nat.mul_le_mul_left (blockSize M.tm) (Nat.add_le_add hlength (Nat.mul_le_mul_right (perStep M.tm) htime))
  · rintro ⟨w,n,hw,_,ht⟩
    exact ⟨w,hw,(hV x w).symm.trans (acceptingTrace_sound M ht)⟩

end
end DiophantineNP.Classes.Jones.Machine
