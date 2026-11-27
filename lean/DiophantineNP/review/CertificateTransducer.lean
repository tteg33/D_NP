import DiophantineNP.ClockedVerifier
import Lean.Util.CollectAxioms

/-! # Reading a binary certificate as the verifier's framed tape

The scanner retains one payload bit and a flag telling whether it was the first
bit in the current field. A zero tag ends a field. A one tag and the bit that
follows it advance the scanner. Each transition reads at most two bits, writes
at most two tape symbols, and decreases the unprocessed input. The field counter
starts at the fixed certificate arity and only decreases.
-/
namespace DiophantineNP.Classes.BinaryCertificates

open Computability
open private digits readDigits putField from DiophantineNP.BinaryCertificates

/-- The previous payload bit and the flag indicating a one-bit field. -/
private abbrev Pending := Option (Bool × Bool)

private def finish : Pending → Option (List (Option Bool))
  | none => none
  | some (false, true) => some [none]
  | some (true, _) => some [some true, none]
  | some (false, false) => none

private def flush (pending : Pending) (tail : List (Option Bool)) : List (Option Bool) :=
  match pending with
  | none => tail
  | some (b, _) => some b :: tail

private def scan (fields : ℕ) (pending : Pending) (input : List Bool) :
    Option (List (Option Bool)) :=
  match fields, input with
  | 0, [] => if pending.isNone then some [] else none
  | _, [] => none
  | 0, _ :: _ => none
  | _+1, [true] => none
  | r+1, false :: tail => do
    let out ← finish pending
    let rest ← scan r none tail
    return out ++ rest
  | r+1, true :: b :: tail =>
    (scan (r+1) (some (b, pending.isNone)) tail).map (flush pending)
termination_by input.length

/-- Translate one raw binary certificate into the input alphabet of the verifier. -/
def transcode (r : ℕ) (s : List Bool) : Option (List (Option Bool)) := scan r none s

private def tagged : List Bool → List Bool
  | [] => []
  | b :: s => true :: b :: tagged s

private theorem putField_tagged (s : List Bool) : putField s = tagged s ++ [false] := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [putField, tagged, ih]

private theorem scan_pending (r : ℕ) (b first last : Bool) (front rest : List Bool) :
    scan (r+1) (some (b, first)) (tagged (front ++ [last]) ++ rest) =
    (scan (r+1) (some (last, false)) rest).map
      (fun out => (b :: front).map some ++ out) := by
  induction front generalizing b first with
  | nil => simp [tagged, scan]; rfl
  | cons c cs ih =>
    simp only [List.cons_append, tagged, List.cons_append]
    rw [scan]
    simp only [Option.isNone_some, ih]
    cases scan (r+1) (some (last, false)) rest <;> rfl

private theorem scan_zero (r : ℕ) (rest : List Bool) :
    scan (r+1) none (putField [false] ++ rest) =
    (scan r none rest).map (fun out => none :: out) := by
  rw [putField, putField]
  simp only [List.cons_append, List.nil_append]
  rw [scan, scan]
  cases scan r none rest <;> rfl

private theorem scan_positive (r : ℕ) (front rest : List Bool) :
    scan (r+1) none (putField (front ++ [true]) ++ rest) =
    (scan r none rest).map (fun out => ((front ++ [true]).map some ++ [none]) ++ out) := by
  cases front with
  | nil =>
    simp only [List.nil_append]
    rw [putField, putField]
    simp only [List.cons_append, List.nil_append]
    rw [scan, scan]
    cases scan r none rest <;> rfl
  | cons b bits =>
    rw [putField_tagged, List.append_assoc]
    simp only [List.cons_append, tagged, List.nil_append]
    rw [scan, scan_pending, scan]
    cases scan r none rest <;> simp [flush, finish, List.map_append, List.append_assoc]

private theorem scan_final_zero (r : ℕ) (b : Bool) (bits rest : List Bool) :
    scan (r+1) none (putField (b :: (bits ++ [false])) ++ rest) = none := by
  rw [putField_tagged, List.append_assoc]
  simp only [tagged, List.cons_append, List.nil_append]
  rw [scan, scan_pending, scan]
  rfl

private def framed : {r : ℕ} → (Fin r → ℕ) → List (Option Bool)
  | 0, _ => []
  | _+1, w => field (w 0) ++ framed (fun i => w i.succ)

private theorem framed_eq {r : ℕ} (w : Fin r → ℕ) :
    framed w = (List.ofFn fun i => field (w i)).flatten := by
  induction r with
  | zero => simp [framed]
  | succ r ih => simp [framed, List.ofFn_succ, ih]

private theorem scan_field (r : ℕ) (n : ℕ) (rest : List Bool) :
    scan (r+1) none (putField (digits n) ++ rest) =
    (scan r none rest).map (fun out => field n ++ out) := by
  by_cases h : n = 0
  · subst n
    rw [show field 0 = [none] by
      change (encodeNat 0).map some ++ ([none] : List (Option Bool)) = ([none] : List (Option Bool))
      have h : encodeNat 0 = [] := List.length_eq_zero_iff.mp (by simp [encodeNat_length])
      rw [h]; rfl]
    exact scan_zero r rest
  · have final (p : PosNum) : ∃ s : List Bool, encodePosNum p = s ++ [true] := by
      induction p with
      | one => exact ⟨[],rfl⟩
      | bit0 _ ih => obtain ⟨s, hs⟩ := ih; exact ⟨false::s, by simp [encodePosNum,hs]⟩
      | bit1 _ ih => obtain ⟨s, hs⟩ := ih; exact ⟨true::s, by simp [encodePosNum,hs]⟩
    obtain ⟨p, hp⟩ : ∃ p : PosNum, (n : Num) = .pos p := by
      cases hn : (n : Num) with
      | zero =>
        have : n = 0 := by simpa using congrArg (fun m : Num => (m : ℕ)) hn
        contradiction
      | pos p => exact ⟨p, rfl⟩
    obtain ⟨s, hs⟩ := final p
    have he : encodeNat n = s ++ [true] := by simpa [encodeNat, hp, encodeNum] using hs
    change scan (r+1) none (putField (digits n) ++ rest) =
      (scan r none rest).map (fun (out : List (Option Bool)) => ((encodeNat n).map some ++ ([none] : List (Option Bool))) ++ out)
    rw [digits, if_neg h, he, scan_positive]

private theorem scan_encode {r : ℕ} (w : Fin r → ℕ) : scan r none (encode w) = some (framed w) := by
  induction r with
  | zero => simp [encode, framed, scan]
  | succ r ih => rw [encode, scan_field, ih]; rfl

/-- The transducer supplies precisely the verifier's witness suffix. -/
theorem transcode_encode {r : ℕ} (w : Fin r → ℕ) :
    transcode r (encode w) = some ((List.ofFn fun i => field (w i)).flatten) := by
  simpa [transcode, ← framed_eq] using scan_encode w

private theorem firstField (s : List Bool) :
    (∃ fieldBits rest : List Bool, s = putField fieldBits ++ rest) ∨
    (∀ r p, scan (r+1) p s = none) := by
  match s with
  | [] => right; intro r p; simp [scan]
  | false :: rest => exact Or.inl ⟨[],rest,rfl⟩
  | [true] => right; intro r p; rw [scan]
  | true :: b :: tail =>
    rcases firstField tail with ⟨ds, rest, hs⟩ | h
    · subst tail; exact Or.inl ⟨b::ds,rest, by simp [putField]⟩
    · right; intro r p; rw [scan, h]; rfl
termination_by s.length

private theorem canonical_field {r : ℕ} {ds rest : List Bool} {out : List (Option Bool)}
    (h : scan (r+1) none (putField ds ++ rest) = some out) : ∃ n, ds = digits n := by
  cases ds using List.reverseRecOn with
  | nil => simp [putField, scan, finish] at h
  | append_singleton front b =>
    cases b with
    | true =>
      let p := wordSentinel front
      have hn := p.to_nat_pos.ne'
      exact ⟨(p:ℕ), by simpa [digits, hn, p] using (encode_wordSentinel front).symm⟩
    | false =>
      cases front with
      | nil => exact ⟨0, by simp [digits]⟩
      | cons b bits =>
        rw [List.cons_append, scan_final_zero] at h
        contradiction

private theorem sound {r : ℕ} {s : List Bool} {out : List (Option Bool)}
    (h : scan r none s = some out) : ∃ w : Fin r → ℕ, s = encode w ∧ framed w = out := by
  induction r generalizing s out with
  | zero =>
    cases s with
    | nil => exact ⟨Fin.elim0, rfl, by simpa [scan, framed] using h⟩
    | cons b s => simp [scan] at h
  | succ r ih =>
    rcases firstField s with ⟨ds,rest,rfl⟩ | hbad
    · obtain ⟨n,rfl⟩ := canonical_field h
      rw [scan_field] at h
      cases hr : scan r none rest with
      | none => simp [hr] at h
      | some t =>
        obtain ⟨w, rfl, rfl⟩ := ih hr
        refine ⟨Fin.cases n w, ?_, ?_⟩
        · simp [encode]
        · simpa [framed, hr] using h
    · rw [hbad] at h; contradiction

/-- Acceptance of raw binary words is exact, including on malformed inputs. -/
theorem transcode_eq_some_iff {r : ℕ} {s : List Bool} {out : List (Option Bool)} :
    transcode r s = some out ↔
      ∃ w : Fin r → ℕ, s = encode w ∧ out = (List.ofFn fun i => field (w i)).flatten := by
  constructor
  · intro h
    obtain ⟨w, rfl, rfl⟩ := sound h
    exact ⟨w, rfl, framed_eq w⟩
  · rintro ⟨w, rfl, rfl⟩; exact transcode_encode w

/-- Prepending the encoded instance produces exactly the raw tape seen by the
polynomial-time verifier, while preserving the original certificate cutoff. -/
theorem bounded_tape_iff {r : ℕ} (x budget : ℕ) (accept : List (Option Bool) → Prop) :
    (∃ w : Fin r → ℕ, natCost w ≤ budget ∧ accept (tape x w)) ↔
    ∃ s : List Bool, s.length ≤ 2 * budget + r ∧
      ∃ out, transcode r s = some out ∧ accept (field x ++ out) := by
  constructor
  · rintro ⟨w, hw, hP⟩
    exact ⟨encode w, by rw [encode_length]; omega, _, transcode_encode w, hP⟩
  · rintro ⟨s, hs, out, hout, hP⟩
    obtain ⟨w,rfl,rfl⟩ := transcode_eq_some_iff.mp hout
    rw [encode_length] at hs
    exact ⟨w, by omega, hP⟩

/-- The scanner with a transition counter. The terminal transition also costs
one. Each successful branch emits a list of bounded length in front of the
recursive output. -/
private def measured (fields : ℕ) (pending : Pending) (input : List Bool) :
    ℕ × Option (List (Option Bool)) :=
  match fields, input with
  | 0, [] => (1, if pending.isNone then some [] else none)
  | _, [] => (1, none)
  | 0, _ :: _ => (1, none)
  | _+1, [true] => (1, none)
  | r+1, false :: tail =>
    match finish pending with
    | none => (1, none)
    | some out =>
      let result := measured r none tail
      (result.1 + 1, result.2.map (out ++ ·))
  | r+1, true :: b :: tail =>
    let result := measured (r+1) (some (b, pending.isNone)) tail
    (result.1 + 1, result.2.map (flush pending))
termination_by input.length

private theorem measured_spec (r : ℕ) (p : Pending) (s : List Bool) :
    (measured r p s).2 = scan r p s ∧ (measured r p s).1 ≤ s.length + 1 := by
  match r, s with
  | 0, [] => simp [measured, scan]
  | 0, _ :: _ => simp [measured, scan]
  | _+1, [] => simp [measured, scan]
  | _+1, [true] => simp [measured, scan]
  | r+1, false :: t =>
    rw [measured, scan]
    cases h : finish p with
    | none => simp
    | some out =>
      obtain ⟨he, hb⟩ := measured_spec r none t
      simp [he]
      exact ⟨by cases scan r none t <;> rfl, hb⟩
  | r+1, true :: b :: t =>
    rw [measured, scan]
    obtain ⟨he, hb⟩ := measured_spec (r+1) (some (b, p.isNone)) t
    simp [he]
    omega
termination_by s.length

/-- For successful and rejected inputs alike, the counted run returns the same
answer as the transducer and uses at most one transition per bit plus one. -/
def countedTranscode (r : ℕ) (s : List Bool) : ℕ × Option (List (Option Bool)) :=
  measured r none s

theorem countedTranscode_spec (r : ℕ) (s : List Bool) :
    (countedTranscode r s).2 = transcode r s ∧
    (countedTranscode r s).1 ≤ s.length + 1 := measured_spec r none s

/-- A numerical language is in the project's NP exactly when the fixed
transducer followed by a total clocked TM2 accepts its bounded word certificates. -/
theorem clocked_word_iff (L : Language) : L ∈ NP ↔
    ∃ (r : ℕ) (q : Polynomial ℕ) (M : Clocked.Machine) (t : Polynomial ℕ),
      (∀ u, ∃ b, Clocked.runFor M u (t.eval u.length) = Clocked.output M b) ∧
      ∀ x, x ∈ L ↔ ∃ s : List Bool, s.length ≤ 2 * q.eval (bits x) + r ∧
        ∃ out, transcode r s = some out ∧
          Clocked.runFor M (field x ++ out) (t.eval (field x ++ out).length) =
            Clocked.output M true := by
  rw [← Clocked.languages_eq_NP]
  constructor
  · rintro ⟨r, q, M, t, total, h⟩
    exact ⟨r, q, M, t, total, fun x => (h x).trans (bounded_tape_iff (r := r) x (q.eval (bits x)) (fun u =>
      Clocked.runFor M u (t.eval u.length) = Clocked.output M true))⟩
  · rintro ⟨r, q, M, t, total, h⟩
    exact ⟨r, q, M, t, total, fun x => (h x).trans (bounded_tape_iff (r := r) x (q.eval (bits x)) (fun u =>
      Clocked.runFor M u (t.eval u.length) = Clocked.output M true)).symm⟩

open private DiophantineNP.Classes.Clocked.eval_monotone from DiophantineNP.ClockedVerifier in
/-- The sum of scanner transitions and the allowed TM2 steps is polynomial in
the instance length for every admissible word that decodes, including rejected
machine computations. On a malformed word only the scanner runs. -/
theorem combined_clock (r : ℕ) (q t : Polynomial ℕ) :
    ∃ T : Polynomial ℕ, ∀ x (s : List Bool) out,
      s.length ≤ 2 * q.eval (bits x) + r → transcode r s = some out →
      (countedTranscode r s).1 + t.eval (field x ++ out).length ≤ T.eval (bits x) := by
  let pad : Polynomial ℕ := Polynomial.C (r+1)
  refine ⟨q + q + pad + t.comp (Polynomial.X + q + pad), ?_⟩
  intro x s out hlen hout
  obtain ⟨w, rfl, rfl⟩ := transcode_eq_some_iff.mp hout
  have hs := (countedTranscode_spec r (encode w)).2
  rw [encode_length] at hlen hs
  have ht := (tape_length_bounds x w).2
  have hclock := DiophantineNP.Classes.Clocked.eval_monotone t (show (tape x w).length ≤ bits x + q.eval (bits x) + (r+1) by omega)
  change t.eval (tape x w).length ≤ t.eval (bits x + q.eval (bits x) + (r+1)) at hclock
  change _ + t.eval (tape x w).length ≤ _
  simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X, pad, Polynomial.eval_C]
  omega

open Lean Elab Command in
run_cmd do
  for theoremName in #[``clocked_word_iff, ``combined_clock] do
    let axioms ← collectAxioms theoremName
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axiom in {theoremName}: {axioms}"
    logInfo m!"{theoremName} uses {axioms}."

end DiophantineNP.Classes.BinaryCertificates
