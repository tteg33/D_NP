import DiophantineNP.EncodingFacts

/-! # A single binary word for a tuple of certificates

Each natural is written in little-endian binary, with a single zero bit for zero.
Each payload bit is preceded by a one and a zero terminates each field. Thus the
binary word for a fixed tuple has length exactly twice its charged bit cost plus
the arity. The inverse rejects malformed words, including redundant high zeroes.
-/
namespace DiophantineNP.Classes.BinaryCertificates

open Computability

private def digits (n : ℕ) : List Bool :=
  if n = 0 then [false] else encodeNat n

private def readDigits (s : List Bool) : ℕ :=
  if s = [false] then 0 else decodeNat s

private theorem encodeNat_ne_single_zero (n : ℕ) : encodeNat n ≠ [false] := by
  change encodeNum (n : Num) ≠ [false]
  cases (n : Num) with
  | zero => decide
  | pos p =>
    cases p <;> simp [encodeNum, encodePosNum, encodePosNum_nonempty]

private theorem readDigits_digits (n : ℕ) : readDigits (digits n) = n := by
  by_cases h : n = 0
  · simp [h, digits, readDigits]
  · simp [digits, readDigits, h, encodeNat_ne_single_zero]

private theorem digits_length (n : ℕ) : (digits n).length = bits n := by
  by_cases h : n = 0
  · simp [h, digits, bits]
  · simp [digits, h, encodeNat_length_eq_bits h]

/-- A zero marks the end of the field. A one introduces a data bit. -/
private def putField : List Bool → List Bool
  | [] => [false]
  | b :: s => true :: b :: putField s

private def getField : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: rest => some ([], rest)
  | [true] => none
  | true :: b :: rest => (getField rest).map fun (fieldBits, tailBits) => (b :: fieldBits, tailBits)

private theorem getField_putField (s rest : List Bool) :
    getField (putField s ++ rest) = some (s, rest) := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [putField, getField, ih]

private theorem putField_length (s : List Bool) : (putField s).length = 2 * s.length + 1 := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [putField, ih]; omega

/-- The binary certificate obtained by concatenating the tagged fields. -/
def encode : {r : ℕ} → (Fin r → ℕ) → List Bool
  | 0, _ => []
  | _ + 1, w => putField (digits (w 0)) ++ encode (fun i => w i.succ)

private def parse : (r : ℕ) → List Bool → Option (Fin r → ℕ)
  | 0, [] => some Fin.elim0
  | 0, _ :: _ => none
  | r + 1, s => do
    let (fieldBits, rest) ← getField s
    let tail ← parse r rest
    return Fin.cases (readDigits fieldBits) tail

private theorem parse_encode {r : ℕ} (w : Fin r → ℕ) : parse r (encode w) = some w := by
  induction r with
  | zero =>
    exact congrArg some (funext fun i => i.elim0)
  | succ r ih =>
    simp [encode, parse, getField_putField, ih, readDigits_digits]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- Decode only the unique canonical encoding of a tuple, rejecting all other words. -/
def decode (r : ℕ) (s : List Bool) : Option (Fin r → ℕ) := do
  let w ← parse r s
  if encode w = s then some w else none

theorem decode_eq_some_iff {r : ℕ} {s : List Bool} {w : Fin r → ℕ} :
    decode r s = some w ↔ s = encode w := by
  constructor
  · unfold decode
    cases hp : parse r s with
    | none => simp
    | some v =>
      by_cases h : encode v = s
      · simp [h]; intro h'; subst w; exact h.symm
      · simp [h]
  · rintro rfl
    simp [decode, parse_encode]

theorem encode_length {r : ℕ} (w : Fin r → ℕ) :
    (encode w).length = 2 * natCost w + r := by
  induction r with
  | zero => simp [encode, natCost]
  | succ r ih =>
    simp only [encode, List.length_append, putField_length, digits_length, ih,
      natCost, Fin.sum_univ_succ]
    omega

/-- The polynomial bound on word length preserves the original witness cutoff
in both directions. The predicate may accept tuples of arbitrary size. -/
theorem bounded_iff {r : ℕ} (budget : ℕ) (P : (Fin r → ℕ) → Prop) :
    (∃ w, natCost w ≤ budget ∧ P w) ↔
    ∃ s : List Bool, s.length ≤ 2 * budget + r ∧ ∃ w, decode r s = some w ∧ P w := by
  constructor
  · rintro ⟨w, hw, hP⟩
    exact ⟨encode w, by rw [encode_length]; omega, w, decode_eq_some_iff.mpr rfl, hP⟩
  · rintro ⟨s, hs, w, hw, hP⟩
    rw [decode_eq_some_iff.mp hw, encode_length] at hs
    exact ⟨w, by omega, hP⟩

end DiophantineNP.Classes.BinaryCertificates
