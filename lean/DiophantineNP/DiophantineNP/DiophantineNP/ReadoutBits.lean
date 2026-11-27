import Std

/-! Binary word arithmetic used by the CRT readout. -/
namespace DiophantineNP.Readout

/-- Sum indexed from zero, with the empty prefix contributing zero. -/
def prefixSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSum f n + f n

def word (bit : Nat → Bool) (n : Nat) : Nat :=
  prefixSum (fun i => (bit i).toNat * 2^i) n

theorem word_lt (bit : Nat → Bool) (n : Nat) : word bit n < 2^n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    change word bit n + (bit n).toNat * 2^n < 2^(n+1)
    rw [Nat.pow_succ]
    cases bit n <;> simp <;> omega

/-- Each position below the declared width is exactly the supplied bit. -/
theorem word_testBit (bit : Nat → Bool) {n i : Nat} (hi : i < n) :
    (word bit n).testBit i = bit i := by
  induction n with
  | zero => omega
  | succ n ih =>
    change (word bit n + (bit n).toNat * 2^n).testBit i = bit i
    rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (word_lt bit n)]
    by_cases h : i < n
    · simpa [h] using ih h
    · have hie : i = n := by omega
      subst i
      cases bit n <;> simp

theorem word_native {x n : Nat} (hx : x < 2^n) : word x.testBit n = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact word_testBit x.testBit hi
  · have hni : n ≤ i := by omega
    have hp : 2^n ≤ 2^i := Nat.pow_le_pow_right (by decide) hni
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (word_lt _ _) hp),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx hp)]

/-- The two inequalities specify the ceiling without truncated subtraction at zero. -/
def Ceiling (D m numerator a : Nat) : Prop :=
  m * numerator ≤ a * D ∧ a * D < m * numerator + D

theorem ceiling_unique {D m N a b : Nat} (ha : Ceiling D m N a) (hb : Ceiling D m N b) :
    a = b := by
  obtain ⟨ha₁, ha₂⟩ := ha
  obtain ⟨hb₁, hb₂⟩ := hb
  have h : ∀ x y : Nat, x < y → x * D + D ≤ y * D := by
    intro x y hxy
    simpa [Nat.succ_mul] using Nat.mul_le_mul_right D (show x + 1 ≤ y by omega)
  rcases Nat.lt_trichotomy a b with hab | hab | hba
  · have := h _ _ hab
    omega
  · exact hab
  · have := h _ _ hba
    omega

/-- Draft coefficients, already multiplied by their complementary factors. -/
def weight (d q : Nat → Nat) (m i : Nat) : Nat := (d i * 2^i / m) * q i

def selectedSum (d q : Nat → Nat) (bit : Nat → Bool) (m n : Nat) : Nat :=
  prefixSum (fun i => (bit i).toNat * weight d q m i) n

private def errors (d q : Nat → Nat) (bit : Nat → Bool) (m n : Nat) : Nat :=
  prefixSum (fun i => (bit i).toNat * ((d i * 2^i) % m) * q i) n

private theorem floors {n D m : Nat} {d q : Nat → Nat} (bit : Nat → Bool)
    (hprod : ∀ i < n, d i * q i = D) :
    m * selectedSum d q bit m n + errors d q bit m n = word bit n * D := by
  induction n with
  | zero => simp [selectedSum, errors, word, prefixSum]
  | succ n ih =>
    have h := ih (fun i hi => hprod i (by omega))
    have hstep :
        m * ((bit n).toNat * weight d q m n) +
        (bit n).toNat * ((d n * 2^n) % m) * q n =
        ((bit n).toNat * 2^n) * D := by
      have hf := Nat.mod_add_div (d n * 2^n) m
      have hh := congrArg (fun a => a * q n) hf
      dsimp only at hh
      rw [Nat.add_mul] at hh
      cases bit n
      · simp
      · simp [weight, ← hprod n (by omega),
          Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hh ⊢
        omega
    change m * (selectedSum d q bit m n + _) + (errors d q bit m n + _) =
      (word bit n + _) * D
    rw [Nat.mul_add, Nat.add_mul]
    dsimp only
    omega

private theorem prefix_le {f : Nat → Nat} {N k v : Nat} (h : ∀ i < k, N * f i ≤ v) :
    N * prefixSum f k ≤ k * v := by
  induction k with
  | zero => simp [prefixSum]
  | succ k ih =>
    have a := ih (fun i hi => h i (by omega))
    have b := h k (by omega)
    simpa [prefixSum, Nat.mul_add, Nat.succ_mul] using Nat.add_le_add a b

/-- Aggregate floor errors, compared in integers.  The sufficient condition
`n * m < d i` is deliberately stronger than the sharp error budget. -/
theorem selected_ceiling {n D m : Nat} {d q : Nat → Nat} (bit : Nat → Bool)
    (hn : 0 < n) (hD : 0 < D) (hm : 0 < m) (hprod : ∀ i < n, d i * q i = D)
    (hsize : ∀ i < n, n * m < d i) :
    Ceiling D m (selectedSum d q bit m n) (word bit n) := by
  have heq := floors (m := m) bit hprod
  have hsmall : ∀ i < n,
      n * ((bit i).toNat * ((d i * 2^i) % m) * q i) ≤ D - 1 := by
    intro i hi
    have hp := hprod i hi
    have hq : 0 < q i := by
      by_cases h : q i = 0
      · simp [h] at hp
        omega
      · omega
    have hrem := Nat.mod_lt (d i * 2^i) hm
    have h₁ := Nat.mul_le_mul_left n (Nat.le_of_lt hrem)
    have h₂ := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_le_of_lt h₁ (hsize i hi)) hq
    cases bit i
    · simp
    · simp only [Bool.toNat_true, Nat.one_mul, ← Nat.mul_assoc]
      omega
  have hbound := prefix_le hsmall
  change n * errors d q bit m n ≤ n * (D-1) at hbound
  have hsmall' := Nat.le_of_mul_le_mul_left hbound hn
  constructor <;> omega

/-- With a wide enough scale factor, the ordinary coefficient sum is already
the least nonnegative representative. -/
theorem selected_lt {n D m : Nat} {d q : Nat → Nat} (bit : Nat → Bool)
    (hD : 0 < D) (hwidth : 2^n ≤ m) (hprod : ∀ i < n, d i * q i = D) :
    selectedSum d q bit m n < D := by
  have heq := floors (m := m) bit hprod
  have hw := Nat.lt_of_lt_of_le (word_lt bit n) hwidth
  have hmul := Nat.mul_lt_mul_of_pos_right hw hD
  by_cases h : D ≤ selectedSum d q bit m n
  · have hh := Nat.mul_le_mul_left m h
    have hcomm := Nat.mul_comm m D
    omega
  · omega

/-- The paper's scale and its lower bound on all prime powers meet the floor budget. -/
theorem paper_budget (n : Nat) : n * 2^(n+2) < 3^(4*n+10) := by
  have h₁ : n < 2^n := Nat.lt_two_pow_self
  have h₂ : n * 2^(n+2) < 2^n * 2^(n+2) :=
    Nat.mul_lt_mul_of_pos_right h₁ (Nat.two_pow_pos _)
  rw [← Nat.pow_add] at h₂
  have h₃ : (2:Nat)^(n+(n+2)) ≤ 3^(n+(n+2)) := Nat.pow_le_pow_left (by decide) _
  have h₄ : (3:Nat)^(n+(n+2)) ≤ 3^(4*n+10) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

end DiophantineNP.Readout
