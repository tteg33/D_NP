import DiophantineNP.Statement
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Bit costs when eliminating a Laurent coordinate

The base for signed coefficient extraction is chosen after positive rational
values have been supplied for the other coordinates. Its bit length depends on
those values. With a fixed number of nested extractions the successive
increases can be bounded explicitly.
-/
namespace DiophantineNP.RadixGrowth

private theorem below_bits (x : ℕ) : x ≤ 2^(bits x) := Nat.lt_log2_self.le

private theorem bits_of_bound {x h : ℕ} (hx : x ≤ 2^h) : bits x ≤ h+1 := by
  by_cases hz : x = 0
  · simp [hz, bits]
  · exact Nat.succ_le_succ ((Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
      ((Nat.log2_self_le hz).trans hx))

def coordinateBits {d : ℕ} (p q : Fin d → ℕ) : ℕ := ∑ i, (bits (p i)+bits (q i))

def clearFactor {d : ℕ} (p q : Fin d → ℕ) (G : ℕ) : ℕ := ∏ i, (p i*q i)^G

def specializedHeight {d : ℕ} (p q : Fin d → ℕ) (H G : ℕ) : ℕ :=
  H * ∏ i, (max (p i) (q i))^(2*G)

private theorem product_of_powers {d : ℕ} {f g : Fin d → ℕ} (h : ∀ i, f i ≤ 2^(g i))
    (G : ℕ) : (∏ i, (f i)^G) ≤ 2^(G*(∑ i, g i)) := by
  calc
    _ ≤ ∏ i, (2^(g i))^G := Finset.prod_le_prod' (fun i _ => Nat.pow_le_pow_left (h i) _)
    _ = ∏ i, 2^(G*g i) := by apply Finset.prod_congr rfl; intro i _; rw [← pow_mul, Nat.mul_comm (g i) G]
    _ = _ := by rw [Finset.mul_sum, Finset.prod_pow_eq_pow_sum]

theorem clearFactor_bound {d : ℕ} (p q : Fin d → ℕ) (G : ℕ) :
    clearFactor p q G ≤ 2^(G*coordinateBits p q) := by
  apply product_of_powers
  intro i
  rw [pow_add]
  exact Nat.mul_le_mul (below_bits _) (below_bits _)

theorem specializedHeight_bound {d : ℕ} (p q : Fin d → ℕ) (H G : ℕ) :
    specializedHeight p q H G ≤ 2^(bits H+2*G*coordinateBits p q) := by
  rw [pow_add]
  apply Nat.mul_le_mul (below_bits _)
  apply product_of_powers
  intro i
  apply max_le
  · exact (below_bits _).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..))
  · exact (below_bits _).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..))

/-- Auxiliary radix from Lemma 3.5, with b a supported shift. -/
def radix {d : ℕ} (p q : Fin d → ℕ) (H G b : ℕ) :=
  4*(specializedHeight p q H G*(2*b+1))+5

theorem radix_bits {d : ℕ} (p q : Fin d → ℕ) (H G b : ℕ) :
    bits (radix p q H G b) ≤ bits H + 2*G*coordinateBits p q + bits (2*b+1) + 5 := by
  let k := bits H + 2*G*coordinateBits p q + bits (2*b+1)
  have hf : specializedHeight p q H G * (2*b+1) ≤ 2^k := by
    dsimp [k]
    rw [pow_add]
    exact Nat.mul_le_mul (specializedHeight_bound p q H G) (below_bits _)
  have hpos : 0 < 2^k := Nat.two_pow_pos _
  apply bits_of_bound (h := k+4)
  rw [pow_add]
  unfold radix
  omega

/-- Raising the evaluation radix to any indicated extraction exponent still
costs only a factor linear in the *value* of that exponent in bit length. -/
theorem radix_power_bits {d : ℕ} (p q : Fin d → ℕ) (H G b e : ℕ) :
    bits ((radix p q H G b)^e) ≤ e*(bits H+2*G*coordinateBits p q+bits (2*b+1)+5)+1 := by
  apply bits_of_bound
  rw [Nat.mul_comm e, pow_mul]
  apply Nat.pow_le_pow_left
  exact (below_bits _).trans (Nat.pow_le_pow_right (by decide) (radix_bits ..))

/-- If A bounds the local constants, adjoining the new coordinate to an
existing scalar evaluator grows its input bit size by this explicit factor. -/
theorem next_size {d : ℕ} (p q : Fin d → ℕ) (H G b A : ℕ)
    (hA : bits H + bits (2*b+1) + 2*G + 9 ≤ A) :
    coordinateBits p q + bits (radix p q H G b) + bits 1 + 1 ≤
      A*(coordinateBits p q+1) := by
  have hz := radix_bits p q H G b
  have hb : bits 1 = 1 := by decide
  let s := coordinateBits p q
  change s + _ + _ + 1 ≤ A*(s+1)
  change bits _ ≤ bits H+2*G*s+bits (2*b+1)+5 at hz
  have hmul := Nat.mul_le_mul_right s (show 2*G+1 ≤ A by omega)
  rw [Nat.add_mul, Nat.one_mul] at hmul
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The multiplicative overhead is paid once for each node on the evaluation path. -/
theorem nested_size (A : ℕ) (s : ℕ → ℕ) (height : ℕ)
    (step : ∀ i<height, s (i+1)+1 ≤ A*(s i+1)) :
    s height+1 ≤ A^height*(s 0+1) := by
  induction height with
  | zero => simp
  | succ h ih =>
    have prev := ih (fun i hi => step i (by omega))
    exact (step h (by omega)).trans (by simpa [pow_succ', Nat.mul_assoc] using Nat.mul_le_mul_left A prev)

end DiophantineNP.RadixGrowth
