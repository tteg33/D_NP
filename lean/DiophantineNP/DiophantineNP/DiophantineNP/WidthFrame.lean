import DiophantineNP.WidthData
import DiophantineNP.Readout
import Mathlib.NumberTheory.PrimeCounting

namespace DiophantineNP.WidthData

/-- The modular system of Section 2, specialized to the actual sequence of
odd prime powers in the manuscript. -/
noncomputable def frame (n : ℕ) (hn : 0 < n) : Readout.Frame where
  n := n
  m := scale n
  d := widthFactor n
  width_pos := hn
  scale := Nat.pow_le_pow_right (by decide) (by omega)
  size := by
    intro i _
    have hi := Nat.add_two_le_nth_prime (i+1)
    have hlo : 3 ≤ Nat.nth Nat.Prime (i+1) := by omega
    exact lt_of_lt_of_le (Readout.paper_budget n) (Nat.pow_le_pow_left hlo _)
  primePower := by
    intro i _
    exact (isPrimePow_nat_iff _).mpr ⟨_, 4*n+10, Nat.prime_nth_prime (i+1), by omega, rfl⟩
  coprime := by
    apply List.Nodup.pairwise_of_forall_ne List.nodup_range
    intro i _ j _ hij
    exact Nat.coprime_pow_primes _ _ (Nat.prime_nth_prime (i+1)) (Nat.prime_nth_prime (j+1))
      (fun h => hij (by have := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective h; omega))

theorem frame_D (n : ℕ) (hn : 0 < n) : (frame n hn).D = widthD n := rfl
theorem frame_J (n : ℕ) (hn : 0 < n) : (frame n hn).J = widthJ n := rfl

theorem widthJ_lt_D (n : ℕ) (hn : 0 < n) : widthJ n < widthD n := by
  let F := frame n hn
  have hprod : ∀ i < F.n, F.d i * F.q i = F.D := fun _ hi => F.factor hi
  have h := Readout.selected_lt (fun _ => true) F.D_pos F.scale hprod
  simpa [Readout.selectedSum, Readout.Frame.J] using
    (show Readout.selectedSum F.d F.q (fun _ => true) F.m F.n < F.D from h)

/-- Fixed-width verifier, using exactly the width data of the manuscript. -/
theorem native_certificate_iff {n a b : ℕ} (hn : 0 < n) (ha : a < 2^n) (hb : b < 2^n) :
    (∃ S < widthD n, ∃ T < widthD n,
      S*S ≡ S [MOD widthD n] ∧ T*T ≡ T [MOD widthD n] ∧ S*T ≡ S [MOD widthD n] ∧
      Readout.Ceiling (widthD n) (scale n) (S * widthJ n % widthD n) a ∧
      Readout.Ceiling (widthD n) (scale n) (T * widthJ n % widthD n) b) ↔
    ∀ i, a.testBit i = true → b.testBit i = true :=
  (frame n hn).certificate_iff ha hb

end DiophantineNP.WidthData
