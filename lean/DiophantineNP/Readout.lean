import DiophantineNP.ReadoutBits
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! Section 2 of the draft.  All results here operate on native natural
numbers.  `Frame` allows any sufficiently large pairwise coprime prime
powers, independently of how a later compiler produces their product. -/
namespace DiophantineNP.Readout

structure Frame where
  n : ℕ
  m : ℕ
  d : ℕ → ℕ
  width_pos : 0 < n
  scale : 2^n ≤ m
  size : ∀ i < n, n * m < d i
  primePower : ∀ i < n, IsPrimePow (d i)
  coprime : (List.range n).Pairwise (fun i j => Nat.Coprime (d i) (d j))

namespace Frame

def D (F : Frame) : ℕ := ((List.range F.n).map F.d).prod
def q (F : Frame) (i : ℕ) : ℕ := F.D / F.d i
def J (F : Frame) : ℕ := prefixSum (weight F.d F.q F.m) F.n

/-- CRT equivalence with the componentwise conditions, for any pair of integers
represented as naturals. -/
theorem components (F : Frame) {a b : ℕ} :
    a ≡ b [MOD F.D] ↔ ∀ i < F.n, a ≡ b [MOD F.d i] := by
  simpa [D] using (Nat.modEq_list_map_prod_iff (a := a) (b := b) F.coprime)

theorem crt (F : Frame) (bit : ℕ → Bool) :
    ∃ S < F.D, ∀ i < F.n, S ≡ (bit i).toNat [MOD F.d i] := by
  let r := Nat.chineseRemainderOfList (fun i => (bit i).toNat) F.d (List.range F.n) F.coprime
  refine ⟨r.val, Nat.chineseRemainderOfList_lt_prod _ _ _ _ ?_, ?_⟩
  · intro i hi
    have := F.size i (List.mem_range.mp hi)
    omega
  · intro i hi
    exact r.property i (List.mem_range.mpr hi)

theorem D_pos (F : Frame) : 0 < F.D := by
  obtain ⟨S, hS, _⟩ := F.crt (fun _ => false)
  omega

theorem factor (F : Frame) {i : ℕ} (hi : i < F.n) : F.d i * F.q i = F.D := by
  apply Nat.mul_div_cancel'
  exact List.dvd_prod (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem factor_gt_one (F : Frame) {i : ℕ} (hi : i < F.n) : 1 < F.d i := by
  have hp : 0 < F.m := lt_of_lt_of_le (Nat.two_pow_pos _) F.scale
  have := Nat.mul_pos F.width_pos hp
  have := F.size i hi
  omega

private theorem local_idem {d S : ℕ} (hd : IsPrimePow d) (hs : S * S ≡ S [MOD d]) :
    S ≡ 0 [MOD d] ∨ S ≡ 1 [MOD d] := by
  cases S with
  | zero => exact Or.inl Nat.ModEq.rfl
  | succ k =>
    have hle : k + 1 ≤ (k + 1) * (k + 1) := by
      rw [Nat.mul_succ]
      omega
    have hdvd := (Nat.modEq_iff_dvd' hle).mp hs.symm
    have hf : d ∣ (k + 1) * k := by
      simpa only [Nat.mul_succ, Nat.add_sub_cancel] using hdvd
    have hc : Nat.Coprime (k+1) k := by simp
    rcases (hc.isPrimePow_dvd_mul hd).mp hf with h | h
    · exact Or.inl (Nat.modEq_zero_iff_dvd.mpr h)
    · exact Or.inr (by simpa using (Nat.modEq_zero_iff_dvd.mpr h).add_right 1)

/-- The bit selected at a prime-power factor, from the index of the CRT residue. -/
def select (F : Frame) (S i : ℕ) : Bool := decide (S % F.d i = 1)

theorem select_correct (F : Frame) {S : ℕ} (hS : S * S ≡ S [MOD F.D]) :
    ∀ i < F.n, S ≡ (F.select S i).toNat [MOD F.d i] := by
  intro i hi
  have hd := F.factor_gt_one hi
  have hh := local_idem (F.primePower i hi) (F.components.mp hS i hi)
  rcases hh with hz | ho
  · have he : S % F.d i = 0 := by simpa [Nat.ModEq] using hz
    simpa [select, he] using hz
  · have he : S % F.d i = 1 := by simpa [Nat.ModEq, Nat.mod_eq_of_lt hd] using ho
    simpa [select, he] using ho

private theorem weighted_mod {k D m S : ℕ} {d q : ℕ → ℕ} (bit : ℕ → Bool)
    (hprod : ∀ i < k, d i * q i = D)
    (hbit : ∀ i < k, S ≡ (bit i).toNat [MOD d i]) :
    S * prefixSum (weight d q m) k ≡ selectedSum d q bit m k [MOD D] := by
  induction k with
  | zero => simp [selectedSum, prefixSum, Nat.ModEq]
  | succ k ih =>
    have prev := ih (fun i hi => hprod i (by omega)) (fun i hi => hbit i (by omega))
    have hh := ((hbit k (by omega)).mul_right' (q k)).mul_right (d k * 2^k / m)
    rw [hprod k (by omega)] at hh
    have hterm : S * weight d q m k ≡ (bit k).toNat * weight d q m k [MOD D] := by
      simpa [weight, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh
    change S * (prefixSum _ k + _) ≡ selectedSum d q bit m k + _ [MOD D]
    rw [Nat.mul_add]
    exact prev.add hterm

/-- The paper's least-residue and ceiling step for arbitrary CRT selectors. -/
theorem readout (F : Frame) (S : ℕ) (bit : ℕ → Bool)
    (hbit : ∀ i < F.n, S ≡ (bit i).toNat [MOD F.d i]) :
    Ceiling F.D F.m (S * F.J % F.D) (word bit F.n) := by
  have hm : 0 < F.m := lt_of_lt_of_le (Nat.two_pow_pos _) F.scale
  have hprod : ∀ i < F.n, F.d i * F.q i = F.D := fun _ hi => F.factor hi
  have h := weighted_mod (m := F.m) bit hprod hbit
  have hlt := selected_lt bit F.D_pos F.scale hprod
  change S * F.J % F.D = selectedSum F.d F.q bit F.m F.n % F.D at h
  rw [Nat.mod_eq_of_lt hlt] at h
  rw [h]
  exact selected_ceiling bit F.width_pos F.D_pos hm hprod F.size

private theorem lift_idem (F : Frame) (S : ℕ) (bit : ℕ → Bool)
    (hbit : ∀ i < F.n, S ≡ (bit i).toNat [MOD F.d i]) : S*S ≡ S [MOD F.D] := by
  apply F.components.mpr
  intro i hi
  have h := hbit i hi
  apply (h.mul h).trans
  cases hb : bit i <;> simpa [hb] using h.symm

/-- The relation `S*T ≡ S` is the natural-number version of `D ∣ S(1-T)`. -/
def Certificate (F : Frame) (a b : ℕ) : Prop :=
  ∃ S < F.D, ∃ T < F.D,
    S*S ≡ S [MOD F.D] ∧ T*T ≡ T [MOD F.D] ∧ S*T ≡ S [MOD F.D] ∧
    Ceiling F.D F.m (S*F.J % F.D) a ∧ Ceiling F.D F.m (T*F.J % F.D) b

/-- Once the two width words are correct, the full modular system is sound and
complete for inclusion of the binary digits of native inputs. -/
theorem certificate_iff (F : Frame) {a b : ℕ} (ha : a < 2^F.n) (hb : b < 2^F.n) :
    F.Certificate a b ↔ ∀ i, a.testBit i = true → b.testBit i = true := by
  constructor
  · intro ⟨S, _, T, _, hS, hT, hST, hca, hcb⟩ i hai
    have hsi := F.select_correct hS
    have hti := F.select_correct hT
    have ea := ceiling_unique hca (F.readout S _ hsi)
    have eb := ceiling_unique hcb (F.readout T _ hti)
    have hi : i < F.n := by
      by_contra! hn
      have hlt := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hn)
      rw [Nat.testBit_lt_two_pow hlt] at hai
      contradiction
    rw [ea, word_testBit _ hi] at hai
    rw [eb, word_testBit _ hi]
    have h := ((hsi i hi).mul (hti i hi)).symm.trans ((F.components.mp hST i hi).trans (hsi i hi))
    cases ht : F.select T i
    · have hbad : 0 ≡ 1 [MOD F.d i] := by simpa [hai, ht] using h
      have := hbad.eq_of_lt_of_lt (by have := F.factor_gt_one hi; omega) (F.factor_gt_one hi)
      omega
    · rfl
  · intro hincl
    obtain ⟨S, hSlt, hsi⟩ := F.crt a.testBit
    obtain ⟨T, hTlt, hti⟩ := F.crt b.testBit
    refine ⟨S, hSlt, T, hTlt, F.lift_idem _ _ hsi, F.lift_idem _ _ hti, ?_, ?_, ?_⟩
    · apply F.components.mpr
      intro i hi
      have hs := hsi i hi
      have ht := hti i hi
      apply (hs.mul ht).trans
      cases h : a.testBit i
      · simpa [h] using hs.symm
      · simpa [h, hincl i h] using hs.symm
    · simpa [word_native ha] using F.readout S _ hsi
    · simpa [word_native hb] using F.readout T _ hti

end Frame
end DiophantineNP.Readout
