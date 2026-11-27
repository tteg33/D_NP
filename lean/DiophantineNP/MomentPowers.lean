import DiophantineNP.WidthData
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Simultaneous powering by exact integer digit extraction

The two additive tags of a row are its index and its square. If an ordered
product of n rows has the same two tag sums as n copies of row j, every row
in that product is j. Grouping both tags into a single exponent gives a
polynomially spaced digit containing the exact n-th power of a selected row.
-/
namespace DiophantineNP.MomentPowers
open scoped BigOperators

private theorem equal_rows {r n : ℕ} (f : Fin n → Fin r) (j : Fin r)
    (hs : ∑ i, (f i).val = n*j.val) (hq : ∑ i, (f i).val^2 = n*j.val^2) :
    f = fun _ => j := by
  have hs' : ∑ i, ((f i).val : ℤ) = (n:ℤ)*j.val := by exact_mod_cast hs
  have hq' : ∑ i, ((f i).val : ℤ)^2 = (n:ℤ)*(j.val:ℤ)^2 := by exact_mod_cast hq
  have hz : ∑ i, (((f i).val:ℤ) - j.val)^2 = 0 := by
    calc ∑ i, (((f i).val:ℤ) - j.val)^2 =
        ∑ i, (((f i).val:ℤ)^2 - (2*(j.val:ℤ))*(f i).val + (j.val:ℤ)^2) := by
          apply Finset.sum_congr rfl; intro i _; ring
      _ = 0 := by rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,hs',hq']; simp; ring
  funext i
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => sq_nonneg (((f t).val:ℤ)-j.val))).mp hz i (Finset.mem_univ i)
  apply Fin.ext
  have : ((f i).val:ℤ)=j.val := by nlinarith
  exact_mod_cast this

def tag (n r i : ℕ) := i + (n*r+1)*i^2

theorem tag_unique {r n : ℕ} (f : Fin n → Fin r) (j : Fin r) :
    ∑ i, tag n r (f i).val = n*tag n r j.val ↔ f = fun _ => j := by
  constructor
  · intro he
    let L := n*r+1
    have hf : ∑ i, (f i).val < L := by
      have a := Finset.sum_le_sum (s:=Finset.univ) (g:=fun _ : Fin n => r) (fun i _ => (f i).isLt.le)
      simpa [L] using Nat.lt_succ_of_le a
    have hj : n*j.val < L := Nat.lt_succ_of_le (Nat.mul_le_mul_left _ j.isLt.le)
    have he' : (∑ i, (f i).val) + L*(∑ i, (f i).val^2) = n*j.val + L*(n*j.val^2) := by
      simpa [tag,L,Finset.sum_add_distrib,← Finset.mul_sum,Nat.mul_add,Nat.mul_left_comm] using he
    have hs := congrArg (fun x => x%L) he'
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hf,Nat.mod_eq_of_lt hj] at hs
    apply equal_rows f j hs
    rw [hs] at he'
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos _) (Nat.add_left_cancel he')
  · rintro rfl; simp

/-- Extract a digit from a weighted sum of powers, even when many terms use
the same exponent, provided their total unweighted coefficient sum fits. -/
theorem digit_weighted {ι : Type} [Fintype ι] (c e : ι → ℕ) (b k : ℕ) (h : ∑ i, c i < b) :
    (∑ i, c i*b^(e i)) / b^k % b = ∑ i, if e i=k then c i else 0 := by
  classical
  let low := ∑ i, if e i < k then c i*b^(e i) else 0
  let mid := ∑ i, if e i=k then c i else 0
  let high := ∑ i, if k < e i then c i*b^(e i-(k+1)) else 0
  have hb : 0 < b := (Nat.zero_le _).trans_lt h
  have hp : 0 < b^k := pow_pos hb _
  have hm : mid < b := (Finset.sum_le_sum (g:=c) (fun i _ => by split <;> omega)).trans_lt h
  have hl : low < b^k := by
    cases k with
    | zero => simp [low]
    | succ t =>
      have le : low ≤ ∑ i, c i*b^t := by
        apply Finset.sum_le_sum
        intro i _; split
        · next hi => exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (by omega))
        · exact Nat.zero_le _
      rw [← Finset.sum_mul] at le
      exact le.trans_lt (by simpa [pow_succ,Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right h (pow_pos hb t))
  have he : (∑ i, c i*b^(e i)) = low+b^k*(mid+b*high) := by
    dsimp [low,mid,high]
    rw [Finset.mul_sum,Nat.mul_add,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rcases lt_trichotomy (e i) k with l|l|l
    · simp [l,l.ne,l.not_gt]
    · simp [l,Nat.mul_comm]
    · simp [l,l.ne',l.not_gt]
      have he : e i = k+1+(e i-(k+1)) := by omega
      conv_lhs => rw [he,pow_add,pow_succ]
      ring
  rw [he,Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt hl,Nat.zero_add,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hm]

/-- In the n-th power of one packed integer, a known digit equals the n-th
power of any requested row. Its position is at most n·r + n·(nr+1)·r². -/
theorem packed_power_digit {r n : ℕ} (a : Fin r → ℕ) (j : Fin r) (b : ℕ) (hb : (∑ i, a i)^n < b) :
    (∑ i, a i * b^(tag n r i.val))^n / b^(n*tag n r j.val) % b = (a j)^n := by
  classical
  let c (f : Fin n → Fin r) := ∏ s, a (f s)
  let e (f : Fin n → Fin r) := ∑ s, tag n r (f s).val
  have hw : (∑ i, a i * b^(tag n r i.val))^n = ∑ f, c f*b^(e f) := by
    rw [Fintype.sum_pow]; apply Finset.sum_congr rfl; intro f _
    simp [c,e,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  have hc : ∑ f, c f < b := by simpa [Fintype.sum_pow,c] using hb
  rw [hw,digit_weighted c e b _ hc]
  simp [e,tag_unique,c]

/-- A power-of-two digit base with polynomial bit length suffices. The whole
powered packed integer has at most the displayed polynomial number of bits. -/
theorem powered_word_bound {r n h : ℕ} (a : Fin r → ℕ) (ha : ∑ i, a i ≤ 2^h) :
    let w := h*n+1
    let b := 2^w
    (∑ i, a i)^n < b ∧
      (∑ i, a i*b^(tag n r i.val))^n ≤ 2^((h+w*(r+(n*r+1)*r^2))*n) := by
  let w := h*n+1
  let b := 2^w
  have hb : 0 < b := Nat.two_pow_pos _
  let L := r+(n*r+1)*r^2
  have ht (i : Fin r) : tag n r i.val ≤ L :=
    Nat.add_le_add i.isLt.le (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left i.isLt.le 2))
  have he := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => Nat.mul_le_mul_left (a i) (Nat.pow_le_pow_right hb (ht i)))
  rw [← Finset.sum_mul] at he
  have hw : (∑ i, a i*b^(tag n r i.val)) ≤ 2^(h+w*L) := by
    rw [pow_add,pow_mul]
    exact he.trans (Nat.mul_le_mul_right _ ha)
  constructor
  · calc (∑ i, a i)^n ≤ (2^h)^n := Nat.pow_le_pow_left ha _
      _ = 2^(h*n) := (pow_mul ..).symm
      _ < _ := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  · rw [pow_mul]; exact Nat.pow_le_pow_left hw n

end DiophantineNP.MomentPowers
