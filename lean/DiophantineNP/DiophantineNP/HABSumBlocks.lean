import DiophantineNP.GeneralSumTemplate
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-! # Iterated addition by bounded diagonal counts and two binary words

The column populations are short binary numbers. Redistributing their bits yields
a second array whose columns have population at most the number of bits L in
a first population. Grouping k consecutive columns then gives a digit with
at most two base-2^k digits when L ≤ 2^k. Splitting these digits into two
ordinary words leaves only one binary addition. The top block is padded
with zeros, so the construction applies without a divisibility assumption. -/

namespace DiophantineNP.HABSumBlocks
open Finset

def column (f : ℕ → ℕ) (rows i : ℕ) : ℕ :=
  ((range rows).filter (fun r => (f r).testBit i)).card

def diagonal (c : ℕ → ℕ) (L j : ℕ) : ℕ :=
  ((range L).filter (fun t => t ≤ j ∧ (c (j-t)).testBit t = true)).card

def block (c : ℕ → ℕ) (U L k start : ℕ) : ℕ :=
  ∑ s ∈ range k, (if start+s<U then diagonal c L (start+s) else 0) * 2^s

private def digits (k : ℕ) (f : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ i ∈ range N, f i * 2^(i*k)

def lowWord (c : ℕ → ℕ) (U L k : ℕ) : ℕ :=
  digits k (fun i => block c U L k (i*k) % 2^k) U

def highWord (c : ℕ → ℕ) (U L k : ℕ) : ℕ :=
  2^k * digits k (fun i => block c U L k (i*k) / 2^k) U

theorem column_le (f : ℕ → ℕ) (rows i : ℕ) : column f rows i ≤ rows := by
  simpa [column] using (card_filter_le (range rows) (fun r => (f r).testBit i = true))

theorem diagonal_le (c : ℕ → ℕ) (L j : ℕ) : diagonal c L j ≤ L := by
  simpa [diagonal] using (card_filter_le (range L) (fun t => t ≤ j ∧ (c (j-t)).testBit t = true))

theorem block_bound (c : ℕ → ℕ) (U L k start : ℕ) (hL : L ≤ 2^k) :
    block c U L k start < 2^k * 2^k := by
  have hs := Finset.sum_le_sum (s:=range k) (g:=fun s => 2^k * 2^s)
    (f:=fun s => (if start+s<U then diagonal c L (start+s) else 0) * 2^s)
    (fun s _ => Nat.mul_le_mul_right _ (by split <;> first | exact (diagonal_le ..).trans hL | omega))
  have hex := geom_sum_mul_add (1:ℕ) k
  simp only [one_add_one_eq_two,mul_one] at hex
  rw [← Finset.mul_sum] at hs
  exact lt_of_le_of_lt hs (Nat.mul_lt_mul_of_pos_left (by omega) (Nat.two_pow_pos _))

private theorem digits_succ (f : ℕ → ℕ) (k n : ℕ) :
    digits k f (n+1) = 2^k * digits k (fun i => f (i+1)) n + f 0 := by
  simp only [digits, sum_range_succ' (fun i => f i*2^(i*k)), zero_mul, pow_zero, mul_one,
    Finset.mul_sum, Nat.succ_mul, pow_add]
  congr 1
  apply sum_congr rfl
  intro i hi
  ring

private theorem digits_bit (f : ℕ → ℕ) (k n a t : ℕ) (ha : a<n) (ht : t<k)
    (hf : ∀ i<n, f i < 2^k) :
    (digits k f n).testBit (a*k+t) = (f a).testBit t := by
  induction n generalizing a f with
  | zero => omega
  | succ n ih =>
    rw [digits_succ, Nat.testBit_two_pow_mul_add _ (hf 0 (by omega))]
    cases a with
    | zero => simp [ht]
    | succ a =>
      have hstart : ¬ ((a+1)*k+t<k) := by rw [Nat.succ_mul]; omega
      rw [if_neg hstart, Nat.succ_mul, show a*k+k+t-k=a*k+t by omega]
      exact ih (fun i => f (i+1)) a (by omega) (fun i hi => hf (i+1) (by omega))

theorem lowWord_bit (c : ℕ → ℕ) {U L k j : ℕ} (hk : 0<k) (hj : j<U) :
    (lowWord c U L k).testBit j = (block c U L k (j/k*k)).testBit (j%k) := by
  let f := fun i => block c U L k (i*k) % 2^k
  have hh := digits_bit f k U (j/k) (j%k) ((Nat.div_le_self j k).trans_lt hj) (Nat.mod_lt j hk)
    (fun i _ => Nat.mod_lt _ (Nat.two_pow_pos k))
  rw [Nat.mul_comm (j/k) k,Nat.div_add_mod] at hh
  simpa [lowWord,f,Nat.testBit_mod_two_pow,Nat.mod_lt j hk] using hh

theorem highWord_bit (c : ℕ → ℕ) {U L k j : ℕ} (hk : 0<k) (hj : j<U) (hL : L≤2^k) :
    (highWord c U L k).testBit j =
      (if j<k then false else (block c U L k ((j/k-1)*k)).testBit (k+j%k)) := by
  rw [highWord,Nat.testBit_two_pow_mul]
  by_cases h : j<k
  · simp [h,show ¬k≤j by omega]
  · rw [if_neg h,decide_eq_true (by omega : k≤j),Bool.true_and]
    let f := fun i => block c U L k (i*k) / 2^k
    have ht := Nat.mod_lt j hk
    have hq : 1≤j/k := (Nat.le_div_iff_mul_le hk).mpr (by omega)
    have hd : (j/k-1)*k+j%k=j-k := by
      have hd := Nat.div_add_mod j k
      rw [Nat.mul_comm k (j/k)] at hd
      have hp : (j/k-1)*k+k=j/k*k := by rw [← Nat.succ_mul, show (j/k-1).succ=j/k by omega]
      omega
    have hh := digits_bit f k U (j/k-1) (j%k) (by have := Nat.div_le_self j k; omega) ht
      (fun i _ => (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr (block_bound c U L k (i*k) hL))
    rw [hd] at hh
    simpa [f,Nat.testBit_div_two_pow,Nat.add_comm k (j%k)] using hh

private theorem prefix_sum (f : ℕ → ℕ) (N : ℕ) :
    Readout.prefixSum f N = ∑ i ∈ range N, f i := by
  induction N with
  | zero => simp [Readout.prefixSum]
  | succ N ih => rw [Readout.prefixSum,ih,sum_range_succ]

private theorem pack_bits {x N : ℕ} (h : x<2^N) :
    ∑ i ∈ range N, (x.testBit i).toNat*2^i = x := by
  simpa [Readout.word,prefix_sum] using Readout.word_native h

private theorem column_sum (f : ℕ→ℕ) (rows U : ℕ) (fits : ∀r<rows, f r<2^U) :
    ∑ i ∈ range U, column f rows i * 2^i = Readout.prefixSum f rows := by
  rw [prefix_sum]
  have hf (i) : column f rows i = ∑ r ∈ range rows, ((f r).testBit i).toNat := by
    rw [column,card_filter]; apply sum_congr rfl; intro r _
    cases (f r).testBit i <;> rfl
  simp_rw [hf,Finset.sum_mul]
  rw [Finset.sum_comm]
  exact sum_congr rfl (fun r hr => pack_bits (fits r (mem_range.mp hr)))

private theorem sum_congr_mod {N m : ℕ} {f g : ℕ→ℕ}
    (h : ∀i<N, f i ≡ g i [MOD m]) :
    (∑ i ∈ range N, f i) ≡ (∑ i ∈ range N, g i) [MOD m] := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ]
    exact (ih (fun i hi => h i (by omega))).add (h N (by omega))

private theorem shift_mod (a : ℕ→ℕ) (t U : ℕ) :
    (∑ j ∈ range U, if t≤j then a (j-t) * 2^j else 0) ≡
      (∑ i ∈ range U, a i * 2^(i+t)) [MOD 2^U] := by
  calc
    _ = ∑ i ∈ range U, if i+t<U then a i * 2^(i+t) else 0 := by
      rw [Finset.sum_ite, Finset.sum_ite]
      simp only [sum_const_zero,add_zero]
      apply Finset.sum_bij' (fun j _ => j-t) (fun i _ => i+t)
      · intro j hj; simp only [mem_filter,mem_range] at *; omega
      · intro i hi; simp only [mem_filter,mem_range] at *; omega
      · intro i hi; simp only [mem_filter,mem_range] at *; omega
      · intro i hi; omega
      · intro i hi
        have hp := (mem_filter.mp hi).2
        simp [Nat.sub_add_cancel hp]
    _ ≡ _ [MOD 2^U] := by
      apply sum_congr_mod
      intro i hi
      split
      · rfl
      · rename_i h
        apply Nat.ModEq.symm; apply Nat.modEq_zero_iff_dvd.mpr
        exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow _ (by omega)) _

private theorem diagonal_sum (c : ℕ→ℕ) (L U : ℕ) (fits : ∀ i<U, c i<2^L) :
    (∑ j ∈ range U, diagonal c L j * 2^j) ≡
      (∑ i ∈ range U, c i * 2^i) [MOD 2^U] := by
  have hval (j) : diagonal c L j * 2^j =
      ∑ t ∈ range L, if t≤j then ((c (j-t)).testBit t).toNat*2^j else 0 := by
    rw [diagonal,card_filter,Finset.sum_mul]
    apply sum_congr rfl; intro t _
    by_cases h : t≤j
    · simp only [h,true_and,if_true]; cases (c (j-t)).testBit t <;> simp
    · simp [h]
  simp_rw [hval]
  rw [sum_comm]
  calc
    _ ≡ (∑ t ∈ range L, ∑ i ∈ range U, ((c i).testBit t).toNat*2^(i+t)) [MOD 2^U] :=
      sum_congr_mod (fun t _ => shift_mod (fun i => ((c i).testBit t).toNat) t U)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl; intro i hi
      conv_rhs => rw [← pack_bits (fits i (mem_range.mp hi)),Finset.sum_mul]
      apply sum_congr rfl; intro j _
      rw [pow_add]; ring

private theorem blocks_sum (a : ℕ→ℕ) (k n : ℕ) :
    (∑ i ∈ range n, (∑ s ∈ range k, a (i*k+s)*2^s)*2^(i*k)) =
      ∑ j ∈ range (n*k), a j*2^j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,ih,Nat.succ_mul,Finset.sum_range_add,Finset.sum_mul]
    congr 1
    apply sum_congr rfl
    intro s _
    rw [pow_add];ring

private theorem words_sum (c : ℕ→ℕ) {U L k : ℕ} (hk : 0<k) :
    lowWord c U L k + highWord c U L k = ∑ j ∈ range U, diagonal c L j*2^j := by
  unfold lowWord highWord digits
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  calc
    _ = ∑ i ∈ range U, block c U L k (i*k)*2^(i*k) := by
      apply sum_congr rfl; intro i _
      rw [← mul_assoc,← add_mul,Nat.mod_add_div]
    _ = ∑ j ∈ range (U*k), (if j<U then diagonal c L j else 0)*2^j :=
      blocks_sum (fun j => if j<U then diagonal c L j else 0) k U
    _ = _ := by
      have hU := Nat.le_mul_of_pos_right U hk
      rw [← Nat.add_sub_of_le hU,Finset.sum_range_add]
      simp [show ∀ x, ¬U+x<U by intro;omega]
      exact sum_congr rfl (fun i hi => if_pos (mem_range.mp hi))

theorem sum_bit (f : ℕ→ℕ) {U rows L k j : ℕ} (hk : 0<k) (hr : rows<2^L)
    (hj : j<U) (fits : ∀r<rows, f r<2^U) :
    (lowWord (column f rows) U L k + highWord (column f rows) U L k).testBit j =
      (Readout.prefixSum f rows).testBit j := by
  have he := diagonal_sum (column f rows) L U (fun i _ => (column_le _ _ _).trans_lt hr)
  rw [column_sum _ rows U fits] at he
  rw [words_sum _ hk]
  have hb := congrArg (fun x : ℕ => x.testBit j) he
  simpa [Nat.testBit_mod_two_pow,hj] using hb

end DiophantineNP.HABSumBlocks
