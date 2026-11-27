import DiophantineNP.ShortResidue

/-! # Choosing block parameters inside a fixed finite formula for iterated addition

For sufficiently large U the block width k and radix B = 2^k satisfy two
inequalities. Each column count (including U) fits in B bits, and the k B²
possible triples used to count a single block fit in the universe. A formula
selects the least admissible k so that different bit queries use the same radix.
-/
namespace DiophantineNP.HABSumParameters
open Counting PrimeFormula WidthFormula FiniteArithmeticGap ShortResidue
open ShortResidue.Predicate

/-- The finite domain need only compare with the first missing power of two. -/
def Eligible (U k : ℕ) : Prop :=
  0 < k ∧ k * 2^k * 2^k < U ∧ U ≤ 2^(2^k - 1)

private theorem exponential_bound (k : ℕ) (h : 5 ≤ k) : 4*k+5 ≤ 2^k := by
  induction k,h using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ]; omega

private theorem eligible_large {U : ℕ} (hU : 2^20 ≤ U) : ∃ k, Eligible U k := by
  have h20 : 20 ≤ U.log2 := (Nat.le_log2 (by omega)).2 hU
  let k := U.log2/4
  have hk : 5 ≤ k := by dsimp [k]; omega
  have hexp := exponential_bound k hk
  have hlog : U.log2+1 ≤ 4*k+4 := by dsimp [k]; omega
  have bound : k*2^k*2^k < 2^(4*k) := calc
    k*2^k*2^k < 2^k*2^k*2^k := Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.two_pow_pos k)) (Nat.two_pow_pos k)
    _ ≤ 2^(4*k) := by rw [←pow_add,←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨k,by omega,bound.trans_le ((Nat.pow_le_pow_right (by decide) (by dsimp [k]; omega)).trans
      (Nat.log2_self_le (by omega : U≠0))),?_⟩
  exact Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))

/-- Only the first 1024 universe sizes need the fixed-row fallback. -/
theorem eligible_exists {U : ℕ} (hU : 1024<U) : ∃ k, Eligible U k := by
  by_cases hl : 2^20 ≤ U
  · exact eligible_large hl
  by_cases h : U ≤ 2^15
  · refine ⟨4,by decide,?_,?_⟩ <;> norm_num at * <;> omega
  · refine ⟨5,by decide,?_,?_⟩ <;> norm_num at * <;> omega

theorem eligible_fits {U k : ℕ} (h : Eligible U k) :
    k<U ∧ 2^k<U ∧ U<2^(2^k) ∧ 2*k<U := by
  obtain ⟨hk,hc,hw⟩ := h
  have hb : 1 < 2^k := one_lt_pow₀ (by decide) (by omega)
  have a : k ≤ k*2^k := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)
  have b : k*2^k ≤ k*2^k*2^k := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)
  have c : 2^k ≤ k*2^k := Nat.le_mul_of_pos_left _ hk
  have d := Nat.mul_le_mul_left k (by omega : 2≤2^k)
  refine ⟨by omega,by omega,hw.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega)),by omega⟩

def powAt (x y : ℕ) : Predicate where
  syntaxF σ := fromFormula (powerAt (σ y) (σ x))
  holds _ _ e := e y=2^(e x)
  valid _ _ _ := by rw [fromFormula_eval,powerAt_spec]

def bit (x i : ℕ) : Predicate where
  syntaxF σ := fromFormula (bitAt (σ x) (σ i))
  holds _ _ e := (e x).testBit (e i) = true
  valid _ _ _ := by rw [fromFormula_eval,bitAt_eval]

/-- Rename the free named variables of a predicate. Its binders remain local. -/
def reindex (p : Predicate) (f : ℕ → ℕ) : Predicate where
  syntaxF σ := p.syntaxF (σ ∘ f)
  holds U t e := p.holds U t (e ∘ f)
  valid σ t env := p.valid (σ ∘ f) t env

local infixr:35 " ⋀ " => Predicate.both

private def raw : Predicate :=
  (eqN 0 0).neg ⋀ powAt 0 1 ⋀ ex 2 (mul 0 1 2 ⋀ ex 3 (mul 2 1 3)) ⋀
    ex 4 (eqN 4 1 ⋀ ex 5 (add 5 4 1 ⋀ (ex 6 (powAt 5 6)).neg))

private theorem raw_iff (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (hb : e 1<U) :
    raw.holds U t e ↔ e 1 = 2^(e 0) ∧ Eligible U (e 0) := by
  simp [raw,both,ex,eqN,neg,powAt,mul,add,Function.update]
  constructor
  · rintro ⟨h0,hp,⟨_,hc⟩,_,z,_,hz,hw⟩
    refine ⟨hp,by omega,by simpa [←hp] using hc,?_⟩
    simpa [←hp,←hz] using hw
  · rintro ⟨hp,hk,hc,hw⟩
    rw [←hp] at hc hw
    have hb0 : 0<e 1 := hp ▸ Nat.two_pow_pos _
    have hpart := Nat.le_mul_of_pos_right (e 0*e 1) hb0
    exact ⟨by omega,hp,⟨by omega,hc⟩,by omega,e 1-1,by omega,by omega,hw⟩

/-- A fixed predicate on a proposed width and radix. -/
def good (k b : ℕ) := reindex raw (fun i => if i=0 then k else b)

theorem good_iff (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (k b : ℕ) (hb : e b<U) :
    (good k b).holds U t e ↔ e b=2^(e k) ∧ Eligible U (e k) := by
  simpa [good,reindex,Function.comp_def] using
    raw_iff U t (e ∘ (fun i => if i=0 then k else b)) (by simpa [Function.comp_def] using hb)

private def leastRaw : Predicate :=
  good 0 1 ⋀ (ex 2 (lt 2 0 ⋀ ex 3 (good 2 3))).neg

def selected (k b : ℕ) : Predicate := reindex leastRaw (fun i => if i=0 then k else b)

theorem selected_iff (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (k b : ℕ) (hb : e b<U) :
    (selected k b).holds U t e ↔
      e b=2^(e k) ∧ Eligible U (e k) ∧ ∀ l, Eligible U l → e k ≤ l := by
  let a := e ∘ (fun i => if i=0 then k else b)
  change leastRaw.holds U t a ↔ _
  change ((good 0 1).holds U t a ∧ ¬(ex 2 (lt 2 0 ⋀ ex 3 (good 2 3))).holds U t a) ↔ _
  rw [good_iff U t a 0 1 (by simpa [a] using hb)]
  simp only [ex,both,lt,Function.update_self]
  have hh (l m : ℕ) (hm : m<U) : (good 2 3).holds U t (Function.update (Function.update a 2 l) 3 m) ↔
      m=2^l ∧ Eligible U l := by
    simpa [Function.update] using good_iff U t (Function.update (Function.update a 2 l) 3 m) 2 3
      (by simpa [Function.update] using (hm : m<U))
  simp only [a,Function.comp_apply,if_pos,one_ne_zero,Function.update_of_ne (by decide : (0:ℕ)≠2)]
  constructor
  · rintro ⟨⟨h,hg⟩,hn⟩
    refine ⟨h,hg,fun l hl => ?_⟩
    by_contra! hlt
    obtain ⟨hlU,hmU,_,_⟩ := eligible_fits hl
    apply hn ⟨l,hlU,hlt,2^l,hmU,?_⟩
    exact (hh l _ hmU).2 ⟨rfl,hl⟩
  · rintro ⟨h,hg,hmin⟩
    refine ⟨⟨h,hg⟩,?_⟩
    rintro ⟨l,hlU,hlt,m,hmU,hm⟩
    exact (Nat.not_lt_of_le (hmin l ((hh l m hmU).1 hm).2)) hlt

end DiophantineNP.HABSumParameters
