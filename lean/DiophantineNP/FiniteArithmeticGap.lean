import DiophantineNP.WidthFormulaSubstitution
import Mathlib.Data.Nat.Factors

/-! # Native numerical BIT from arithmetic and unary strict majority

For a power of two, its exponent is the number of smaller powers of two.
These smaller powers lie in the lower half of the universe. A disjoint
upper suffix pads a strict-majority count to compare that number with a
given index. The formula then tests parity of an ordinary quotient.
-/
namespace DiophantineNP.FiniteArithmeticGap
open Counting PrimeFormula WidthFormula Finset

private def orF {k : ℕ} (a b : Formula k) : Formula k := .disj a b
private theorem orF_spec {k U : ℕ} (a b : Formula k) (env : Fin k → Fin U) :
    (orF a b).eval env = true ↔ a.eval env = true ∨ b.eval env = true := by
  simp [orF, Formula.eval]

/-- Positive powers of two, including 1, have no prime divisor exceeding two. -/
def powerOfTwo {k : ℕ} (x : Fin k) : Formula k :=
  andF (atLeast 1 x) (notF (.ex (andF (prime 0) (andF (atLeast 3 0)
    (.ex (mulF (0 : Fin (k+1)).succ 0 (up2 x)))))))

theorem powerOfTwo_spec {k U : ℕ} (x : Fin k) (env : Fin k → Fin U) :
    (powerOfTwo x).eval env = true ↔ ∃ h : ℕ, (env x).val = 2^h := by
  simp only [powerOfTwo, andF_spec, atLeast_true, notF_spec, exists_true, prime_true, mulF_spec,
    Fin.cases_zero, Fin.cases_succ]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) ?_⟩
    intro p hp hdiv
    by_contra hne
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    obtain ⟨t,ht⟩ := hdiv
    have hpU : p < U := (Nat.le_of_dvd (by omega) (show p ∣ (env x).val from ⟨t,ht⟩)).trans_lt (env x).isLt
    have htU : t < U := by
      have := Nat.le_mul_of_pos_left t hp.pos
      omega
    exact h ⟨⟨p,hpU⟩,hp,hp3,⟨t,htU⟩,ht.symm⟩
  · rintro ⟨h,he⟩
    refine ⟨by rw [he]; exact Nat.two_pow_pos _, ?_⟩
    rintro ⟨p,hp,hp3,m,hm⟩
    have hd : p.val ∣ 2^h := ⟨m.val,he ▸ hm.symm⟩
    have ht := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
    omega

private theorem count_fin_eq (U : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    count (fun j : Fin U => decide (P j.val)) = ((Finset.range U).filter P).card := by
  unfold count
  apply Finset.card_bij (fun j _ => j.val)
  · intro j hj
    simpa using And.intro j.isLt (show P j.val by simpa using hj)
  · intro _ _ _ _ h
    exact Fin.ext h
  · intro a ha
    obtain ⟨hl,hp⟩ := Finset.mem_filter.mp ha
    exact ⟨⟨a, Finset.mem_range.mp hl⟩, by simpa using hp, rfl⟩

private theorem tail_card (U t : ℕ) :
    ((Finset.range U).filter (fun x => t ≤ x)).card = U-t := by
  have he : (Finset.range U).filter (fun x => t ≤ x) = Finset.Ico t U := by
    ext j
    simp [and_comm]
  rw [he, Nat.card_Ico]

private def cut (U : ℕ) : ℕ := U - U / 2

/-- The upper half begins where the suffix ceases to be a strict majority. -/
private def upper {k : ℕ} (x : Fin k) : Formula k :=
  .neg (.maj (.atom (.leq x.succ 0)))

private theorem upper_true {k U : ℕ} (x : Fin k) (env : Fin k → Fin U) :
    (upper x).eval env = true ↔ cut U ≤ (env x).val := by
  change (!decide (U/2 < count (fun z : Fin U => decide ((env x).val ≤ z.val)))) = true ↔ _
  rw [count_fin_eq, tail_card]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  unfold cut
  omega

private def pad {k : ℕ} (z j : Fin k) : Formula k :=
  .ex (andF (upper 0) (addF 0 j.succ z.succ))

private theorem pad_spec {k U : ℕ} (z j : Fin k) (env : Fin k → Fin U) :
    (pad z j).eval env = true ↔ cut U + (env j).val ≤ (env z).val := by
  simp only [pad, exists_true, andF_spec, upper_true, addF_spec, Fin.cases_zero, Fin.cases_succ]
  constructor
  · rintro ⟨v,h,e⟩; omega
  · intro h
    exact ⟨⟨(env z).val-(env j).val, by have := (env z).isLt; omega⟩,by dsimp; omega,by dsimp; omega⟩

private def low {k : ℕ} (extra : Bool) (z p : Fin k) : Formula k :=
  let a := andF (powerOfTwo z) (ltF z p)
  if extra then orF (isNat 0 z) a else a

private def rank {k : ℕ} (extra : Bool) (p j : Fin k) : Formula k :=
  .maj (orF (low extra 0 p.succ) (pad 0 j.succ))

private def smallPowers (h : ℕ) := (range h).image (fun e => (2:ℕ)^e)

private theorem mem_small (h z : ℕ) :
    z ∈ smallPowers h ↔ (∃ e : ℕ, z = 2^e) ∧ z < 2^h := by
  simp only [smallPowers, mem_image, mem_range]
  constructor
  · rintro ⟨e,he,rfl⟩
    exact ⟨⟨_,rfl⟩,Nat.pow_lt_pow_right (by decide) he⟩
  · rintro ⟨⟨e,rfl⟩,he⟩
    exact ⟨e,lt_of_not_ge (fun hh => he.not_ge (Nat.pow_le_pow_right (by decide) hh)),rfl⟩

private theorem card_small (h : ℕ) : (smallPowers h).card = h := by
  rw [smallPowers, card_image_of_injective, card_range]
  exact (pow_right_strictMono₀ (by decide : 1<(2:ℕ))).injective

private theorem small_lower {U h z : ℕ} (hU : 2^h < U) (hz : z ∈ smallPowers h) : z < cut U := by
  obtain ⟨e,he,eq⟩ := mem_image.mp hz
  have hh : e<h := mem_range.mp he
  have h : 2^(e+1) ≤ (2:ℕ)^h := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ,eq] at h
  unfold cut
  omega

private def paddedLow (extra : Bool) (h : ℕ) : Finset ℕ :=
  if extra then insert 0 (smallPowers h) else smallPowers h

private theorem card_paddedLow (extra : Bool) (h : ℕ) : (paddedLow extra h).card = h+extra.toNat := by
  have hn : 0 ∉ smallPowers h := by
    intro hv
    obtain ⟨⟨e,he⟩,_⟩ := (mem_small h 0).mp hv
    have : 0<(2:ℕ)^e := by positivity
    omega
  cases extra <;> simp [paddedLow,hn,card_small]

private theorem padded_lower {U h z : ℕ} (extra : Bool) (hU : 2^h<U) (hz : z ∈ paddedLow extra h) : z < cut U := by
  cases extra with
  | false => exact small_lower hU hz
  | true =>
    rcases mem_insert.mp hz with hz|hz
    · have : 0 < (2:ℕ)^h := Nat.two_pow_pos _
      unfold cut; omega
    · exact small_lower hU hz

private theorem low_spec {k U h : ℕ} (extra : Bool) (z p : Fin k) (env : Fin k → Fin U) (he : (env p).val=2^h) :
    (low extra z p).eval env = true ↔ (env z).val ∈ paddedLow extra h := by
  cases extra <;> simp [low,orF_spec,isNat_spec,andF_spec,powerOfTwo_spec,ltF_true,paddedLow,mem_small,he]

private theorem rank_spec {k U h : ℕ} (extra : Bool) (p j : Fin k) (env : Fin k → Fin U)
    (hp : (env p).val=2^h) (hj : (env j).val ≤ U/2) :
    (rank extra p j).eval env = true ↔ (env j).val < h+extra.toNat := by
  let t := cut U + (env j).val
  let S := paddedLow extra h
  have hU : 2^h < U := hp ▸ (env p).isLt
  have hlt : ∀ z ∈ S, z < cut U := fun z hz => padded_lower extra hU hz
  have hu : cut U ≤ U := Nat.sub_le _ _
  have ht : t ≤ U := by dsimp [t,cut]; omega
  have hfun : (fun v : Fin U => (orF (low extra 0 p.succ) (pad 0 j.succ)).eval (Fin.cases v env)) =
      fun v => decide (v.val ∈ S ∨ t ≤ v.val) := by
    funext v
    apply Bool.eq_iff_iff.mpr
    rw [orF_spec, low_spec extra _ _ _ (by simpa only [Fin.cases_succ] using hp),pad_spec,decide_eq_true_eq]
    rfl
  change decide (U/2 < count _) = true ↔ _
  rw [hfun,count_fin_eq U (fun z => z ∈ S ∨ t ≤ z),decide_eq_true_eq]
  have hsets : (range U).filter (fun z => z ∈ S ∨ t ≤ z) = S ∪ Ico t U := by
    ext z
    simp only [mem_filter, mem_range, mem_union, mem_Ico]
    constructor
    · rintro ⟨hz,h|h⟩
      · exact Or.inl h
      · exact Or.inr ⟨h,hz⟩
    · rintro (h|⟨ha,hb⟩)
      · exact ⟨(hlt z h).trans_le hu,Or.inl h⟩
      · exact ⟨hb,Or.inr ha⟩
  have hd : Disjoint S (Ico t U) := by
    apply disjoint_left.mpr
    intro z hz ht'
    have := hlt z hz
    have := (mem_Ico.mp ht').1
    dsimp [t] at *
    omega
  rw [hsets,card_union_of_disjoint hd,Nat.card_Ico,card_paddedLow]
  dsimp [t,cut]
  omega

/-- The graph of `p = 2^j`, including the smallest finite universes. -/
def powerAt {k : ℕ} (p j : Fin k) : Formula k :=
  andF (powerOfTwo p) (andF (.ex (addF j.succ j.succ 0))
    (andF (rank true p j) (notF (rank false p j))))

private theorem twice_le_pow (j : ℕ) : 2*j ≤ 2^j := by
  induction j with
  | zero => decide
  | succ j ih =>
    cases j with
    | zero => decide
    | succ i =>
      rw [pow_succ]
      omega

theorem powerAt_spec {k U : ℕ} (p j : Fin k) (env : Fin k → Fin U) :
    (powerAt p j).eval env = true ↔ (env p).val = 2^(env j).val := by
  simp only [powerAt,andF_spec,powerOfTwo_spec,exists_true,addF_spec,Fin.cases_succ,Fin.cases_zero,notF_spec]
  constructor
  · rintro ⟨⟨h,hp⟩,⟨t,ht⟩,hl,hr⟩
    have hh : (env j).val≤U/2 := by have := t.isLt; omega
    have h1 := (rank_spec true p j env hp hh).mp hl
    have h2 := mt (rank_spec false p j env hp hh).mpr hr
    simp at h1 h2
    rwa [show (env j).val = h by omega]
  · intro hp
    have ht : (env j).val+(env j).val < U := by
      have := twice_le_pow (env j).val
      have := (env p).isLt
      omega
    have hh : (env j).val≤U/2 := by omega
    exact ⟨⟨_,hp⟩,⟨⟨_,ht⟩,rfl⟩,(rank_spec true p j env hp hh).mpr (by simp),
      fun h => by simpa using (rank_spec false p j env hp hh).mp h⟩

private def quotient {k : ℕ} (x p q : Fin k) : Formula k :=
  .ex (.ex (andF (mulF (up2 p) (up2 q) (0 : Fin (k+1)).succ)
    (andF (ltF 0 (up2 p)) (addF (0 : Fin (k+1)).succ 0 (up2 x)))))

private theorem quotient_spec {k U : ℕ} (x p q : Fin k) (env : Fin k → Fin U)
    (hp : 0 < (env p).val) :
    (quotient x p q).eval env = true ↔ (env q).val = (env x).val / (env p).val := by
  simp only [quotient,exists_true,andF_spec,mulF_spec,ltF_true,addF_spec,Fin.cases_succ,Fin.cases_zero]
  constructor
  · rintro ⟨m,r,hm,hr,hx⟩
    have e : (env x).val = r.val+(env p).val*(env q).val := by omega
    rw [e,Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt hr, Nat.zero_add]
  · intro hq
    have hr := Nat.mod_lt (env x).val hp
    have he := Nat.div_add_mod (env x).val (env p).val
    rw [← hq] at he
    have hu := (env x).isLt
    exact ⟨⟨(env p).val*(env q).val,by omega⟩,⟨(env x).val % (env p).val,by omega⟩,rfl,hr,he⟩

private def isOdd {k : ℕ} (q : Fin k) : Formula k := notF (.ex (addF 0 0 q.succ))

private theorem isOdd_spec {k U : ℕ} (q : Fin k) (env : Fin k → Fin U) :
    (isOdd q).eval env = true ↔ (env q).val%2 = 1 := by
  simp only [isOdd,notF_spec,exists_true,addF_spec, Fin.cases_zero, Fin.cases_succ]
  constructor
  · intro ha
    by_contra hn
    exact ha ⟨⟨(env q).val/2,by have := (env q).isLt; omega⟩,by dsimp; omega⟩
  · rintro hn ⟨v,hv⟩
    omega

/-- A concrete arithmetic/majority formula for the native binary digit. -/
def bitAt {k : ℕ} (x j : Fin k) : Formula k :=
  .ex (andF (powerAt 0 j.succ)
    (.ex (andF (quotient (up2 x) (0 : Fin (k+1)).succ 0) (isOdd 0))))

theorem bitAt_eval {k U : ℕ} (x j : Fin k) (env : Fin k → Fin U) :
    (bitAt x j).eval env = (env x).val.testBit (env j).val := by
  apply Bool.eq_iff_iff.mpr
  simp only [bitAt,exists_true,andF_spec,powerAt_spec, Fin.cases_succ,Fin.cases_zero]
  constructor
  · rintro ⟨p,hp,q,hquot,ho⟩
    have hpos : 0 < p.val := hp ▸ Nat.two_pow_pos _
    have hq := (quotient_spec _ _ _ _ hpos).mp hquot
    have hodd := (isOdd_spec _ _).mp ho
    simp only [Fin.cases_succ, Fin.cases_zero] at hq hodd
    rw [hp] at hq
    simpa [Nat.testBit_eq_decide_div_mod_eq,← hq] using hodd
  · intro hb
    have hh := Nat.ge_two_pow_of_testBit hb
    let p : Fin U := ⟨2^(env j).val, hh.trans_lt (env x).isLt⟩
    let q : Fin U := ⟨(env x).val/p.val, (Nat.div_le_self _ _).trans_lt (env x).isLt⟩
    refine ⟨p,rfl,q,(quotient_spec _ _ _ _ (show 0<p.val from Nat.two_pow_pos _)).mpr rfl,
      (isOdd_spec _ _).mpr ?_⟩
    simpa [Nat.testBit_eq_decide_div_mod_eq,p,q] using hb

/-- The binary-matrix arithmetic facts are the remaining finite-logic input.
The product and sum results need only their low U bits, even on overflow. -/
structure IteratedArithmetic where
  product : Template 1
  sum : Template 1
  product_correct {U : ℕ} (f : ℕ → ℕ) (fits : ∀ t<U, f t<2^U) (j : Fin U) :
    product.eval (fun r c => (f r.val).testBit c.val) (fun _ => j) = (productPrefix f U).testBit j.val
  sum_correct {U : ℕ} (f : ℕ → ℕ) (fits : ∀ t<U, f t<2^U) (j : Fin U) :
    sum.eval (fun r c => (f r.val).testBit c.val) (fun _ => j) = (Readout.prefixSum f U).testBit j.val

def IteratedArithmetic.toLiterature (A : IteratedArithmetic) : LiteratureFormulas where
  nativeBit := bitAt 0 1
  bit_correct := fun x j => bitAt_eval 0 1 (pairEnv x j)
  product := A.product
  sum := A.sum
  product_correct := A.product_correct
  sum_correct := A.sum_correct

theorem IteratedArithmetic.widthDescriptions (A : IteratedArithmetic) : Packing.WidthDescriptions :=
  widthDescriptions_of_literature A.toLiterature

end DiophantineNP.FiniteArithmeticGap
