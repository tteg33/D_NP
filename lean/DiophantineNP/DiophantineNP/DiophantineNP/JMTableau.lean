import DiophantineNP.Statement
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Fixed-width bit masks for register-machine tableaux

Columns are successive configurations, starting at the low-order digit. A radix
`2^w` makes masking a digitwise relation. The selectors below treat the carry
in the halving mask on p. 827 of Jones and Matiyasevich (1984).
-/
namespace DiophantineNP.JMTableau

/-- Pack a fixed number of columns with the first column least significant. -/
def pack (q : ℕ) : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | _+1, a => q*pack q (fun i => a i.succ) + a 0

theorem mask_append_iff (w a b x y : ℕ) (ha : a < 2^w) (hb : b < 2^w) :
    BitIncl (2^w*x+a) (2^w*y+b) ↔ BitIncl a b ∧ BitIncl x y := by
  have low {u v : ℕ} (hu : u < 2^w) (i : ℕ) (hi : i < w) :
      (2^w*v+u).testBit i = u.testBit i := by
    simp [Nat.testBit_two_pow_mul_add _ hu, hi]
  have high {u v : ℕ} (hu : u < 2^w) (i : ℕ) :
      (2^w*v+u).testBit (i+w) = v.testBit i := by
    simp [Nat.testBit_two_pow_mul_add _ hu, Nat.not_lt.mpr (Nat.le_add_left _ _)]
  constructor
  · intro h
    constructor
    · intro i hi
      have hbit := Nat.testBit_mod_two_pow a w i
      rw [Nat.mod_eq_of_lt ha,hi] at hbit
      have hil : i < w := by simpa using hbit.symm
      exact (low hb i hil) ▸ h i ((low ha i hil).symm ▸ hi)
    · intro i hi
      exact (high hb i) ▸ h (i+w) ((high ha i).symm ▸ hi)
  · rintro ⟨h1,h2⟩ i hi
    by_cases hl : i < w
    · rw [low ha i hl] at hi
      rw [low hb i hl]
      exact h1 _ hi
    · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hl)
      rw [Nat.add_comm w t] at hi ⊢
      rw [high ha] at hi
      rw [high hb]
      exact h2 _ hi

/-- One packed bitwise inclusion is equivalent to one bit mask in every column. -/
theorem mask_pack_iff {w n : ℕ} (a b : Fin n → ℕ)
    (ha : ∀ i, a i < 2^w) (hb : ∀ i, b i < 2^w) :
    BitIncl (pack (2^w) a) (pack (2^w) b) ↔ ∀ i, BitIncl (a i) (b i) := by
  induction n with
  | zero => simp [pack,BitIncl]
  | succ n ih =>
    rw [pack, pack, mask_append_iff _ _ _ _ _ (ha 0) (hb 0), ih _ _ (fun i => ha i.succ) (fun i => hb i.succ)]
    exact ⟨fun ⟨h,t⟩ => Fin.cases h t, fun h => ⟨h 0,fun i => h i.succ⟩⟩

theorem pack_add {n : ℕ} (q : ℕ) (a b : Fin n → ℕ) :
    pack q (fun i => a i+b i) = pack q a+pack q b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pack,ih]; ring

theorem pack_scale {n : ℕ} (q c : ℕ) (a : Fin n → ℕ) :
    pack q (fun i => c*a i) = c*pack q a := by
  induction n with
  | zero => simp [pack]
  | succ n ih => simp only [pack,ih]; ring

theorem pack_sum {n s : ℕ} (q : ℕ) (a : Fin s → Fin n → ℕ) :
    (∑ j, pack q (a j)) = pack q (fun t => ∑ j, a j t) := by
  induction s with
  | zero =>
    have hz := pack_scale (n:=n) q 0 (fun _ => 0)
    simpa using hz.symm
  | succ s ih =>
    rw [Fin.sum_univ_succ,ih (fun j => a j.succ)]
    simp only [Fin.sum_univ_succ (fun j => a j _)]
    exact (pack_add _ _ _).symm

theorem pack_sub {n : ℕ} (q : ℕ) (a b : Fin n → ℕ) (h : ∀ i, b i ≤ a i) :
    pack q (fun i => a i-b i) = pack q a-pack q b := by
  have eqn : (fun i => a i-b i+b i) = a := funext (fun i => Nat.sub_add_cancel (h i))
  have := pack_add q (fun i => a i-b i) b
  rw [eqn] at this
  omega

theorem pack_lt_power {w t : ℕ} (a : Fin t → ℕ) (ha : ∀ i, a i < 2^w) :
    pack (2^w) a < (2^w)^t := by
  induction t with
  | zero => simp [pack]
  | succ n ih =>
    have h := ih (fun i => a i.succ) (fun i => ha i.succ)
    have hh := Nat.mul_le_mul_left (2^w) (show pack (2^w) (fun i => a i.succ)+1 ≤ (2^w)^n by omega)
    have := ha 0
    rw [Nat.mul_add,Nat.mul_one] at hh
    rw [pack,pow_succ,Nat.mul_comm ((2^w)^n)]
    omega

/-- `n` radix-`2^w` digits need at most `n*w+1` bits, including the zero case. -/
theorem pack_bits {w n : ℕ} (a : Fin n → ℕ) (ha : ∀ i, a i < 2^w) :
    bits (pack (2^w) a) ≤ w*n+1 := by
  by_cases hz : pack (2^w) a = 0
  · simp [hz,bits]
  · exact Nat.succ_le_succ ((Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
      ((Nat.log2_self_le hz).trans (by simpa [pow_mul] using (pack_lt_power a ha).le)))

private theorem mask_top {a w : ℕ} (ha : a < 2^w) : BitIncl a (2^w-1) := by
  rw [bitIncl_iff_and,Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt ha]

private theorem mask_self (a : ℕ) : BitIncl a a := fun _ h => h

private theorem mask_le {a b : ℕ} (h : BitIncl a b) : a ≤ b := by
  rw [← (bitIncl_iff_and a b).mp h]
  exact Nat.and_le_right

/-- The masks for a single active lane recover the quotient on both even and odd values. -/
theorem half_lane (r j : ℕ) :
    BitIncl (2*j) r ∧ BitIncl r (2*j+1) ↔ j = r/2 := by
  have er : 2*(r/2)+r%2 = r := Nat.div_add_mod r 2
  have lowR : r%2 < 2^1 := by omega
  have h0 := mask_append_iff 1 0 (r%2) j (r/2) (by decide) lowR
  have h1 := mask_append_iff 1 (r%2) 1 (r/2) j lowR (by decide)
  norm_num [er] at h0 h1
  constructor
  · rintro ⟨hl,hu⟩
    exact Nat.le_antisymm (mask_le ((h0.mp hl).2)) (mask_le ((h1.mp hu).2))
  · rintro rfl
    refine ⟨h0.mpr ⟨?_,mask_self _⟩, h1.mpr ⟨?_,mask_self _⟩⟩
    · simp [BitIncl]
    · exact mask_top (w:=1) lowR



/-- The corrected three-mask system for the contribution subtracted by a
ceiling-half operation. `I` is the word of ones and `L` selects its times. -/
def halfConditions (q I L R J : ℕ) : Prop :=
  BitIncl (2*J) R ∧ BitIncl J ((q/2-1)*L) ∧ BitIncl R ((q-1)*(I-L)+2*J+L)

/-- Corrected (49) holds exactly for the packed floor-half contribution (50).
The first and third masks allow the parity bit to vary at active times. -/
theorem halfConditions_iff {w n : ℕ} (r j : Fin n → ℕ) (on : Fin n → Bool)
    (hr : ∀ i, r i < 2^(w+1)) (hj : ∀ i, j i < 2^(w+1)) :
    let q := 2^(w+1)
    let L := pack q (fun i => if on i then 1 else 0)
    halfConditions q (pack q (fun _ : Fin n => 1)) L (pack q r) (pack q j) ↔
      ∀ i, j i = if on i then r i/2 else 0 := by
  let q := 2^(w+1)
  let h := 2^w
  let l (i : Fin n) : ℕ := if on i then 1 else 0
  have hq : q = 2*h := by dsimp [q,h]; rw [pow_succ,mul_comm]
  have hh : 0 < h := Nat.two_pow_pos _
  have hl (i : Fin n) : l i ≤ 1 := by unfold l; split <;> decide
  have hhigh (i : Fin n) : (h-1)*l i < q := by
    unfold l; split <;> simp <;> omega
  have hmask : BitIncl (pack q j) ((q/2-1)*pack q l) ↔
      ∀ i, BitIncl (j i) ((h-1)*l i) := by
    rw [show q/2 = h by omega, ← pack_scale]
    exact mask_pack_iff _ _ hj hhigh
  change halfConditions q (pack q _) (pack q l) (pack q r) (pack q j) ↔ _
  unfold halfConditions
  have upper (hsmall : ∀ i, BitIncl (j i) ((h-1)*l i)) :
      (BitIncl (2*pack q j) (pack q r) ∧
       BitIncl (pack q r) ((q-1)*(pack q (fun _ : Fin n => 1)-pack q l)+2*pack q j+pack q l)) ↔
       ∀ i, BitIncl (2*j i) (r i) ∧ BitIncl (r i) ((q-1)*(1-l i)+2*j i+l i) := by
    have hd (i : Fin n) : 2*j i < q := by
      have hj' := mask_le (hsmall i)
      have hm := Nat.mul_le_mul_left (h-1) (hl i)
      simp only [Nat.mul_one] at hm
      omega
    have he (i : Fin n) : (q-1)*(1-l i)+2*j i+l i < q := by
      have he := mask_le (hsmall i)
      by_cases hi : on i
      · simp [l,hi] at he ⊢; omega
      · simp [l,hi] at he ⊢; omega
    rw [← pack_sub q _ l (fun i => hl i), ← pack_scale, ← pack_scale, ← pack_add, ← pack_add,
      mask_pack_iff _ _ hd hr, mask_pack_iff _ _ hr he]
    exact forall_and.symm
  constructor
  · rintro ⟨a,b,c⟩
    have hb := hmask.mp b
    have limits := (upper hb).mp ⟨a,c⟩
    intro i
    have v := limits i
    have he := mask_le (hb i)
    by_cases hi : on i
    · simp only [l,hi,if_true,Nat.sub_self,Nat.mul_zero,Nat.zero_add] at v ⊢
      exact (half_lane ..).mp v
    · simp [l,hi] at he ⊢; exact he
  · intro H
    have hb (i : Fin n) : BitIncl (j i) ((h-1)*l i) := by
      rw [H i]
      by_cases hi : on i
      · simp [l,hi]
        exact mask_top (w:=w) (by have := hr i; change r i < q at this; try omega)
      · simp [l,hi]; exact mask_self _
    have hu := (upper hb).mpr (fun i => by
      by_cases hi : on i
      · have hh' := H i
        simp only [hi,if_true] at hh'
        simpa [l,hi] using (half_lane (r i) (j i)).mpr hh'
      · have hh' := H i
        simp only [hi,Bool.false_eq_true,if_false] at hh'
        simp [l,hi,hh']
        exact ⟨by simp [BitIncl], mask_top (hr i)⟩)
    exact ⟨hu.1,hmask.mpr hb,hu.2⟩

/-- At times 0,1,2,3 the instructions are goto, ceiling-half, decrement, halt.
The register starting at 1 takes values 1,1,1,0. The honest floor-half
contribution is zero. Radix 64 also satisfies the paper's bound (46). -/
theorem printed_half_mask_counterexample :
    let q := 64
    let I := 1+q+q^2+q^3
    let L := q
    let R := 1+q+q^2
    2^3*(1+1) < q/2 ∧
    (∀ J : ℕ, ¬BitIncl R ((q-1)*(I-L)+2*J+I)) ∧
    halfConditions q I L R 0 := by
  dsimp
  refine ⟨by decide, ?_, ?_⟩
  · intro J hm
    have bad := hm 0 (by decide)
    rw [← Nat.mod_two_eq_one_iff_testBit_zero] at bad
    omega
  · unfold halfConditions
    simp only [bitIncl_iff_and]
    decide

/-- The three printed conditions in (49) can also admit an incorrect quotient.
The two lanes are inactive with register 0 and active with register 2. -/
theorem printed_half_mask_wrong_quotient :
    let q := 64
    let I := 1+q
    let L := q
    let R := 2*q
    let J := 0
    BitIncl (2*J) R ∧ BitIncl J ((q/2-1)*L) ∧
      BitIncl R ((q-1)*(I-L)+2*J+I) ∧ J ≠ (2/2)*q := by
  dsimp
  simp only [bitIncl_iff_and]
  decide

/-- The masked additions in (47) extract precisely the source register at
active times, as asserted in (48). -/
theorem addSelector_iff {w n : ℕ} (r a : Fin n → ℕ) (on : Fin n → Bool)
    (hr : ∀ i, r i < 2^w) (ha : ∀ i, a i < 2^w) :
    let q := 2^w
    let I := pack q (fun _ : Fin n => 1)
    let L := pack q (fun i => if on i then 1 else 0)
    let R := pack q r
    let A := pack q a
    (BitIncl A R ∧ BitIncl A ((q-1)*L) ∧ BitIncl R ((q-1)*(I-L)+A)) ↔
      ∀ i, a i = if on i then r i else 0 := by
  let q := 2^w
  let l (i : Fin n) : ℕ := if on i then 1 else 0
  have hq : 0 < q := Nat.two_pow_pos _
  have hl (i : Fin n) : l i ≤ 1 := by unfold l; split <;> decide
  have hL (i : Fin n) : (q-1)*l i < q := by unfold l; split <;> simp <;> omega
  change _ ∧ BitIncl (pack q a) ((q-1)*pack q l) ∧
    BitIncl (pack q r) ((q-1)*(pack q (fun _ => 1)-pack q l)+pack q a) ↔ _
  rw [← pack_scale, mask_pack_iff _ _ ha hr, mask_pack_iff _ _ ha hL,
      ← pack_sub q _ l (fun i => hl i), ← pack_scale, ← pack_add]
  have last (h : ∀ i, BitIncl (a i) ((q-1)*l i)) :
      BitIncl (pack q r) (pack q (fun i => (q-1)*(1-l i)+a i)) ↔
      ∀ i, BitIncl (r i) ((q-1)*(1-l i)+a i) := by
    apply mask_pack_iff _ _ hr
    intro i
    have hl' := mask_le (h i)
    by_cases hi : on i
    · simpa [l,hi] using ha i
    · simp [l,hi] at hl' ⊢; omega
  constructor
  · rintro ⟨h₁,h₂,h₃⟩ i
    have ha' := mask_le (h₂ i)
    have h := mask_le ((last h₂).mp h₃ i)
    by_cases hi : on i
    · simp [l,hi] at h ⊢
      exact Nat.le_antisymm (mask_le (h₁ i)) h
    · simpa [l,hi] using ha'
  · intro H
    have h₂ (i : Fin n) : BitIncl (a i) ((q-1)*l i) := by
      rw [H i]
      by_cases hi : on i
      · simpa [l,hi] using mask_top (hr i)
      · simp [l,hi,BitIncl]
    refine ⟨?_, h₂, (last h₂).mpr ?_⟩
    · intro i
      rw [H i]
      by_cases hi : on i <;> simp [hi,BitIncl]
    · intro i
      rw [H i]
      by_cases hi : on i
      · simpa [l,hi] using mask_self (r i)
      · simpa [l,hi] using mask_top (hr i)

/-- The shifted line mask (52) tests the next column. The two possible
destination indicators are disjoint, as they are for distinct machine lines. -/
theorem branch_iff {w n : ℕ} (hw : 0 < w) (src : Fin n → Bool)
    (left right : Fin (n+1) → Bool) (hd : ∀ i, ¬(left i = true ∧ right i = true)) :
    let q := 2^w
    let lane {m} (f : Fin m → Bool) := pack q (fun i => if f i then 1 else 0)
    BitIncl (q*lane src) (lane left + lane right) ↔
      ∀ i, src i = true → left i.succ = true ∨ right i.succ = true := by
  let q := 2^w
  let digit (b : Bool) : ℕ := if b then 1 else 0
  have hq : 1 < q := Nat.one_lt_two_pow (by omega)
  let s : Fin (n+1) → ℕ := Fin.cases 0 (fun i => digit (src i))
  have hs (i : Fin (n+1)) : s i < q := by
    refine Fin.cases (by simpa [s] using hq.le) (fun j => ?_) i
    simp only [s, Fin.cases_succ, digit]; split <;> omega
  have hmask (i : Fin (n+1)) : digit (left i) + digit (right i) < q := by
    have H := hd i
    cases h : left i <;> cases h' : right i <;> (simp_all [digit]; try omega)
  change BitIncl (q*pack q (fun i => digit (src i)))
    (pack q (fun i => digit (left i))+pack q (fun i => digit (right i))) ↔ _
  have hsrc : q*pack q (fun i => digit (src i)) = pack q s := by simp [pack,s]
  rw [hsrc, ← pack_add, mask_pack_iff _ _ hs hmask]
  have lane (x y z : Bool) (h : ¬(y=true ∧ z=true)) :
      BitIncl (digit x) (digit y+digit z) ↔ (x=true → y=true ∨ z=true) := by
    cases x <;> cases y <;> cases z <;> simp_all [digit,bitIncl_iff_and]
  constructor
  · intro H i
    exact (lane _ _ _ (hd i.succ)).1 (H i.succ)
  · intro H i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [s,BitIncl]
    · exact (lane _ _ _ (hd j.succ)).2 (H j)

/-- Bounded lane vectors have a unique packed representation. -/
theorem pack_eq_iff {w n : ℕ} (a b : Fin n → ℕ) (ha : ∀ i, a i < 2^w)
    (hb : ∀ i, b i < 2^w) :
    pack (2^w) a = pack (2^w) b ↔ a=b := by
  refine ⟨fun h => ?_, fun h => congrArg _ h⟩
  have h₁ := (mask_pack_iff a b ha hb).mp (h ▸ mask_self _)
  have h₂ := (mask_pack_iff b a hb ha).mp (h.symm ▸ mask_self _)
  exact funext (fun i => Nat.le_antisymm (mask_le (h₁ i)) (mask_le (h₂ i)))

private theorem pack_last {n : ℕ} (q : ℕ) (r : Fin (n+1) → ℕ) :
    pack q r = pack q (fun i : Fin n => r i.castSucc) + q^n*r (Fin.last n) := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    change q*pack q (fun i : Fin (n+1) => r i.succ)+r 0 =
      q*pack q (fun i : Fin n => r i.succ.castSucc)+r 0 + q^(n+1)*r (Fin.last (n+1))
    rw [ih (fun i => r i.succ),pow_succ]
    change q*(pack q (fun i : Fin n => r i.succ.castSucc)+q^n*r (Fin.last (n+1)))+r 0 = _
    ring

/-- With the final register zero, the whole-register equation in (38) and
(39) recovers the initial value and every individual register transition.
The last two hypotheses ensure that neither side carries into another lane. -/
theorem registerUpdate_iff {w n : ℕ} (r : Fin (n+1) → ℕ) (a b : Fin n → ℕ) (initial : ℕ)
    (hfinal : r (Fin.last n) = 0) (hi : initial < 2^w) (hstart : r 0 < 2^w)
    (hnext : ∀ i, r i.succ + b i < 2^w) (hprev : ∀ i, r i.castSucc + a i < 2^w) :
    let q := 2^w
    pack q r + q*pack q b = initial + q*(pack q r + pack q a) ↔
      r 0 = initial ∧ ∀ i, r i.succ+b i = r i.castSucc+a i := by
  let q := 2^w
  have hq : 0 < q := Nat.two_pow_pos _
  have hx : pack q r = q*pack q (fun i => r i.succ)+r 0 := rfl
  have hy : pack q r = pack q (fun i : Fin n => r i.castSucc) := by
    simpa [hfinal] using pack_last q r
  let z := fun i : Fin n => r i.succ+b i
  let y := fun i : Fin n => r i.castSucc+a i
  have hz : pack q r + q*pack q b = r 0+q*pack q z := by
    rw [hx,show pack q z = _ from pack_add q (fun i => r i.succ) b]; ring
  have hw : pack q r + pack q a = pack q y := by
    rw [hy]; exact (pack_add q _ _).symm
  change pack q r + q*pack q b = initial + q*(pack q r + pack q a) ↔ _
  rw [hz,hw]
  constructor
  · intro he
    have hlow := congrArg (fun x => x%q) he
    dsimp only at hlow
    rw [Nat.add_mul_mod_self_left,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hstart,Nat.mod_eq_of_lt hi] at hlow
    rw [hlow] at he
    have hu := Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel he)
    exact ⟨hlow, fun i => congrFun ((pack_eq_iff z y hnext hprev).mp hu) i⟩
  · rintro ⟨hl,hu⟩
    exact congrArg₂ (·+·) hl (congrArg (q*·) (congrArg (pack q) (funext hu)))

/-- A bound in terms of the radix suffices to decode an arbitrary guessed word.
The individual digits are its quotients modulo the radix. -/
theorem pack_digits {n q v : ℕ} (hq : 0 < q) (hv : v < q^n) :
    pack q (fun i : Fin n => v/q^i.val%q) = v := by
  induction n generalizing v with
  | zero => simpa [pack] using (show v = 0 by simpa using hv).symm
  | succ n ih =>
    rw [pack]
    have hd : v/q < q^n := (Nat.div_lt_iff_lt_mul hq).mpr (by simpa [pow_succ] using hv)
    have h := ih hd
    have e : (fun i : Fin n => v/q^i.succ.val%q) = (fun i : Fin n => (v/q)/q^i.val%q) := by
      funext i
      simp only [Fin.val_succ,Nat.div_div_eq_div_mul,pow_succ]
      rw [mul_comm (q^i.val)]
    rw [e,h]
    simpa using Nat.div_add_mod v q

/-- If an arbitrary witness masks a packed upper bound then it too is a
packed word with the same number of in-range digits. -/
theorem mask_unpack_iff {w n v : ℕ} (upper : Fin n → ℕ) (hu : ∀ i, upper i < 2^w) :
    BitIncl v (pack (2^w) upper) ↔
      ∃ digits : Fin n → ℕ, v = pack (2^w) digits ∧ ∀ i, BitIncl (digits i) (upper i) := by
  constructor
  · intro h
    let q := 2^w
    let digits (i : Fin n) := v/q^i.val%q
    have hd (i : Fin n) : digits i < q := Nat.mod_lt _ (Nat.two_pow_pos w)
    have he : pack q digits = v := pack_digits (Nat.two_pow_pos _) ((mask_le h).trans_lt (pack_lt_power _ hu))
    exact ⟨digits,he.symm,(mask_pack_iff _ _ hd hu).mp (he.symm ▸ h)⟩
  · rintro ⟨a,rfl,h⟩
    exact (mask_pack_iff _ _ (fun i => (mask_le (h i)).trans_lt (hu i)) hu).mpr h

/-- Register-line masks are one-hot in every column exactly when their
ordinary sum is the all-ones word. The strict line-count bound prevents carries. -/
theorem onehot_iff {w n m : ℕ} (lines : Fin m → Fin n → Bool) (hm : m < 2^w)
    (hw : 0 < w) :
    (∑ j, pack (2^w) (fun i => if lines j i then 1 else 0)) =
      pack (2^w) (fun _ : Fin n => 1) ↔
      ∀ i, (Finset.univ.filter (fun j => lines j i = true)).card = 1 := by
  let M := 2^w
  let flag (j : Fin m) (i : Fin n) : ℕ := if lines j i then 1 else 0
  have count (i : Fin n) :
      (∑ j, flag j i) = (Finset.univ.filter (fun j => lines j i = true)).card := by
    simp [flag,Finset.sum_boole]
  change (∑ j, pack M (flag j)) = _ ↔ _
  rw [pack_sum,pack_eq_iff]
  · rw [funext_iff]; simp_rw [count]
  · intro i
    exact ((count i).le.trans (Finset.card_filter_le _ _)).trans_lt (by simpa using hm)
  · exact fun _ => Nat.one_lt_two_pow (by omega)

/-- A concrete radix for (25) and (46) with polynomial binary length in the
input length, time bound and number of machine lines. -/
def laneWidth (x steps lines : ℕ) := steps + bits x + lines + 3

theorem honest_radix (x s m : ℕ) :
    let w := laneWidth x s m
    2^s*(x+1) < 2^w/2 ∧ m+1 < 2^w ∧ bits (2^w) = w+1 := by
  let n := s+bits x+m+2
  have hwidth : laneWidth x s m = n+1 := by rfl
  have hx : x+1 ≤ 2^(bits x) := Nat.lt_log2_self
  have hprod := Nat.mul_le_mul_left (2^s) hx
  rw [← pow_add] at hprod
  have hlarge : 2^(s+bits x) < 2^n :=
    Nat.pow_lt_pow_right (by decide) (by dsimp [n]; omega)
  have hm : m+1 < 2^laneWidth x s m :=
    (by have h := Nat.lt_two_pow_self (n := m+1)
        exact h.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [laneWidth]; omega)))
  exact ⟨by simpa [hwidth,pow_succ] using hprod.trans_lt hlarge, hm, by simp [bits]⟩

private theorem mask_self_shift {x : ℕ} (hx : BitIncl x (2*x)) : x = 0 := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases hz : x=0
    · exact hz
    let d := x/2
    have hd := Nat.div_add_mod x 2
    have h := mask_append_iff 1 (x%2) 0 d x (by omega) (by decide)
    have he : x = 2^1*d+x%2 := hd.symm
    have ht : BitIncl (x%2) 0 ∧ BitIncl d x := by
      apply h.mp
      change BitIncl (2*d+x%2) (2*x+0)
      rw [hd,Nat.add_zero]; exact hx
    have hzero := mask_le ht.1
    have hd' : x = 2*d := by dsimp [d]; omega
    have := ih d (Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide)) (hd' ▸ ht.2)
    omega

/-- Formula (12) as a positive-integer relation. -/
theorem power_two_iff_mask {x : ℕ} (hx : 0 < x) :
    (∃ i, x = 2^i) ↔ BitIncl x (2*x-1) := by
  constructor
  · rintro ⟨i,rfl⟩
    rw [show 2*2^i=2^(i+1) by rw [pow_succ,mul_comm]]
    apply mask_top
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  · intro h
    induction x using Nat.strong_induction_on with
    | h x ih =>
      let d := x/2
      have hd : 2*d+x%2=x := Nat.div_add_mod x 2
      by_cases even : x%2=0
      · have he : x=2*d := by omega
        have posd : 0<d := by omega
        have hu : 2*x-1=2*(2*d-1)+1 := by omega
        rw [hu,he] at h
        have hh := (mask_append_iff 1 0 1 d (2*d-1) (by decide) (by decide)).mp (by simpa using h)
        obtain ⟨k,hk⟩ := ih d (by omega) posd hh.2
        exact ⟨k+1, by rw [he,hk,pow_succ,mul_comm]⟩
      · have he : x=2*d+1 := by omega
        have hu : 2*x-1=2*(2*d)+1 := by omega
        rw [hu,he] at h
        have hh := (mask_append_iff 1 1 1 d (2*d) (by decide) (by decide)).mp (by simpa using h)
        exact ⟨0,by have := mask_self_shift hh.2; omega⟩

private theorem geom_word (q n : ℕ) (hq : 0 < q) :
    (q-1)*pack q (fun _ : Fin n => 1)+1=q^n := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack,pow_succ,← ih]
    have hh : q-1+1=q := Nat.sub_add_cancel hq
    rw [Nat.mul_add,Nat.mul_one,show (q-1)*(q*pack q (fun _ : Fin n => 1)) =
      (q-1)*pack q (fun _ : Fin n => 1)*q by ring]
    rw [Nat.add_assoc, hh]; ring

/-- The polynomial clock `P=(q−1)*I+1` and one mask force an all-ones
word of some length. This removes the variable exponent in (27) when that
length may be read back from the tableau. Width zero is excluded. -/
theorem clock_iff {w I : ℕ} (hw : 0<w) :
    let q := 2^w
    let P := (q-1)*I+1
    BitIncl P (2*P-1) ↔ ∃ n : ℕ, I = pack q (fun _ : Fin n => 1) := by
  let q := 2^w
  have hq : 1 < q := Nat.one_lt_two_pow (by omega)
  change BitIncl ((q-1)*I+1) (2*((q-1)*I+1)-1) ↔ _
  rw [← power_two_iff_mask (by omega)]
  constructor
  · rintro ⟨v,hv⟩
    induction v using Nat.strong_induction_on generalizing I with
    | h v ih =>
      by_cases hI : I=0
      · exact ⟨0,hI⟩
      have hqI : q-1 ≤ (q-1)*I := Nat.le_mul_of_pos_right _ (by omega)
      have hwv : w ≤ v := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (by
        change q ≤ 2^v; omega)
      let v' := v-w
      have he : 2^v = q*2^v' := by
        dsimp [q,v']; rw [← pow_add]; congr 1; omega
      have e : q*I+1 = I+q*2^v' := by
        rw [← he, ← hv]
        have hh : q = q-1+1 := by omega
        calc
          _ = ((q-1)+1)*I+1 := congrArg (fun z => z*I+1) hh
          _ = _ := by ring
      have em := congrArg (fun z => z%q) e
      dsimp only at em
      rw [Nat.mul_comm q I,Nat.add_comm (I*q) 1,Nat.add_mul_mod_self_right,
        Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hq] at em
      let J := I/q
      have hsplit : I=q*J+1 := by
        have h := Nat.div_add_mod I q
        simpa [J,← em] using h.symm
      have ec : (q-1)*J+1=2^v' := by
        rw [he,hsplit] at hv
        have hh : q-1+1=q := Nat.sub_add_cancel hq.le
        have left : q*((q-1)*J+1) = (q-1)*(q*J+1)+1 := by
          calc
            _ = (q-1)*(q*J)+q := by ring
            _ = _ := by rw [Nat.mul_add,Nat.mul_one,Nat.add_assoc,hh]
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0<q) (left.trans hv)
      obtain ⟨n,hn⟩ := ih v' (by dsimp [v']; omega) ec
      exact ⟨n+1,by rw [hsplit,hn,pack]⟩
  · rintro ⟨n,rfl⟩
    exact ⟨w*n,(geom_word q n (by omega)).trans (pow_mul 2 w n).symm⟩

/-- Nonnegative affine forms in a fixed finite bank of natural registers. A
pair of such forms represents an arbitrary integer affine equality. -/
structure Affine (m : ℕ) where
  offset : ℕ
  coeff : Fin m → ℕ

def Affine.eval {m : ℕ} (p : Affine m) (x : Fin m → ℕ) :=
  p.offset + ∑ i, p.coeff i * x i

/-- The same fixed linear combination on selected packed register words. -/
def Affine.packed {m : ℕ} (p : Affine m) (L : ℕ) (x : Fin m → ℕ) :=
  p.offset * L + ∑ i, p.coeff i * x i

def selected (Q I L R A : ℕ) : Prop :=
  BitIncl A R ∧ BitIncl A ((Q-1)*L) ∧ BitIncl R ((Q-1)*(I-L)+A)

/-- Soundness of an unbounded integer guess for a selected register word. -/
theorem selected_iff {w n : ℕ} (r : Fin n → ℕ) (flag : Fin n → Bool)
    (hr : ∀ i, r i < 2^w) (A : ℕ) :
    let q := 2^w
    let I := pack q (fun _ : Fin n => 1)
    let L := pack q (fun i => if flag i then 1 else 0)
    selected q I L (pack q r) A ↔ A=pack q (fun i => if flag i then r i else 0) := by
  let a (i : Fin n) : ℕ := if flag i then r i else 0
  let q := 2^w
  have ha (i) : a i < q := by dsimp [a]; split; exact hr i; exact Nat.two_pow_pos w
  constructor
  · intro S
    obtain ⟨b,hb,hbi⟩ := (mask_unpack_iff r hr).mp S.1
    have h := (addSelector_iff r b flag hr (fun i => (mask_le (hbi i)).trans_lt (hr i))).mp (hb ▸ S)
    exact hb.trans (congrArg (pack q) (funext h))
  · rintro rfl
    exact (addSelector_iff r a flag hr ha).mpr (fun _ => rfl)

private theorem flag_affine {m n : ℕ} (p : Affine m) (q : ℕ)
    (flag : Fin n → Bool) (r : Fin m → Fin n → ℕ) :
    p.packed (pack q (fun t => if flag t then 1 else 0))
      (fun i => pack q (fun t => if flag t then r i t else 0)) =
    pack q (fun t => if flag t then p.eval (fun j => r j t) else 0) := by
  unfold Affine.packed
  simp only [← pack_scale,pack_sum,← pack_add]
  apply congrArg (pack q)
  funext t
  by_cases h : flag t <;> simp [h,Affine.eval]

/-- One branch of a finite instruction table is checked simultaneously in all
time columns by a constant number of packed integer witnesses. Registers may
hold before values, after values, and the internal values of a macrostep. -/
theorem guardedAffine_iff {w n m : ℕ} (L R : Affine m) (r : Fin m → Fin n → ℕ)
    (flag : Fin n → Bool) (hr : ∀ j t, r j t < 2^w)
    (hl : ∀ t, L.eval (fun j => r j t) < 2^w)
    (hu : ∀ t, R.eval (fun j => r j t) < 2^w) :
    let q := 2^w
    let flags := pack q (fun t => if flag t then 1 else 0)
    let I := pack q (fun _ : Fin n => 1)
    (∃ A : Fin m → ℕ, (∀ j, selected q I flags (pack q (r j)) (A j)) ∧
      L.packed flags A = R.packed flags A) ↔
      ∀ t, flag t = true → L.eval (fun j => r j t) = R.eval (fun j => r j t) := by
  let q := 2^w
  let flags := pack q (fun t => if flag t then 1 else 0)
  let I := pack q (fun _ : Fin n => 1)
  let A (j : Fin m) := pack q (fun t => if flag t then r j t else 0)
  have eqs (B : Fin m → ℕ) :
      (∀ j, selected q I flags (pack q (r j)) (B j)) ↔ B=A := by
    constructor
    · intro h
      exact funext (fun j => (selected_iff _ _ (hr j) _).mp (h j))
    · rintro rfl j
      exact (selected_iff _ _ (hr j) _).mpr rfl
  have bound (P : Affine m) (h : ∀ t, P.eval (fun j => r j t) < q) (t : Fin n) :
      (if flag t then P.eval (fun j => r j t) else 0) < q := by
    split
    · exact h t
    · exact Nat.two_pow_pos _
  have E : L.packed flags A = R.packed flags A ↔
      ∀ t, flag t = true → L.eval (fun j => r j t) = R.eval (fun j => r j t) := by
    rw [flag_affine, flag_affine,pack_eq_iff _ _ (bound L hl) (bound R hu),funext_iff]
    constructor
    · intro h t ht
      simpa [ht] using h t
    · intro h t
      by_cases ht : flag t <;> simp [ht,h]
  exact ⟨fun ⟨B,h,e⟩ => E.mp ((eqs B).mp h ▸ e), fun h => ⟨A,(eqs _).mpr rfl,E.mpr h⟩⟩

/-- A single mask on an arbitrary word forces each lane to fit in `v` bits.
The remaining high bits in every lane stay available as carry guards. -/
theorem register_mask_iff {w v n X : ℕ} (hv : v ≤ w) :
    let q := 2^w
    let K := 2^v
    let I := pack q (fun _ : Fin n => 1)
    BitIncl X ((K-1)*I) ↔ ∃ r : Fin n → ℕ, X = pack q r ∧ ∀ t, r t < K := by
  let K := 2^v
  have hK : 0<K := Nat.two_pow_pos _
  have hW : K ≤ 2^w := Nat.pow_le_pow_right (by decide) hv
  dsimp only
  rw [← pack_scale]
  simp only [Nat.mul_one]
  rw [mask_unpack_iff _ (fun _ => by dsimp [K] at *; omega)]
  constructor
  · rintro ⟨r,eq,h⟩
    exact ⟨r,eq,fun t => by have := mask_le (h t); dsimp [K] at *; omega⟩
  · rintro ⟨r,eq,h⟩
    exact ⟨r,eq,fun t => mask_top (h t)⟩

/-- A fixed bound on the sum of coefficients reserves enough carry bits
for an affine equality on every well-typed witness, even a dishonest one. -/
theorem Affine.eval_lt {m v g : ℕ} (p : Affine m) (r : Fin m → ℕ)
    (hr : ∀ j, r j < 2^v) (hg : p.offset+(∑ j, p.coeff j) < 2^g) :
    p.eval r < 2^(g+v) := by
  have hpos := Nat.two_pow_pos v
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun j _ => Nat.mul_le_mul_left (p.coeff j) (hr j).le)
  rw [← Finset.sum_mul] at hs
  have ho := Nat.le_mul_of_pos_right p.offset hpos
  exact (Nat.add_le_add ho hs).trans_lt (by
    rw [← Nat.add_mul, pow_add]; exact Nat.mul_lt_mul_of_pos_right hg hpos)

private theorem mask_flag_word {w n v : ℕ} (hw : 0<w) :
    BitIncl v (pack (2^w) (fun _ : Fin n => 1)) ↔
    ∃ flag : Fin n → Bool, v=pack (2^w) (fun t => if flag t then 1 else 0) := by
  have one : 1 < 2^w := Nat.one_lt_two_pow (by omega)
  rw [mask_unpack_iff _ (fun _ => one)]
  constructor
  · rintro ⟨r,he,hr⟩
    refine ⟨fun t => decide (r t=1),he.trans (congrArg _ (funext (fun i => ?_)))⟩
    have h := mask_le (hr i)
    by_cases hi : r i=1
    · simp [hi]
    · simp [hi]; omega
  · rintro ⟨f,rfl⟩
    exact ⟨_,rfl,fun i => by cases h : f i <;> simp [BitIncl]⟩

/-- Polynomial and mask constraints for an arbitrary fixed, finite table of
guarded affine equalities. Each branch may test several equalities. All
guesses are whole words, and their number depends only on the table. -/
def branchChecks {m b : ℕ} (P : Fin b → List (Affine m × Affine m))
    (q I : ℕ) (R : Fin m → ℕ) : Prop :=
  ∃ flags : Fin b → ℕ, (∀ i, BitIncl (flags i) I) ∧ (∑ i, flags i) = I ∧
    ∀ i, ∀ p ∈ P i, ∃ A : Fin m → ℕ,
      (∀ j, selected q I (flags i) (R j) (A j)) ∧ p.1.packed (flags i) A = p.2.packed (flags i) A

/-- Exact finite-transition-table decoding with fixed word arity for arbitrary
trace length `n`. The coefficient bound in `Affine.eval_lt` supplies the last
two hypotheses from register masks plus a fixed number of carry guard bits. -/
theorem branchChecks_iff {m b n w : ℕ} (P : Fin b → List (Affine m × Affine m))
    (r : Fin m → Fin n → ℕ) (hw : 0 < w) (hb : b < 2^w) (hr : ∀ j t, r j t < 2^w)
    (hL : ∀ i, ∀ p ∈ P i, ∀ t, p.1.eval (fun j => r j t) < 2^w)
    (hR : ∀ i, ∀ p ∈ P i, ∀ t, p.2.eval (fun j => r j t) < 2^w) :
    branchChecks P (2^w) (pack (2^w) (fun _ : Fin n => 1)) (fun j => pack (2^w) (r j)) ↔
      ∀ t, ∃ i, ∀ p ∈ P i, p.1.eval (fun j => r j t) = p.2.eval (fun j => r j t) := by
  classical
  let q := 2^w
  let I := pack q (fun _ : Fin n => 1)
  constructor
  · rintro ⟨flags,hm,hs,ht⟩
    choose f hf using fun i => (mask_flag_word hw).mp (hm i)
    have counts := (onehot_iff f hb hw).mp (by simpa only [← hf] using hs)
    intro t
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun i => f i t = true)).card by rw [counts]; decide)
    refine ⟨i,fun p h => ?_⟩
    apply (guardedAffine_iff p.1 p.2 r (f i) hr (hL _ _ h) (hR _ _ h)).mp _ t (Finset.mem_filter.mp hi).2
    simpa only [← hf] using ht i p h
  · intro h
    choose sel H using h
    let f (i : Fin b) (t : Fin n) := decide (sel t=i)
    let flags (i : Fin b) := pack q (fun t => if f i t then 1 else 0)
    refine ⟨flags, fun i => (mask_flag_word hw).mpr ⟨f i,rfl⟩, (onehot_iff f hb hw).mpr ?_, ?_⟩
    · intro t
      have eqs : (Finset.univ.filter (fun j => f j t = true)) = {sel t} := by
        ext i
        simp [f,eq_comm]
      rw [eqs, Finset.card_singleton]
    · intro i p hp
      apply (guardedAffine_iff p.1 p.2 r (f i) hr (hL _ _ hp) (hR _ _ hp)).mpr
      intro t hit
      have e : sel t=i := by simpa [f] using hit
      exact H t p (e.symm ▸ hp)

/-- One polynomial equation links before- and after-register words into a
single trace with prescribed endpoints. The clock supplies its leading place
value `(q−1)*I+1` even when the trace has zero transitions. -/
theorem shiftTrace_iff {w n : ℕ} (a b : Fin n → ℕ) (first last : ℕ)
    (ha : ∀ t, a t < 2^w) (hb : ∀ t, b t < 2^w)
    (hf : first < 2^w) (hl : last < 2^w) :
    let q := 2^w
    let I := pack q (fun _ : Fin n => 1)
    pack q a + ((q-1)*I+1)*last = q*pack q b+first ↔
      ∃ r : Fin (n+1) → ℕ, r 0 = first ∧ r (Fin.last n) = last ∧
        (∀ t, r t.castSucc = a t) ∧ (∀ t, r t.succ = b t) := by
  let q := 2^w
  let L : Fin (n+1) → ℕ := Fin.snoc a last
  let R : Fin (n+1) → ℕ := Fin.cons first b
  have hL : ∀ t, L t < q := fun t => Fin.lastCases (by simpa [L] using hl)
    (fun j => by simpa [L] using ha j) t
  have hR : ∀ t, R t < q := fun t => Fin.cases (by simpa [R] using hf)
    (fun j => by simpa [R] using hb j) t
  have left : pack q L = pack q a + q^n*last := by simpa [L] using pack_last q L
  have right : pack q R = q*pack q b+first := by rw [pack]; simp [R]
  dsimp only
  rw [geom_word _ _ (Nat.two_pow_pos _)]
  change pack q a + q^n*last = q*pack q b+first ↔ _
  rw [← left,← right,pack_eq_iff L R hL hR]
  constructor
  · intro h
    refine ⟨L,by rw [h]; simp [R],by simp [L],fun t => by simp [L],fun t => ?_⟩
    rw [h]; simp [R]
  · rintro ⟨r,hf',hl',ha',hb'⟩
    have hleft : L = r := funext (fun t => Fin.lastCases (by simpa [L] using hl'.symm)
      (fun i => by simpa [L] using (ha' i).symm) t)
    exact hleft.trans (funext (fun t => Fin.cases (by simpa [R] using hf')
      (fun i => by simpa [R] using hb' i) t))

end DiophantineNP.JMTableau
