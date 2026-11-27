import DiophantineNP.HABSumParameters
import DiophantineNP.HABSumBlocks

/-! # Selecting the two binary words in the iterated-addition construction -/
namespace DiophantineNP.HABSumSelectors
open Counting PrimeFormula WidthFormula FiniteArithmeticGap ShortResidue
open ShortResidue.Predicate HABSumParameters HABSumBlocks
local infixr:35 " ⋀ " => Predicate.both

/-- The location formula uses j at 0, k at 1, the block start at 3
and the bit within the block total at 4. For a high digit the bit lies
one full block later than its low digit. -/
private def location (high : Bool) : Predicate :=
  ex 6 (mul 6 1 3 ⋀ add 3 4 0 ⋀
    (if high then ex 7 (lt 7 1 ⋀ add 1 7 4) else lt 4 1))

private def Loc (high : Bool) (j k start pos : ℕ) : Prop :=
  if high then k≤j ∧ start=(j/k-1)*k ∧ pos=k+j%k
  else start=j/k*k ∧ pos=j%k

private theorem location_iff (high : Bool) {U : ℕ} (t : ℕ→ℕ→Bool) (e : ℕ→ℕ)
    (hj : e 0<U) (hk : 0<e 1) : (location high).holds U t e ↔ Loc high (e 0) (e 1) (e 3) (e 4) := by
  let j := e 0
  let k := e 1
  have div := Nat.div_add_mod j k
  have rem := Nat.mod_lt j hk
  have quo := Nat.div_le_self j k
  change j<U at hj
  have base (q r : ℕ) (hr : r<k) (h : q*k+r=j) : j/k=q ∧ j%k=r := by
    rw [←h,Nat.add_comm (q*k) r,Nat.mul_comm q k,Nat.add_mul_div_left _ _ hk,Nat.add_mul_mod_self_left, Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr]
    simp
  cases high
  · simp only [location, Bool.false_eq_true, ↓reduceIte, ex,both,mul,add,lt,Loc]
    change (∃ q<U, q*k=e 3 ∧ e 3+e 4=j ∧ e 4<k) ↔ e 3=j/k*k ∧ e 4=j%k
    constructor
    · rintro ⟨q,_,h1,h2,hr⟩
      obtain ⟨h,h'⟩ := base q (e 4) hr (h1 ▸ h2)
      exact ⟨h ▸ h1.symm,h'.symm⟩
    · rintro ⟨h,h'⟩
      exact ⟨j/k,by omega,h.symm,by rw [h,h',Nat.mul_comm];exact div,h' ▸ rem⟩
  · simp only [location, ↓reduceIte,ex,both,mul,add,lt,Loc]
    change (∃ q<U, q*k=e 3 ∧ e 3+e 4=j ∧ ∃ r<U, r<k ∧ k+r=e 4) ↔
      k≤j ∧ e 3=(j/k-1)*k ∧ e 4=k+j%k
    constructor
    · rintro ⟨q,_,h1,h2,r,_,hr,h3⟩
      have hh : (q+1)*k+r=j := by rw [Nat.add_mul,Nat.one_mul,h1]; omega
      obtain ⟨h,h'⟩ := base _ _ hr hh
      exact ⟨by omega,by rw [h,Nat.add_sub_cancel];exact h1.symm,by omega⟩
    · rintro ⟨hle,h,h'⟩
      have hp : 0<j/k := Nat.div_pos hle hk
      have aux := Nat.sub_add_cancel (by omega : 1≤j/k)
      have eq : (j/k-1)*k+k=j/k*k := by
        calc _ = (j/k-1+1)*k := by ring
             _ = _ := by rw [aux]
      refine ⟨j/k-1,by omega,h.symm,?_,j%k,(Nat.mod_le _ _).trans_lt hj,rem,h'.symm⟩
      rw [h,h',←Nat.add_assoc,eq,Nat.mul_comm (j/k) k]; exact div

/-- A compiled block query is placed in the surrounding register environment. -/
def blockQuery (p : Predicate) : Predicate := reindex p (fun i =>
  if i=0 then 3 else if i=1 then 1 else if i=2 then 2 else if i=3 then 2 else 5)

/-- One query for each of the two words, using the same least block size. -/
def component (p : Predicate) (high : Bool) : Template 1 :=
  (ex 1 (ex 2 (selected 1 2 ⋀ ex 3 (ex 4 (location high ⋀ ex 5 ((blockQuery p) ⋀ bit 5 4)))))).syntaxF
    (fun _ => 0)

def BlockSpec (p : Predicate) (U : ℕ) (f : ℕ→ℕ) : Prop :=
  ∀ e : ℕ→ℕ, (∀ i, e i<U) → Eligible U (e 1) → e 2=2^(e 1) → e 3=e 2 →
  (p.holds U (fun r c => (f r).testBit c) e ↔ e 4=block (column f U) U (e 2) (e 1) (e 0))

private theorem update_bounded {U : ℕ} {e : ℕ→ℕ} (he : ∀ i, e i<U) (i : ℕ) {v : ℕ} (hv : v<U) :
    ∀ j, Function.update e i v j<U := by
  intro j
  by_cases h : j=i
  · subst j; simpa using hv
  · simpa [Function.update_of_ne h] using he j

theorem component_spec (p : Predicate) (high : Bool) {U k : ℕ} (f : ℕ→ℕ)
    (hg : Eligible U k) (hmin : ∀ l, Eligible U l → k≤l) (hs : BlockSpec p U f) (j : Fin U) :
    (component p high).eval (fun r c => (f r.val).testBit c.val) (fun _=>j) =
    (if high then highWord (column f U) U (2^k) k else lowWord (column f U) U (2^k) k).testBit j.val := by
  let t := fun r c : ℕ => (f r).testBit c
  let c := column f U
  let val := fun start => block c U (2^k) k start
  have ⟨hkU,hbU,_,h2k⟩ := eligible_fits hg
  have hv (start) : val start < U := by
    refine (block_bound c U _ k start le_rfl).trans_le ?_
    have h := Nat.mul_le_mul_right (2^k) (Nat.le_mul_of_pos_left (2^k) hg.1)
    exact h.trans hg.2.1.le
  apply Bool.eq_iff_iff.mpr
  rw [component, Predicate.valid (table := t)] 
  simp only [ex,both,HABSumParameters.bit]
  let env := fun _ : ℕ => j.val
  let e (a b start pos value : ℕ) := Function.update (Function.update (Function.update
      (Function.update (Function.update env 1 a) 2 b) 3 start) 4 pos) 5 value
  have sel a b (hb : b<U) : (selected 1 2).holds U t (Function.update (Function.update env 1 a) 2 b) ↔
      b=2^a ∧ Eligible U a ∧ ∀ l, Eligible U l → a≤l := by
    simpa [Function.update] using selected_iff U t (Function.update (Function.update env 1 a) 2 b) 1 2
      (by simpa [Function.update] using hb)
  have loc a b start pos (ha : 0<a) : (location high).holds U t (Function.update (Function.update
      (Function.update (Function.update env 1 a) 2 b) 3 start) 4 pos) ↔ Loc high j.val a start pos := by
    apply location_iff _ _ _ j.isLt ha
  have bq start pos value (hsU : start<U) (hpU : pos<U) (hvU : value<U) :
      (blockQuery p).holds U t (e k (2^k) start pos value) ↔ value=val start := by
    unfold blockQuery reindex
    apply hs
    · intro i
      exact (update_bounded (update_bounded (update_bounded (update_bounded
        (update_bounded (fun _ => j.isLt) 1 hkU) 2 hbU) 3 hsU) 4 hpU) 5 hvU) _
    · exact hg
    · rfl
    · rfl
  change (∃ a<U, ∃ b<U, (selected 1 2).holds U t _ ∧ ∃ start<U, ∃ pos<U,
    (location high).holds U t _ ∧ ∃ v<U, (blockQuery p).holds U t (e a b start pos v) ∧ v.testBit pos=true) ↔ _
  constructor
  · rintro ⟨a,ha,b,hb,sel',s,hsU,i,hiU,loc',v,hvU,bq',bit'⟩
    obtain ⟨rfl,hga,hmina⟩ := (sel a b hb).1 sel'
    have hak : a=k := Nat.le_antisymm (hmina k hg) (hmin a hga)
    subst a
    obtain rfl := (bq s i v hsU hiU hvU).1 bq'
    have hl := (loc k _ s i hg.1).1 loc'
    cases high
    · obtain ⟨rfl,rfl⟩ := hl
      simpa only [Bool.false_eq_true,↓reduceIte,lowWord_bit _ hg.1 j.isLt] using bit'
    · obtain ⟨h,rfl,rfl⟩ := hl
      simpa only [Bool.true_eq,↓reduceIte,highWord_bit _ hg.1 j.isLt le_rfl,if_neg (Nat.not_lt.mpr h)] using bit'
  · intro bit'
    have rem := Nat.mod_lt j.val hg.1
    have basele := Nat.div_mul_le_self j.val k
    have finish (s i : ℕ) (hsU : s<U) (hiU : i<U) (hl : Loc high j.val k s i) (hb : (val s).testBit i=true) :
        ∃ a<U, ∃ b<U, (selected 1 2).holds U t (Function.update (Function.update env 1 a) 2 b) ∧
          ∃ s<U, ∃ i<U, (location high).holds U t (Function.update (Function.update
            (Function.update (Function.update env 1 a) 2 b) 3 s) 4 i) ∧
          ∃ v<U, (blockQuery p).holds U t (e a b s i v) ∧ v.testBit i=true :=
      ⟨k,hkU,2^k,hbU,(sel _ _ hbU).2 ⟨rfl,hg,hmin⟩,s,hsU,i,hiU,(loc _ _ _ _ hg.1).2 hl,
       val s,hv s,(bq _ _ _ hsU hiU (hv s)).2 rfl,hb⟩
    cases high
    · exact finish _ _ (basele.trans_lt j.isLt) (rem.trans hkU) ⟨rfl,rfl⟩
        (by simpa only [Bool.false_eq_true,↓reduceIte,lowWord_bit _ hg.1 j.isLt] using bit')
    · rw [if_pos rfl,highWord_bit _ hg.1 j.isLt le_rfl] at bit'
      split at bit'
      · contradiction
      · rename_i h
        exact finish _ _ ((Nat.mul_le_mul_right k (Nat.sub_le _ _)).trans_lt (basele.trans_lt j.isLt))
          (by omega) ⟨by omega,rfl,rfl⟩ bit'

end DiophantineNP.HABSumSelectors
