import DiophantineNP.ShortResidue
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Counting a block by coding its bit contributions

Each selected bit at local offset s has weight 2^s. Represent these copies by a
third coordinate w < 2^s, packing all three coordinates into one finite variable.
This construction uses the integer graphs of truncated addition and multiplication,
ordinary BIT, and a predicate for bits of a column population count. -/
namespace DiophantineNP.HABSumFormula
open Counting WidthFormula Finset ShortResidue ShortResidue.Predicate
open scoped Classical
local infixr:35 " ⋀ " => Predicate.both

private def bitP (x j : ℕ) : Predicate where
  syntaxF σ := .bit (σ x) (σ j)
  holds _ _ e := (e x).testBit (e j) = true
  valid _ _ _ := Iff.rfl

/-- A numerical witness w is below 2^s exactly when it has no bit at or above s.
The temporary register is private to this fixed formula. -/
private def lowWeight : Predicate :=
  (Predicate.ex 20 ((Predicate.lt 20 6).neg ⋀ bitP 8 20)).neg

private theorem weight_spec {U : ℕ} (table : ℕ → ℕ → Bool) (e : ℕ → ℕ) (hw : e 8<U) :
    lowWeight.holds U table e ↔ e 8<2^(e 6) := by
  change (¬ ∃ j<U, ¬ j < e 6 ∧ (e 8).testBit j = true) ↔ _
  constructor
  · intro hn
    by_contra! h
    obtain ⟨j,hj,hbit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow h
    have hjU : j<U := by
      have := Nat.ge_two_pow_of_testBit hbit
      have := Nat.lt_two_pow_self (n:=j)
      omega
    exact hn ⟨j,hjU,by omega,hbit⟩
  · rintro h ⟨j,hj,hlo,hbit⟩
    have := Nat.ge_two_pow_of_testBit hbit
    have := Nat.pow_le_pow_right (n:=2) (by decide) (show e 6≤j by omega)
    omega

/-- Registers s=6,t=7,w=8 encode the cell as (s L+t) B+w in register 5. -/
private def codeTest : Predicate :=
  Predicate.ex 11 <| Predicate.ex 12 <| Predicate.ex 13 <|
    mul 6 2 11 ⋀ add 11 7 12 ⋀ mul 12 3 13 ⋀ add 13 8 5

private theorem codeTest_spec {U : ℕ} (table : ℕ → ℕ → Bool) (e : ℕ→ℕ)
    (hz : e 5<U) (hb : 0<e 3) :
    codeTest.holds U table e ↔ (e 6*e 2+e 7)*e 3+e 8=e 5 := by
  change (∃ v<U, ∃ w<U, ∃ x<U, e 6*e 2=v ∧ v+e 7=w ∧ w*e 3=x ∧ x+e 8=e 5) ↔ _
  constructor
  · rintro ⟨v,_,w,_,x,_,h1,h2,h3,h4⟩; subst v; subst w; subst x; exact h4
  · intro he
    have h12 : e 6*e 2+e 7 ≤ (e 6*e 2+e 7)*e 3 := Nat.le_mul_of_pos_right _ hb
    exact ⟨_,by omega,_,by omega,_,by omega,rfl,rfl,rfl,he⟩

/-- The column bit predicate is read at slots i=10,t=7. -/
def cell (colBit : Predicate) : Predicate :=
  Predicate.ex 6 <| Predicate.ex 7 <| Predicate.ex 8 <| Predicate.ex 9 <| Predicate.ex 10 <|
    lt 6 1 ⋀ lt 7 2 ⋀ lowWeight ⋀ add 0 6 9 ⋀ add 10 7 9 ⋀ codeTest ⋀ colBit

/-- A true triple describes 2^s contributions when its input column count has bit t set. -/
def good (c : ℕ→ℕ) (U start k L B z : ℕ) : Prop :=
  ∃ s<k, ∃ t<L, ∃ w<2^s, start+s<U ∧ t≤start+s ∧
    (c (start+s-t)).testBit t=true ∧ (s*L+t)*B+w=z

private def withCells (e : ℕ→ℕ) (s t w j i : ℕ) :=
  Function.update (Function.update (Function.update (Function.update (Function.update e 6 s) 7 t) 8 w) 9 j) 10 i

theorem cell_spec (colBit : Predicate) (c : ℕ→ℕ) (U : ℕ) (tab : ℕ→ℕ→Bool) (e : ℕ→ℕ)
    (hcol : ∀ d : ℕ→ℕ, colBit.holds U tab d ↔ (c (d 10)).testBit (d 7)=true)
    (hk : e 1<U) (hL : e 2<U) (hB : e 3<U) (hbase : e 3=2^(e 1)) (hz : e 5<U) :
    (cell colBit).holds U tab e ↔ good c U (e 0) (e 1) (e 2) (e 3) (e 5) := by
  have hsimp (s t w j i : ℕ) (hw : w<U) :
      (lowWeight ⋀ add 0 6 9 ⋀ add 10 7 9 ⋀ codeTest ⋀ colBit).holds U tab (withCells e s t w j i) ↔
        w<2^s ∧ e 0+s=j ∧ i+t=j ∧ (s*e 2+t)*e 3+w=e 5 ∧ (c i).testBit t=true := by
    let d := withCells e s t w j i
    have ww : d 8<U := by simpa [d,withCells,Function.update] using hw
    have zz : d 5<U := by simpa [d,withCells,Function.update] using hz
    have bb : 0<d 3 := by simp [d,withCells,Function.update,hbase]
    change (lowWeight.holds U tab d ∧ _ ∧ _ ∧ codeTest.holds U tab d ∧ colBit.holds U tab d) ↔ _
    rw [weight_spec _ _ ww,codeTest_spec _ _ zz bb,hcol]
    simp [add,d,withCells,Function.update]
  simp only [cell,Predicate.ex]
  constructor
  · rintro ⟨s,_,t,_,w,hw,j,hj,i,_,hs,ht,h⟩
    obtain ⟨hw',hj',hi,hcode,hbit⟩ := (hsimp s t w j i hw).mp h
    have hst : s<e 1 ∧ t<e 2 := by simpa [lt,Function.update] using And.intro hs ht
    exact ⟨s,hst.1,t,hst.2,w,hw',by omega,by omega,by simpa [show e 0+s-t=i by omega] using hbit,hcode⟩
  · rintro ⟨s,hs,t,ht,w,hw,hj,hjt,hbit,he⟩
    have hwu : w<U := hw.trans_le (Nat.pow_le_pow_right (by decide) hs.le) |>.trans (hbase ▸ hB)
    refine ⟨s,hs.trans hk,t,ht.trans hL,w,hwu,e 0+s,hj,e 0+s-t,by omega,?_,?_,?_⟩
    · simpa [lt,Function.update] using hs
    · simpa [lt,Function.update] using ht
    · exact (hsimp _ _ _ _ _ hwu).mpr ⟨hw,rfl,by omega,he,hbit⟩

private theorem encode_lt {s k t L w B : ℕ} (hs : s<k) (ht : t<L) (hw : w<B) :
    (s*L+t)*B+w < k*L*B := by
  have a : s*L+t < k*L := calc
    s*L+t < (s+1)*L := by rw [Nat.succ_mul]; omega
    _ ≤ _ := Nat.mul_le_mul_right _ hs
  calc
    (s*L+t)*B+w < (s*L+t+1)*B := by rw [Nat.succ_mul]; omega
    _ ≤ _ := Nat.mul_le_mul_right _ a

private theorem digit_inj {q r q' r' B : ℕ} (hr : r<B) (hr' : r'<B)
    (he : q*B+r=q'*B+r') : q=q' ∧ r=r' := by
  have hh := congrArg (fun z : ℕ => z % B) he
  simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hr'] at hh
  subst r'
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel he),rfl⟩

/-- Count the codes by their three coordinates. Truncation applies to the last block. -/
theorem card_good (c : ℕ→ℕ) (U start k L B : ℕ) (hB : B=2^k) (hcap : k*L*B≤U) :
    ((range U).filter (good c U start k L B)).card =
      ∑ s ∈ range k, (if start+s<U then
        ((range L).filter (fun t => t≤start+s ∧ (c (start+s-t)).testBit t=true)).card else 0)*2^s := by
  classical
  let width (s : ℕ) : Finset ℕ :=
    (range L).filter (fun t => start+s<U ∧ t≤start+s ∧ (c (start+s-t)).testBit t=true)
  let triples : Finset ((s : ℕ) × (ℕ × ℕ)) :=
    (range k).sigma (fun s => width s ×ˢ range (2^s))
  let encode (a : (s : ℕ) × (ℕ × ℕ)) := (a.1*L+a.2.1)*B+a.2.2
  have belongs (s t w : ℕ) : Sigma.mk s (t,w) ∈ triples ↔
      s<k ∧ t<L ∧ start+s<U ∧ t≤start+s ∧ (c (start+s-t)).testBit t = true ∧ w<2^s := by
    simp [triples, width, and_assoc, and_left_comm]
  have ww {s w : ℕ} (hs : s<k) (hw : w<2^s) : w<B :=
    hB ▸ hw.trans_le (Nat.pow_le_pow_right (by decide) hs.le)
  have htr : triples.card = ((range U).filter (good c U start k L B)).card := by
    apply card_bij (fun a _ => encode a)
    · rintro ⟨s,t,w⟩ h
      obtain ⟨hs,ht,hj,htj,hbit,hw⟩ := (belongs ..).mp h
      exact mem_filter.mpr ⟨mem_range.mpr ((encode_lt hs ht (ww hs hw)).trans_le hcap),
        ⟨s,hs,t,ht,w,hw,hj,htj,hbit,rfl⟩⟩
    · rintro ⟨s,t,w⟩ ha ⟨s',t',w'⟩ hb he
      obtain ⟨hs,ht,_,_,_,hw⟩ := (belongs ..).mp ha
      obtain ⟨hs',ht',_,_,_,hw'⟩ := (belongs ..).mp hb
      obtain ⟨he',rfl⟩ := digit_inj (ww hs hw) (ww hs' hw') he
      obtain ⟨rfl,rfl⟩ := digit_inj ht ht' he'
      rfl
    · intro z hz
      obtain ⟨s,hs,t,ht,w,hw,hj,htj,hbit,he⟩ := (mem_filter.mp hz).2
      exact ⟨⟨s,t,w⟩,(belongs ..).mpr ⟨hs,ht,hj,htj,hbit,hw⟩,he⟩
  rw [←htr]
  simp only [triples,card_sigma,card_product,card_range]
  apply sum_congr rfl
  intro s hs
  by_cases hj : start+s<U <;> simp [width,hj]

end DiophantineNP.HABSumFormula
