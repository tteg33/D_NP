import DiophantineNP.ShortResidue

/-! # Counting an arbitrary unary property with strict unary majority

Split the universe at its midpoint. In each half a disjoint interval of
padding makes one strict-majority query test whether the size exceeds a
specified value. The full-universe count has a separate binary readout. -/
namespace DiophantineNP.HABCounting
open Finset Counting WidthFormula FiniteArithmeticGap
open ShortResidue ShortResidue.Predicate
open scoped Classical
local infixr:35 " ⋀ " => Predicate.both
local infixr:30 " ⋁ " => Predicate.either

private def halfAt (h : ℕ) : Predicate where
  syntaxF σ := fromFormula (half (σ h))
  holds U _ e := e h = U/2
  valid _ _ _ := by rw [fromFormula_eval, half_true]

private def bitAtP (x j : ℕ) : Predicate where
  syntaxF σ := .bit (σ x) (σ j)
  holds _ _ e := (e x).testBit (e j) = true
  valid _ _ _ := Iff.rfl

/-- Names 0–15 are local to the counting construction. -/
private def body (x : ℕ) (p : Predicate) : Predicate where
  syntaxF σ := p.syntaxF (Function.update (fun i => σ (16+i)) x (σ 0))
  holds U t e := p.holds U t (Function.update (fun i => e (16+i)) x (e 0))
  valid {k U} σ t e := by
    rw [p.valid]
    apply Iff.of_eq
    congr 1
    funext i; by_cases hx : i=x
    · subst i; simp
    · simp [hx]

private def side (lower : Bool) (z h : ℕ) : Predicate :=
  if lower then lt z h else le h z

private def pad (lower : Bool) (z h d : ℕ) : Predicate :=
  if lower then Predicate.ex 7 (lt 7 d ⋀ add h 7 z) else lt z d

private noncomputable def greater (lower : Bool) (s : ℕ) (p : Predicate) : Predicate :=
  Predicate.ex 5 (add 5 s 6 ⋀ Predicate.maj 0 ((side lower 0 6 ⋀ p) ⋁ pad lower 0 6 5))

private noncomputable def equalsPart (lower : Bool) (s : ℕ) (p : Predicate) : Predicate :=
  (greater lower s p).neg ⋀ ((eqN s 0) ⋁
    Predicate.ex 4 ((Predicate.ex 7 (eqN 7 1 ⋀ add 4 7 s)) ⋀ greater lower 4 p))

private noncomputable def totalEq (p : Predicate) : Predicate :=
  Predicate.ex 6 (halfAt 6 ⋀ Predicate.ex 2 (Predicate.ex 3
    (add 2 3 1 ⋀ equalsPart true 2 p ⋀ equalsPart false 3 p)))

private def inSide (lower : Bool) (h z : ℕ) : Prop := if lower then z<h else h≤z

private noncomputable def part (lower : Bool) (S : Finset ℕ) (h : ℕ) :=
  S.filter (inSide lower h)

private def padding (lower : Bool) (h d : ℕ) :=
  if lower then Ico h (h+d) else range d

private theorem pad_spec (lower : Bool) (z h d U : ℕ) (t : ℕ→ℕ→Bool)
    (e : ℕ→ℕ) (hz : z ≠ 7) (hh : h ≠ 7) (hd : d ≠ 7) (hzU : e z<U) :
    (pad lower z h d).holds U t e ↔ e z ∈ padding lower (e h) (e d) := by
  cases lower
  · simp [pad,padding,lt]
  · simp only [pad,padding,Predicate.ex,Predicate.both,lt,add,Function.update_self,
      Function.update_of_ne hz,Function.update_of_ne hh,Function.update_of_ne hd]
    change (∃ a<U, a < e d ∧ e h + a = e z) ↔ e z ∈ Ico (e h) (e h + e d)
    rw [mem_Ico]
    constructor
    · rintro ⟨a,_,ha,he⟩; omega
    · rintro ⟨ha,hb⟩; exact ⟨e z-e h,by omega,by omega,by omega⟩

private theorem side_spec (lower : Bool) (z h U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) :
    (side lower z h).holds U t e ↔ inSide lower (e h) (e z) := by
  cases lower <;> simp [side,inSide,le,lt,Predicate.neg]

private theorem part_upper (lower : Bool) (U : ℕ) (S : Finset ℕ) (hSU : S ⊆ range U) :
    (part lower S (U/2)).card ≤ U-U/2 := by
  cases lower
  · have h : part false S (U/2) ⊆ Ico (U/2) U := by
      intro z hz
      obtain ⟨hz,hh⟩ := mem_filter.mp hz
      exact mem_Ico.mpr ⟨hh,mem_range.mp (hSU hz)⟩
    simpa using card_le_card h
  · have h : part true S (U/2) ⊆ range (U/2) := by
      intro z hz
      exact mem_range.mpr (mem_filter.mp hz).2
    have := card_le_card h
    rw [card_range] at this; omega

private theorem greater_spec (lower : Bool) (s : ℕ) (p : Predicate) (U : ℕ)
    (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (S : Finset ℕ) (hSU : S ⊆ range U)
    (hs : s≠5) (hh : e 6=U/2) (hU : 0<U)
    (hp : ∀ d<U, ∀ z<U, p.holds U t (Function.update (Function.update e 5 d) 0 z) ↔ z∈S) :
    (greater lower s p).holds U t e ↔ e s < (part lower S (U/2)).card := by
  classical
  let H := U/2
  let B := part lower S H
  have one (d : ℕ) (hd : d<U) (hsize : d+e s=H) :
      (Predicate.maj 0 ((side lower 0 6 ⋀ p) ⋁ pad lower 0 6 5)).holds U t
        (Function.update e 5 d) ↔ e s<B.card := by
    let C := padding lower H d
    have cardC : C.card=d := by cases lower <;> simp [C,padding]
    have join : Disjoint B C := by
      apply disjoint_left.mpr
      intro z hz hc
      have hhalf := (mem_filter.mp hz).2
      cases lower <;> simp_all [C,padding,inSide] <;> omega
    have eqS : (range U).filter (fun z => ((side lower 0 6 ⋀ p) ⋁ pad lower 0 6 5).holds U t
          (Function.update (Function.update e 5 d) 0 z)) = B ∪ C := by
      ext z
      by_cases hz : z<U
      · simp only [mem_filter,mem_range,hz,true_and,Predicate.either,Predicate.both,mem_union]
        rw [side_spec,hp d hd z hz,pad_spec _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
          (by simpa using hz)]
        simp [B,C,part,hh,H,Function.update,and_comm]
      · have hzB : z∉B := fun hb => hz (mem_range.mp (hSU (mem_filter.mp hb).1))
        have hzC : z∉C := by
          intro hc
          cases lower <;> simp [C,padding,H] at hc <;> dsimp [H] at hsize <;> omega
        simp [hz,hzB,hzC]
    change U/2 < _ ↔ _
    rw [eqS,card_union_of_disjoint join,cardC]
    dsimp [H] at hsize; omega
  change (∃ d<U, _ ∧ _) ↔ _
  simp only [add,Function.update_self,Function.update_of_ne hs,
    Function.update_of_ne (by decide : 6≠5),hh]
  constructor
  · rintro ⟨d,hd,he,hm⟩; exact (one d hd he).mp hm
  · intro ht
    have hb := part_upper lower U S hSU
    have hsize : e s ≤ U/2 := by omega
    refine ⟨H-e s,by dsimp [H]; omega,by dsimp [H]; omega,?_⟩
    exact (one _ (by dsimp [H]; omega) (by dsimp [H]; omega)).mpr ht

/-- When `p` is the lifted body its value on local slot zero is unaffected by the other local slots. -/
private def represents (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (p : Predicate) (S : Finset ℕ) : Prop :=
  ∀ f : ℕ→ℕ, (∀ i, f (16+i)=e (16+i)) → f 0<U → (p.holds U t f ↔ f 0∈S)

private theorem represents_update {U : ℕ} {t : ℕ→ℕ→Bool} {e : ℕ→ℕ} {p : Predicate}
    {S : Finset ℕ} (h : represents U t e p S) {x : ℕ} (hx : x<16) (v : ℕ) :
    represents U t (Function.update e x v) p S := by
  intro f hf hv
  exact h f (fun i => (hf i).trans (Function.update_of_ne (by omega) _ _)) hv

private theorem gt_spec {lower : Bool} {s : ℕ} {p : Predicate} {U : ℕ} {t : ℕ→ℕ→Bool} {e : ℕ→ℕ}
    {S : Finset ℕ} (hSU : S ⊆ range U) (hs : s≠5) (hh : e 6=U/2) (hU : 0<U)
    (hp : represents U t e p S) :
    (greater lower s p).holds U t e ↔ e s < (part lower S (U/2)).card := by
  apply greater_spec _ _ _ _ _ _ _ hSU hs hh hU
  intro d _ z hz
  have := hp (Function.update (Function.update e 5 d) 0 z)
    (fun i => by simp [Function.update_of_ne (by omega : 16+i ≠ 5)]) (by simpa using hz)
  simpa using this

private theorem equalsPart_spec (lower : Bool) (s : ℕ) (p : Predicate) (U : ℕ)
    (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (S : Finset ℕ) (hSU : S ⊆ range U)
    (hs4 : s≠4) (hs5 : s≠5) (hs7 : s≠7)
    (hh : e 6=U/2) (hs : e s < U) (hp : represents U t e p S) :
    (equalsPart lower s p).holds U t e ↔ e s = (part lower S (U/2)).card := by
  have hc := gt_spec (lower:=lower) hSU hs5 hh (by omega : 0<U) hp
  have predGt (v : ℕ) := gt_spec (lower:=lower) (s:=4) hSU (by decide) (e:=Function.update e 4 v)
      (by simpa using hh) (by omega : 0<U) (represents_update hp (by decide : 4<16) v)
  change (¬_ ∧ (_ ∨ ∃ v<U, (∃ o<U, _ ∧ _) ∧ _)) ↔ _
  simp only [hc,predGt,eqN,add,Function.update_self,Function.update_of_ne hs4,
    Function.update_of_ne hs7,Function.update_of_ne (by decide : 4≠7)]
  constructor
  · rintro ⟨hn, hz|⟨v,_,⟨o,_,ho,he⟩,hv⟩⟩ <;> omega
  · intro he
    refine ⟨by omega,?_⟩
    by_cases hz : e s=0
    · exact Or.inl hz
    · exact Or.inr ⟨e s - 1,by omega,⟨1,by omega,rfl,by omega⟩,by omega⟩

private theorem card_parts (S : Finset ℕ) (h : ℕ) : (part true S h).card+(part false S h).card = S.card := by
  classical
  have dis : Disjoint (part true S h) (part false S h) := by
    apply disjoint_left.mpr
    intro z hz hz'
    exact (not_lt_of_ge (mem_filter.mp hz').2) (mem_filter.mp hz).2
  rw [← card_union_of_disjoint dis]
  congr 1
  ext z
  simp only [mem_union,part,mem_filter,inSide]
  by_cases hz : z<h <;> simp_all

private theorem total_spec (p : Predicate) (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ)
    (S : Finset ℕ) (hSU : S ⊆ range U) (hs : e 1<U) (hp : represents U t e p S) :
    (totalEq p).holds U t e ↔ e 1=S.card := by
  let H:=U/2
  have split (h l r : ℕ) (he : h=H) (hl : l<U) (hr : r<U) :
      let f := Function.update (Function.update (Function.update e 6 h) 2 l) 3 r
      ((add 2 3 1 ⋀ equalsPart true 2 p ⋀ equalsPart false 3 p).holds U t f ↔
        l+r=e 1 ∧ l=(part true S H).card ∧ r=(part false S H).card) := by
    dsimp only
    let f := Function.update (Function.update (Function.update e 6 h) 2 l) 3 r
    have hf := represents_update (represents_update (represents_update hp (by decide : 6<16) h)
      (by decide : 2<16) l) (by decide : 3<16) r
    have left := equalsPart_spec true 2 p U t f S hSU (by decide) (by decide) (by decide)
      (by simpa [f,H,Function.update] using he) (by simpa [f,Function.update] using hl) hf
    have right := equalsPart_spec false 3 p U t f S hSU (by decide) (by decide) (by decide)
      (by simpa [f,H,Function.update] using he) (by simpa [f,Function.update] using hr) hf
    change (f 2+f 3=f 1 ∧ _ ∧ _) ↔ _
    rw [left,right]; simp [f,Function.update,H]
  change (∃ h<U, Function.update e 6 h 6=U/2 ∧ ∃ l<U, ∃ r<U, _) ↔ _
  simp only [Function.update_self]
  have hpairs:=card_parts S H
  constructor
  · rintro ⟨h,_,he,l,hl,r,hr,hf⟩
    obtain ⟨hsum,h1,h2⟩ := (split h l r he hl hr).mp hf
    omega
  · intro he
    have hl : (part true S H).card<U := by omega
    have hr : (part false S H).card<U := by omega
    exact ⟨H,by dsimp [H]; omega,rfl,_,hl,_,hr,(split _ _ _ rfl hl hr).mpr ⟨by omega,rfl,rfl⟩⟩

/-- The cardinality under a finite quantifier, with numerical variable names. -/
noncomputable def cardP (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (x : ℕ) (p : Predicate) : ℕ :=
  ((range U).filter fun z => p.holds U t (Function.update e x z)).card

private theorem for_body (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (x : ℕ) (p : Predicate) :
    represents U t e (body x p) ((range U).filter
      (fun z => p.holds U t (Function.update (fun i => e (16+i)) x z))) := by
  intro f hf hz
  simp only [body,mem_filter,mem_range,hz,true_and,show (fun i=>f (16+i))=(fun i=>e (16+i)) from funext hf]

/-- Exact cardinality when the answer is a member of the finite universe. -/
noncomputable def countEqP (x s : ℕ) (p : Predicate) : Predicate where
  syntaxF σ := (totalEq (body x p)).syntaxF (fun i => if i=1 then σ s else σ (i-16))
  holds U t e := e s=cardP U t e x p
  valid {k U} σ t env := by
    let e : ℕ→ℕ := fun i => (env (if i=1 then σ s else σ (i-16))).val
    rw [Predicate.valid]
    change (totalEq (body x p)).holds U t e ↔ _
    rw [total_spec _ _ _ e _ (filter_subset _ _) (by simp [e]) (for_body _ _ _ _ _)]
    simp [e,cardP,show ∀ i : ℕ, 16+i≠1 by omega]



/-- Read bit `j` of the universe size using its half and parity. -/
private def sizeBit (j : ℕ) : Predicate :=
  Predicate.ex 6 (halfAt 6 ⋀
    ((eqN j 0 ⋀ Predicate.ex 7 (add 6 6 7)) ⋁
     Predicate.ex 4 ((Predicate.ex 7 (eqN 7 1 ⋀ add 4 7 j)) ⋀ bitAtP 6 4)))

private theorem sizeBit_spec (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (hj : e 14<U) :
    (sizeBit 14).holds U t e ↔ U.testBit (e 14) = true := by
  simp only [sizeBit,Predicate.ex,halfAt,Predicate.both,Predicate.either,eqN,add,bitAtP]
  simp [Function.update]
  have halfFits : U/2<U := by omega
  cases he : e 14 with
  | zero =>
      simp [Nat.testBit_zero,halfFits]
      omega
  | succ i =>
      simp [Nat.testBit_succ,halfFits]
      exact ⟨fun h => h.2.2, fun h => ⟨by omega, by omega, h⟩⟩

private noncomputable def wordBit (p : Predicate) : Predicate :=
  (Predicate.ex 1 (totalEq p ⋀ bitAtP 1 14)) ⋁ ((Predicate.ex 0 p.neg).neg ⋀ sizeBit 14)

private theorem wordBit_spec (p : Predicate) (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ)
    (S : Finset ℕ) (hSU : S⊆range U) (hj : e 14<U) (hp : represents U t e p S) :
    (wordBit p).holds U t e ↔ S.card.testBit (e 14)=true := by
  have limb (v : ℕ) (hv : v<U) := total_spec p U t (Function.update e 1 v) S hSU
    (by simpa using hv) (represents_update hp (by decide : 1<16) v)
  have full : (Predicate.ex 0 p.neg).neg.holds U t e ↔ S=range U := by
    change (¬∃ v<U, ¬p.holds U t (Function.update e 0 v)) ↔ _
    have each (v : ℕ) (hv : v<U) := hp (Function.update e 0 v)
      (fun i=>by simp) (by simpa using hv)
    constructor
    · intro h
      apply Subset.antisymm hSU
      intro v hv
      exact (each v (mem_range.mp hv)).mp (by by_contra hn; exact h ⟨v,mem_range.mp hv,hn⟩)
    · rintro rfl ⟨v,hv,hn⟩
      exact hn ((each v hv).mpr (by simpa using hv))
  change ((∃ v<U, _ ∧ _) ∨ _ ∧ _) ↔ _
  rw [full,sizeBit_spec U t e hj]
  constructor
  · rintro (⟨v,hv,he,hb⟩|⟨rfl,hb⟩)
    · obtain rfl : v=S.card := by simpa using (limb v hv).mp he
      simpa [bitAtP,Function.update] using hb
    · simpa using hb
  · intro hb
    by_cases hs : S.card<U
    · exact Or.inl ⟨_,hs,(limb _ hs).mpr (by simp),by simpa [bitAtP,Function.update] using hb⟩
    · have he := eq_of_subset_of_card_le hSU (by simpa using Nat.le_of_not_lt hs)
      exact Or.inr ⟨he,by simpa [he] using hb⟩

/-- A fixed formula for each bit of the cardinality, including the full-set case. -/
noncomputable def countBitP (x j : ℕ) (p : Predicate) : Predicate where
  syntaxF σ := (wordBit (body x p)).syntaxF (fun i => if i=14 then σ j else σ (i-16))
  holds U t e := (cardP U t e x p).testBit (e j)=true
  valid {k U} σ t env := by
    let e : ℕ→ℕ := fun i => (env (if i=14 then σ j else σ (i-16))).val
    rw [Predicate.valid]
    change (wordBit (body x p)).holds U t e ↔ _
    rw [wordBit_spec _ _ _ e _ (filter_subset _ _) (by simp [e]) (for_body _ _ _ _ _)]
    simp [e,cardP,show ∀ i : ℕ, 16+i≠14 by omega]

end DiophantineNP.HABCounting
