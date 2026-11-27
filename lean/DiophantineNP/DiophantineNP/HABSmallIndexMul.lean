import DiophantineNP.HABSourceShift

/-! # Native index multiplication by unary counting

Pack a rectangle of x by y points using the id (r shifted by d) + c + 1.
The stride is a power of two at least y. The formula verifies that all ids
fit strictly in the lower half of the universe. Two strict-majority queries
against the complementary upper interval then give its exact cardinality. -/
namespace DiophantineNP.HAB
open Finset
open scoped Classical

private structure NRel where
  form : {k : ℕ} → (ℕ→Fin k) → Form k
  holds : ℕ → (ℕ→ℕ) → Prop
  valid {k U : ℕ} (σ : ℕ→Fin k) (A : Matrix U) (e : Fin k→Fin U) :
    (form σ).Holds A e ↔ holds U (fun i => (e (σ i)).val)

private def NRel.both (p q : NRel) : NRel where
  form σ := .conj (p.form σ) (q.form σ)
  holds U e := p.holds U e ∧ q.holds U e
  valid _ _ _ := and_congr (p.valid ..) (q.valid ..)

private def NRel.either (p q : NRel) : NRel where
  form σ := .disj (p.form σ) (q.form σ)
  holds U e := p.holds U e ∨ q.holds U e
  valid _ _ _ := or_congr (p.valid ..) (q.valid ..)

private def NRel.neg (p : NRel) : NRel where
  form σ := .neg (p.form σ)
  holds U e := ¬ p.holds U e
  valid _ _ _ := not_congr (p.valid ..)

private theorem push {k U : ℕ} (x : ℕ) (σ : ℕ→Fin k) (env : Fin k→Fin U) (z : Fin U) :
    (fun i => ((Fin.cases z env : Fin (k+1)→Fin U) (Function.update (Fin.succ ∘ σ) x 0 i)).val) =
      Function.update (fun i => (env (σ i)).val) x z.val := by
  funext i
  by_cases hi : i=x
  · subst i; simp
  · simp [hi]

private def NRel.ex (v : ℕ) (p : NRel) : NRel where
  form σ := .ex (p.form (Function.update (Fin.succ ∘ σ) v 0))
  holds U e := ∃ t<U, p.holds U (Function.update e v t)
  valid σ A e := by
    simp only [Form.Holds,p.valid,push]
    exact ⟨fun ⟨i,h⟩ => ⟨i,i.isLt,h⟩,fun ⟨i,hi,h⟩ => ⟨⟨i,hi⟩,h⟩⟩

private noncomputable def NRel.maj (v : ℕ) (p : NRel) : NRel where
  form σ := .many (p.form (Function.update (Fin.succ ∘ σ) v 0))
  holds U e := U/2 < ((range U).filter (fun i => p.holds U (Function.update e v i))).card
  valid {k U} σ A e := by
    simp only [Form.Holds,p.valid,push]
    have he : (univ.filter (fun i : Fin U => p.holds U (Function.update (fun j => (e (σ j)).val) v i.val))).card =
        ((range U).filter (fun i => p.holds U (Function.update (fun j => (e (σ j)).val) v i))).card := by
      apply card_bij (fun i _ => i.val)
      · intro i h; exact mem_filter.mpr ⟨mem_range.mpr i.isLt,(mem_filter.mp h).2⟩
      · exact fun i _ j _ h => Fin.ext h
      · intro i h
        exact ⟨⟨i,mem_range.mp (mem_filter.mp h).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩,rfl⟩
    rw [he]; omega

private def ltR (x y : ℕ) : NRel where
  form σ := .lt (σ x) (σ y)
  holds _ e := e x<e y
  valid _ _ _ := Iff.rfl

private def leR (x y : ℕ) := (ltR y x).neg

private def lit (x n : ℕ) : NRel where
  form σ := indexNat n (σ x)
  holds _ e := e x=n
  valid _ _ _ := indexNat_correct ..

private def addR (x y z : ℕ) : NRel where
  form σ := indexAdd (σ x) (σ y) (σ z)
  holds _ e := e x+e y=e z
  valid _ _ _ := indexAdd_correct ..

private def shiftR (x d z : ℕ) : NRel where
  form σ := indexShift (σ x) (σ d) (σ z)
  holds _ e := e z=e x*2^(e d)
  valid _ _ _ := indexShift_correct ..

private def topR (x : ℕ) : NRel where
  form σ := .neg (.many (.neg (.lt 0 (σ x).succ)))
  holds U e := U-U/2 ≤ e x
  valid {k U} σ A e := by
    simp only [Form.Holds,Fin.cases_zero,Fin.cases_succ,not_lt]
    have he : univ.filter (fun z : Fin U => e (σ x)≤z) = Ici (e (σ x)) := by ext; simp
    rw [he,Fin.card_Ici]
    omega

private def suffix (z s : ℕ) : NRel where
  form σ := .ex (.conj ((topR 0).form (fun _ => 0)) (indexAdd 0 (σ s).succ (σ z).succ))
  holds U e := U-U/2+e s≤e z
  valid {k U} σ A e := by
    simp only [Form.Holds,(topR 0).valid,indexAdd_correct,Fin.cases_zero,Fin.cases_succ]
    change (∃ w : Fin U, U-U/2≤w.val ∧ w.val+(e (σ s)).val=(e (σ z)).val) ↔ _
    constructor
    · rintro ⟨w,h,hh⟩; omega
    · intro h
      exact ⟨⟨(e (σ z)).val-(e (σ s)).val,by have := (e (σ z)).isLt; omega⟩,by dsimp; omega,by dsimp; omega⟩

local infixr:35 " ⋀ " => NRel.both
local infixr:34 " ⋁ " => NRel.either
private noncomputable def tally (extra : Bool) (p : NRel) : NRel :=
  NRel.maj 8 ((if extra then (lit 8 0 ⋁ p) else p) ⋁ suffix 8 2)

private theorem tally_spec (extra : Bool) (p : NRel) (U : ℕ) (e : ℕ→ℕ) (S : Finset ℕ)
    (hU : 0<U) (h0 : 0∉S) (hshort : ∀ j∈S,j<U-U/2) (ht : e 2≤U/2)
    (hh : ∀ j<U,p.holds U (Function.update e 8 j) ↔ j∈S) :
    (tally extra p).holds U e ↔ e 2 < S.card+extra.toNat := by
  let low := if extra then insert 0 S else S
  have lowCap (j : ℕ) (hj : j∈low) : j<U-U/2 := by
    cases extra with
    | false => exact hshort j hj
    | true =>
      rcases mem_insert.mp hj with rfl|h
      · omega
      · exact hshort j h
  let a := U-U/2+e 2
  have dis : Disjoint low (Ico a U) := by
    apply disjoint_left.mpr
    intro j hj hh'
    have := lowCap j hj
    have := (mem_Ico.mp hh').1
    dsimp [a] at *; omega
  have cardLow : low.card=S.card+extra.toNat := by cases extra <;> simp [low,h0]
  change U/2 < _ ↔ _
  have union : (range U).filter (fun j => ((if extra then lit 8 0 ⋁ p else p) ⋁ suffix 8 2).holds U (Function.update e 8 j)) =
      low ∪ Ico a U := by
    ext j
    by_cases hj : j<U
    · have hv := hh j hj
      simp only [mem_filter,mem_range,hj,true_and,mem_union,mem_Ico,and_true,NRel.either,suffix]
      cases extra <;> simp [lit,low,a,hv,Function.update]
    · have hl : j∉low := fun h => hj ((lowCap j h).trans_le (Nat.sub_le U _))
      simp [hj,hl]
  rw [union,card_union_of_disjoint dis,cardLow,Nat.card_Ico]
  dsimp [a]; omega

private def rectCell : NRel :=
  NRel.ex 9 <| NRel.ex 10 <| NRel.ex 11 <| NRel.ex 12 <|
    ltR 9 0 ⋀ ltR 10 1 ⋀ shiftR 9 3 11 ⋀ addR 11 10 12 ⋀ addR 12 7 8

private def ids (x y B : ℕ) : Finset ℕ :=
  ((range x) ×ˢ (range y)).image (fun p => p.1*B+p.2+1)

private theorem mem_ids (x y B z : ℕ) :
    z∈ids x y B ↔ ∃ r<x, ∃ c<y, r*B+c+1=z := by
  simp only [ids,mem_image,mem_product,mem_range,Prod.exists]
  constructor
  · rintro ⟨r,c,⟨hr,hc⟩,h⟩; exact ⟨r,hr,c,hc,h⟩
  · rintro ⟨r,hr,c,hc,h⟩; exact ⟨r,c,⟨hr,hc⟩,h⟩

private theorem card_ids (x y B : ℕ) (h : y≤B) : (ids x y B).card = x*y := by
  have inj : Set.InjOn (fun p : ℕ×ℕ => p.1*B+p.2+1) (↑((range x) ×ˢ range y)) := by
    rintro ⟨r,c⟩ ha ⟨s,d⟩ hb he
    have hc : c<B := (mem_range.mp (mem_product.mp ha).2).trans_le h
    have hd : d<B := (mem_range.mp (mem_product.mp hb).2).trans_le h
    change r*B+c+1=s*B+d+1 at he
    have he' := Nat.add_right_cancel he
    have hm := congrArg (fun z : ℕ => z%B) he'
    simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt hd] at hm
    subst d
    have : r=s := Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel he')
    simp [this]
  rw [ids,card_image_of_injOn inj,card_product,card_range,card_range]

private theorem ids_range {x y B z : ℕ} (hy : y≤B) (hz : z∈ids x y B) : 0<z ∧ z≤x*B := by
  obtain ⟨r,hr,c,hc,rfl⟩ := (mem_ids ..).mp hz
  have := Nat.mul_le_mul_right B hr
  rw [Nat.succ_mul] at this
  omega

private theorem rectCell_spec (e : ℕ→ℕ) (U : ℕ) (h1 : e 7=1)
    (hx : e 0<U) (hy : e 1<U) (hz : e 8<U) :
    rectCell.holds U e ↔ e 8∈ids (e 0) (e 1) (2^(e 3)) := by
  rw [mem_ids]
  change (∃ r<U, ∃ c<U, ∃ a<U, ∃ b<U, r<e 0 ∧ c<e 1 ∧ a=r*2^(e 3) ∧ a+c=b ∧ b+e 7=e 8) ↔ _
  constructor
  · rintro ⟨r,_,c,_,a,_,b,_,hr,hc,rfl,rfl,he⟩; exact ⟨r,hr,c,hc,by omega⟩
  · rintro ⟨r,hr,c,hc,he⟩
    exact ⟨r,hr.trans hx,c,hc.trans hy,_,by omega,_,by omega,hr,hc,rfl,rfl,by omega⟩

private noncomputable def core : NRel :=
  NRel.ex 3 <| NRel.ex 4 <| NRel.ex 5 <| NRel.ex 7 <|
    lit 7 1 ⋀ shiftR 7 3 4 ⋀ shiftR 0 3 5 ⋀ leR 1 4 ⋀ (topR 5).neg ⋀ leR 2 5 ⋀
    tally true rectCell ⋀ (tally false rectCell).neg

private theorem core_spec (U : ℕ) (e : ℕ→ℕ) (hx : e 0<U) (hy : e 1<U) :
    core.holds U e ↔ ∃ d<U, 2^d<U ∧ e 0*2^d<U-U/2 ∧ e 1≤2^d ∧ e 0*e 1=e 2 := by
  let f (d B cap one : ℕ) := Function.update (Function.update (Function.update (Function.update e 3 d) 4 B) 5 cap) 7 one
  have tallyIff (d B cap one : ℕ) (h1 : one=1) (hB : B=2^d) (hcap : cap=e 0*2^d)
      (hc : cap<U-U/2) (hb : e 1≤B) (hz : e 2≤cap) :
      ((tally true rectCell ⋀ (tally false rectCell).neg).holds U (f d B cap one)) ↔
        e 0 * e 1=e 2 := by
    let S := ids (e 0) (e 1) (2^d)
    have hr := fun (j : ℕ) (hj : j∈S) => ids_range (hB ▸ hb) hj
    have no0 : 0∉S := fun h => (hr 0 h).1.false
    have short := fun (j : ℕ) (hj : j∈S) => (hr j hj).2.trans_lt (hcap ▸ hc)
    have cover (j : ℕ) (hj : j<U) :
        rectCell.holds U (Function.update (f d B cap one) 8 j) ↔ j∈S :=
      rectCell_spec _ _ h1 hx hy (by simpa using hj)
    have t := fun b => tally_spec b rectCell U (f d B cap one) S (by omega) no0 short (by change e 2≤U/2;omega) cover
    change ((_ ∧ ¬_) ↔ _)
    rw [t true,t false,card_ids _ _ _ (hB ▸ hb)]
    change (e 2 < e 0 * e 1 + 1 ∧ ¬ e 2 < e 0 * e 1 + 0) ↔ _
    omega
  change (∃ d<U, ∃ B<U, ∃ cap<U, ∃ one<U, one=1 ∧ B=one*2^d ∧ cap=e 0*2^d ∧
    ¬ B<e 1 ∧ ¬ U-U/2≤cap ∧ ¬ cap<e 2 ∧ _) ↔ _
  constructor
  · rintro ⟨d,hd,B,hB,cap,hcap,one,hone,h1,hpow,hc,hb,hl,hz,ht⟩
    have hB' : B=2^d := by simpa [h1] using hpow
    exact ⟨d,hd,hB' ▸ hB,hc ▸ (by omega),by omega,(tallyIff _ _ _ _ h1 hB' hc (by omega) (by omega) (by omega)).mp ht⟩
  · rintro ⟨d,hd,hB,hc,hyB,he⟩
    have hz : e 2≤e 0*2^d := he ▸ Nat.mul_le_mul_left _ hyB
    refine ⟨d,hd,_,hB,_,hc.trans_le (Nat.sub_le U _),1,(Nat.one_le_two_pow).trans_lt hB,
      rfl,by simp,rfl,by omega,by omega,by omega,?_⟩
    exact (tallyIff _ _ _ _ rfl rfl rfl hc hyB hz).mpr he

/-- A rectangle cardinality in the HAB vocabulary for the natural index product. -/
noncomputable def indexSmallMul {k : ℕ} (x y z : Fin k) : Form k :=
  core.form (fun i => if i=0 then x else if i=1 then y else z)

theorem indexSmallMul_sound {k U : ℕ} (x y z : Fin k) (A : Matrix U) (e : Fin k→Fin U) :
    (indexSmallMul x y z).Holds A e → (e x).val*(e y).val=(e z).val := by
  rw [indexSmallMul,NRel.valid,core_spec _ _ (e x).isLt (e y).isLt]
  exact fun ⟨_,_,_,_,_,h⟩ => h

theorem indexSmallMul_complete {k U : ℕ} (x y z : Fin k) (A : Matrix U) (e : Fin k→Fin U)
    {d : ℕ} (hdy : (e y).val≤2^d) (hb : 2^d<U) (hcap : (e x).val*2^d<U-U/2)
    (hprod : (e x).val*(e y).val=(e z).val) : (indexSmallMul x y z).Holds A e := by
  rw [indexSmallMul,NRel.valid,core_spec _ _ (e x).isLt (e y).isLt]
  exact ⟨d,Nat.lt_two_pow_self.trans hb,hb,hcap,hdy,hprod⟩

end DiophantineNP.HAB
