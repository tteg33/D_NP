import DiophantineNP.HABSourceArithmetic
import Mathlib.Data.Nat.Log

/-! # Completing bounded index multiplication with two halvings

For a true relation `x*y=z` all three values fit the universe. Halving
`x` twice ensures that a padded rectangle encoding the product has
size less than half the universe. Four doubling/addition gates restore
the original product, with every intermediate value at most the output. -/
namespace DiophantineNP.HAB
open Counting WidthFormula

private def succIdx {k} (i j : Fin k) : Form k :=
  .ex (.conj (indexNat 1 0) (indexAdd i.succ 0 j.succ))

private theorem succIdx_spec {k U} (i j : Fin k) (A : Matrix U) (e : Fin k→Fin U) :
    (succIdx i j).Holds A e ↔ (e i).val+1=(e j).val := by
  simp only [succIdx,Form.Holds,indexNat_correct,indexAdd_correct,Fin.cases_zero,Fin.cases_succ]
  constructor
  · rintro ⟨v,hv,he⟩; omega
  · intro h; exact ⟨⟨1,by have := (e j).isLt; omega⟩,rfl,h⟩

/-- Expand a product relation to twice the first operand, optionally plus one. -/
private def twice (p : Form 3) : Form 3 :=
  .ex (.ex (.ex (.ex (.conj (p.rename ![3,5,2]) (.conj (indexAdd 3 3 1)
    (.conj (indexAdd 2 2 0) (.disj (.conj (.eq 1 4) (.eq 0 6))
        (.conj (succIdx 1 4) (indexAdd 0 5 6)))))))))

private theorem twice_iff (p : Form 3) {U} (A : Matrix U) (e : Fin 3 → Fin U) :
    (twice p).Holds A e ↔ ∃ q w : Fin U, p.Holds A ![q,e 1,w] ∧
      (((e 0).val=q.val+q.val ∧ (e 2).val=w.val+w.val) ∨
       ((e 0).val=q.val+q.val+1 ∧ (e 2).val=w.val+w.val+(e 1).val)) := by
  let E (q w t v : Fin U) : Fin 7 → Fin U := Fin.cases v (Fin.cases t (Fin.cases w (Fin.cases q e)))
  have args (q w t v : Fin U) : E q w t v ∘ ![3,5,2] = ![q,e 1,w] := by
    funext i; fin_cases i <;> rfl
  change (∃ q w t v : Fin U, (p.rename ![3,5,2]).Holds A (E q w t v) ∧
    (indexAdd 3 3 1).Holds A (E q w t v) ∧ (indexAdd 2 2 0).Holds A (E q w t v) ∧
    ((_ ∧ _) ∨ ((succIdx 1 4).Holds A (E q w t v) ∧ (indexAdd 0 5 6).Holds A (E q w t v)))) ↔ _
  simp only [Form.rename_correct,args,indexAdd_correct,succIdx_spec]
  change (∃ q w t v : Fin U, p.Holds A ![q,e 1,w] ∧
    q.val+q.val=t.val ∧ w.val+w.val=v.val ∧
     ((t=e 0 ∧ v=e 2) ∨ (t.val+1=(e 0).val ∧ v.val+(e 1).val=(e 2).val))) ↔ _
  constructor
  · rintro ⟨q,w,t,v,hp,ht,hv,⟨rfl,rfl⟩|⟨h1,h2⟩⟩
    · exact ⟨q,w,hp,Or.inl ⟨ht.symm,hv.symm⟩⟩
    · exact ⟨q,w,hp,Or.inr ⟨by omega,by omega⟩⟩
  · rintro ⟨q,w,hp,⟨ht,hv⟩|⟨ht,hv⟩⟩
    · exact ⟨q,w,e 0,e 2,hp,ht.symm,hv.symm,Or.inl ⟨rfl,rfl⟩⟩
    · refine ⟨q,w,⟨q.val+q.val,by have := (e 0).isLt;omega⟩,
        ⟨w.val+w.val,by have := (e 2).isLt;omega⟩,hp,rfl,rfl,Or.inr ⟨ht.symm,hv.symm⟩⟩

private theorem twice_sound {p : Form 3} {U} (A : Matrix U)
    (hs : ∀ e : Fin 3→Fin U, p.Holds A e → (e 0).val*(e 1).val=(e 2).val)
    (e : Fin 3→Fin U) (h : (twice p).Holds A e) : (e 0).val*(e 1).val=(e 2).val := by
  obtain ⟨q,w,hp,ha⟩ := (twice_iff p A e).mp h
  have he : q.val*(e 1).val=w.val := hs _ hp
  rcases ha with ⟨hx,hz⟩|⟨hx,hz⟩ <;> rw [hx,hz] <;> simp [Nat.add_mul,he]

private theorem twice_complete {p : Form 3} {U} (A : Matrix U) (e : Fin 3→Fin U)
    (he : (e 0).val*(e 1).val=(e 2).val)
    (hsmall : ∀ q w : Fin U, q.val=(e 0).val/2 → w.val=q.val*(e 1).val →
      p.Holds A ![q,e 1,w]) : (twice p).Holds A e := by
  let x := (e 0).val
  let y := (e 1).val
  let q : Fin U := ⟨x/2,(Nat.div_le_self ..).trans_lt (e 0).isLt⟩
  let w : Fin U := ⟨q.val*y, (Nat.mul_le_mul_right _ (Nat.div_le_self ..)).trans_lt (he ▸ (e 2).isLt)⟩
  have hp := hsmall q w rfl rfl
  apply (twice_iff p A e).mpr
  refine ⟨q,w,hp,?_⟩
  have hq : q.val=x/2 := rfl
  have hw : w.val=q.val*(e 1).val := rfl
  by_cases even : x= q.val+q.val
  · have hx : (e 0).val=q.val+q.val := even
    exact Or.inl ⟨hx,by rw [←he,hx,hw,Nat.add_mul]⟩
  · have hx : (e 0).val=q.val+q.val+1 := by change x=_; omega
    exact Or.inr ⟨hx,by rw [←he,hx,hw];simp [Nat.add_mul]⟩

private def smallCase : Form 3 :=
  .disj (.conj (.disj (indexNat 0 0) (indexNat 0 1)) (indexNat 0 2))
    (.conj (indexNat 1 0) (.eq 1 2))

/-- A padded-rectangle product graph for half the universe suffices to express
the entire bounded numerical multiplication graph in the source vocabulary. -/
def extendSmallMul (p : Form 3) : Form 3 := .disj smallCase (twice (twice p))

private theorem smallCase_iff {U} (A : Matrix U) (e : Fin 3→Fin U) :
    smallCase.Holds A e ↔
    (((e 0).val=0 ∨ (e 1).val=0) ∧ (e 2).val=0) ∨ ((e 0).val=1 ∧ e 1 = e 2) := by
  simp only [smallCase,Form.Holds,indexNat_correct]

/-- The base relation needs no behavior on oversized rectangles beyond soundness. -/
theorem extendSmallMul_correct (p : Form 3) {U} (A : Matrix U)
    (sound : ∀ e : Fin 3→Fin U, p.Holds A e → (e 0).val*(e 1).val=(e 2).val)
    (complete : ∀ e : Fin 3→Fin U, ∀ d : ℕ, 1<U → (e 1).val≤2^d → 2^d<U →
      (e 0).val*2^d < U-U/2 → (e 0).val*(e 1).val=(e 2).val → p.Holds A e)
    (e : Fin 3→Fin U) : (extendSmallMul p).Holds A e ↔ (e 0).val*(e 1).val=(e 2).val := by
  change (smallCase.Holds A e ∨ _) ↔ _
  rw [smallCase_iff]
  constructor
  · rintro (hs|ht)
    · rcases hs with ⟨h|h,r⟩|⟨h,r⟩ <;> simp [h,r]
    · exact twice_sound A (twice_sound A sound) e ht
  · intro he
    by_cases hy : (e 1).val=0
    · exact Or.inl (Or.inl ⟨Or.inr hy,by simpa [hy] using he.symm⟩)
    by_cases hx0 : (e 0).val=0
    · exact Or.inl (Or.inl ⟨Or.inl hx0,by simpa [hx0] using he.symm⟩)
    by_cases hx1 : (e 0).val=1
    · exact Or.inl (Or.inr ⟨hx1,Fin.ext (by simpa [hx1] using he)⟩)
    have hsize := (e 2).isLt
    let d := Nat.clog 2 (e 1).val
    have hyB : (e 1).val≤2^d := Nat.le_pow_clog (by decide) _
    have hBy : 2^d ≤ 2*(e 1).val := by
      cases hd : d with
      | zero => simp; omega
      | succ k =>
        have hlt : k < Nat.clog 2 (e 1).val := by change k < d; omega
        have lower := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mp hlt
        rw [pow_succ]; omega
    have h2 : 2≤(e 0).val := by omega
    have hBU : 2^d<U := hBy.trans_lt <| (Nat.mul_le_mul_right _ h2).trans_lt (he ▸ hsize)
    right
    apply twice_complete A e he
    intro q w hq hw
    apply twice_complete A ![q,e 1,w] hw.symm
    intro q' w' hq' hw'
    change q'.val = q.val/2 at hq'
    change w'.val=q'.val*(e 1).val at hw'
    apply complete ![q',e 1,w'] d (by omega) hyB hBU _ hw'.symm
    change q'.val*2^d<U-U/2
    have hq4 : 4*q'.val ≤ (e 0).val := by omega
    have ha := Nat.mul_le_mul_right (e 1).val hq4
    have hb := Nat.mul_le_mul_left q'.val hBy
    have ha' : (q'.val * (2*(e 1).val))*2 ≤ (e 2).val := by
      rw [←he]; convert ha using 1; ring
    omega

end DiophantineNP.HAB
