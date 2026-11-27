import DiophantineNP.HABPolylogRange
import DiophantineNP.HABSumParameters

/-! # Selecting a polylogarithmic bit budget in the finite structure

The first unrepresented power of two defines a bit width. For a fixed d,
a formula chooses that width to the d-th power plus two headroom bits.
-/
namespace DiophantineNP.HABShortLength
open Counting WidthFormula FiniteArithmeticGap PrimeFormula

def width (U : ℕ) := (U-1).log2+1
def bits (d U : ℕ) := width U ^ d + 2

private def powFits {k} (x : Fin k) : Template k := .ex (fromFormula (powerAt 0 x.succ))

private theorem powFits_spec {k U} (x : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U) :
    (powFits x).eval A e=true ↔ 2^(e x).val<U := by
  simp only [powFits,Tex_true,fromFormula_eval,powerAt_spec,Fin.cases_zero,Fin.cases_succ]
  exact ⟨fun ⟨b,h⟩ => h ▸ b.isLt,fun h => ⟨⟨_,h⟩,rfl⟩⟩

private def firstMissing {k} (w : Fin k) : Template k :=
  .conj (.neg (powFits w)) (.ex (.conj (powFits 0) (.ex
    (.conj (fromFormula (isNat 1 0)) (.atom (.add 1 0 w.succ.succ))))))

private theorem width_bounds {U} (hU : 2≤U) :
    2^((U-1).log2)<U ∧ U≤2^(width U) := by
  have a := Nat.log2_self_le (by omega : U-1≠0)
  have b := Nat.lt_log2_self (n:=U-1)
  unfold width
  omega

private theorem firstMissing_spec {k U} (w : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U) (hU : 2≤U) :
    (firstMissing w).eval A e=true ↔ (e w).val=width U := by
  obtain ⟨lo,hi⟩ := width_bounds hU
  simp only [firstMissing,Tconj_true,Template.eval.eq_4,Bool.not_eq_true',←Bool.not_eq_true,powFits_spec,
    Tex_true,fromFormula_eval,isNat_spec,Fin.cases_zero,not_lt]
  change (U≤2^(e w).val ∧ ∃ j : Fin U, 2^j.val<U ∧ ∃ a : Fin U, a.val=1 ∧
    decide (j.val+a.val=(e w).val)=true) ↔ _
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨h,j,f,a,ha,he⟩
    have x : (U-1).log2 < (e w).val := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (lo.trans_le h)
    have y : j.val < width U := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (f.trans_le hi)
    unfold width at *; omega
  · intro h
    exact ⟨h ▸ hi,⟨(U-1).log2,((Nat.lt_two_pow_self).trans lo)⟩,lo,⟨1,by omega⟩,rfl,h.symm⟩

private abbrev push {k U : ℕ} (z : Fin U) (e : Fin k→Fin U) : Fin (k+1)→Fin U := Fin.cases z e

private def fixedPower : (d : ℕ) → {k : ℕ} → Fin k → Fin k → Template k
  | 0,_,_,y => fromFormula (isNat 1 y)
  | d+1,_,x,y => .ex (.conj (fixedPower d x.succ 0) (.atom (.mul 0 x.succ y.succ)))

private theorem fixedPower_spec (d : ℕ) {k U} (x y : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U)
    (hx : 0<(e x).val) :
    (fixedPower d x y).eval A e=true ↔ (e x).val^d=(e y).val := by
  induction d generalizing k with
  | zero => rw [fixedPower,fromFormula_eval,isNat_spec,pow_zero]; exact eq_comm
  | succ d ih =>
    rw [fixedPower,Tex_true]
    simp only [Tconj_true]
    change (∃ z : Fin U, (fixedPower d x.succ 0).eval A (Fin.cases z e)=true ∧
      decide (z.val*(e x).val=(e y).val)=true) ↔ _
    have h (z : Fin U) := ih x.succ 0 (push z e) hx
    change (∃ z : Fin U, (fixedPower d x.succ 0).eval A (push z e)=true ∧ _) ↔ _
    simp only [h,decide_eq_true_eq,pow_succ,push,Fin.cases_zero,Fin.cases_succ]
    constructor
    · rintro ⟨z,hz,he⟩; rwa [hz]
    · intro he
      have hz := Nat.le_mul_of_pos_right ((e x).val^d) hx
      exact ⟨⟨_,hz.trans_lt (he.symm ▸ (e y).isLt)⟩,rfl,he⟩

def parameter {k} (d : ℕ) (b : Fin k) : Template k :=
  .ex (.conj (firstMissing 0) (.ex (.conj (fixedPower d 1 0) (.ex
    (.conj (fromFormula (isNat 2 0)) (.atom (.add 1 0 b.succ.succ.succ)))))))

theorem parameter_correct {k U} (d : ℕ) (b : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U)
    (hU : 3≤U) (hw : width U<U) :
    (parameter d b).eval A e=true ↔ (e b).val=bits d U := by
  simp only [parameter,Tex_true,Tconj_true,firstMissing_spec _ _ _ (by omega : 2≤U),
    fromFormula_eval,isNat_spec,Fin.cases_zero]
  have test (w x : Fin U) (h : w.val=width U) :
    (fixedPower d (1 : Fin (k+2)) 0).eval A (extend x w e)=true ↔ width U^d=x.val := by
    have h' := fixedPower_spec d (1 : Fin (k+2)) 0 A (extend x w e) (by change 0<w.val; simp [h,width])
    simpa only [show extend x w e 1=w from rfl,show extend x w e 0=x from rfl,h] using h'
  change (∃ w : Fin U, w.val=width U ∧ ∃ x : Fin U,
    (fixedPower d (1 : Fin (k+2)) 0).eval A (extend x w e)=true ∧ ∃ a : Fin U, a.val=2 ∧
    decide (x.val+a.val=(e b).val)=true) ↔ _
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨w,h,x,hx,a,ha,he⟩
    exact he.symm.trans (by rw [ha,←(test w x h).mp hx]; rfl)
  · intro h
    let w : Fin U := ⟨width U,hw⟩
    let x : Fin U := ⟨width U^d,by have := (e b).isLt; unfold bits at h; omega⟩
    exact ⟨w,rfl,x,(test w x rfl).mpr rfl,⟨2,by omega⟩,rfl,h.symm⟩

theorem parameters {U : ℕ} (d : ℕ) (large : HABPolylogRange.threshold (4*(2*d+2)+9)≤U) (h4 : 4≤U) :
    U.log2^d+2≤bits d U ∧ bits d U≤U.log2^(2*d+2) ∧ bits d U<U ∧ width U<U := by
  let l := U.log2
  obtain ⟨hlo,hhi⟩ := width_bounds (by omega : 2≤U)
  have lpos : 2≤l := (Nat.le_log2 (by omega : U≠0)).mpr h4
  have low : l≤width U := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp ((Nat.log2_self_le (by omega : U≠0)).trans hhi)
  have high : width U≤l+1 := Nat.succ_le_succ ((Nat.le_log2 (by omega : U≠0)).mpr hlo.le)
  have sq : width U≤l^2 := by nlinarith [Nat.mul_le_mul_left l lpos]
  have maxBit : bits d U≤l^(2*d+2) := calc
    _ = width U^d+2 := rfl
    _ ≤ (l^2)^d+2 := Nat.add_le_add_right (Nat.pow_le_pow_left sq _) _
    _ ≤ l^(2*d+2) := by
      rw [←pow_mul,pow_add]
      have hz : 1≤l^(2*d) := Nat.one_le_pow _ _ (by omega)
      have hz' := Nat.mul_le_mul_left (l^(2*d)) (by nlinarith : 3≤l^2)
      omega
  obtain ⟨hK,hp,cap⟩ := HABPolylogRange.range_covered (p:=0) large (Nat.zero_le _)
  have below (n : ℕ) (hn : n≤l^(2*d+2)) : n<U := by
    have he : 2*d+2≤4*(2*d+2)+9 := by omega
    have hwide := HABPolylogRange.range_covered large (p:=n) (hn.trans (Nat.pow_le_pow_right (by omega) he))
    exact (hwide.2.1.trans (Nat.pow_le_pow_right (by decide)
      (Nat.le_mul_of_pos_left _ (by omega)))).trans_lt cap
  have hw : width U<U := below _ (sq.trans (Nat.pow_le_pow_right (by omega) (by omega)))
  exact ⟨Nat.add_le_add_right (Nat.pow_le_pow_left low d) 2,maxBit,below _ maxBit,hw⟩

end DiophantineNP.HABShortLength
