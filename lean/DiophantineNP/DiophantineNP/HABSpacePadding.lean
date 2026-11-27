import DiophantineNP.HABPairInterpretation

/-! # Fixed polynomial padding of finite arithmetic formulas

Embed each numerical parameter in the leading interval of a larger structure,
keep the original input relation in its leading square, and set all other
entries to false. Repeated square interpretations give one fixed base-domain
formula for any prescribed number of squarings. -/
namespace DiophantineNP.HABSpacePadding
open Counting PrimeFormula WidthFormula FiniteArithmeticGap HAB HABPairInterpretation

private def corner : Input := fun rh rl ch cl =>
  .conj (fromFormula (isNat 0 rh)) (.conj (fromFormula (isNat 0 ch)) (.entry rl cl))

/-- Copy the input into the leading square of a structure of size U². -/
def widen {U : ℕ} (A : Matrix U) : Matrix (U*U) := fun x y =>
  let r := finProdFinEquiv.symm x
  let c := finProdFinEquiv.symm y
  if r.1.val=0 ∧ c.1.val=0 then A r.2 c.2 else false

private theorem corner_spec {U k : ℕ} (A : Matrix U) (rh rl ch cl : Fin k) (e : Fin k→Fin U) :
    (corner rh rl ch cl).eval A e=widen A (code (e rh) (e rl)) (code (e ch) (e cl)) := by
  apply Bool.eq_iff_iff.mpr
  simp [corner,Tconj_true,isNat_spec,widen,code,and_assoc]

private def point {U : ℕ} (x : Fin U) : Fin (U*U) := code ⟨0,Fin.pos x⟩ x

private theorem point_val {U : ℕ} (x : Fin U) : (point x).val=x.val := by
  simp [point,code]

private noncomputable def once {k : ℕ} (p : Template k) : Template k :=
  .ex (.conj (fromFormula (isNat 0 0)) (compileTemplate @corner p (fun _ => 0) Fin.succ))

private theorem once_spec {k U : ℕ} (p : Template k) (A : Matrix U) (e : Fin k→Fin U)
    (hp : 0<U) : (once p).eval A e = p.eval (widen A) (point ∘ e) := by
  apply Bool.eq_iff_iff.mpr
  rw [once,Tex_true]
  simp only [Tconj_true,fromFormula_eval,isNat_spec,Fin.cases_zero]
  have step (z : Fin U) (hz : z.val=0) :
      (compileTemplate @corner p (fun _ => 0) Fin.succ).eval A (Fin.cases z e) =
      p.eval (widen A) (point ∘ e) := by
    rw [compileTemplate_correct @corner p _ _ A (widen A) _ (fun rh rl ch cl env =>
      corner_spec A rh rl ch cl env)]
    apply congrArg (p.eval (widen A))
    funext i
    change code z (e i)=code ⟨0,_⟩ (e i)
    exact congrArg (fun h => code h (e i)) (Fin.ext hz)
  constructor
  · rintro ⟨z,hz,h⟩; rwa [step z hz] at h
  · exact fun h => ⟨⟨0,hp⟩,rfl,(step _ rfl).trans h⟩

/-- Width after d squarings. -/
def size (U : ℕ) : ℕ → ℕ
  | 0 => U
  | d+1 => size U d * size U d

theorem size_eq (U d : ℕ) : size U d = U^(2^d) := by
  induction d with
  | zero => simp [size]
  | succ d ih => simp only [size,ih,pow_succ (a:=2)]; rw [Nat.mul_two,pow_add]

theorem size_pos {U : ℕ} (h : 0<U) (d : ℕ) : 0<size U d := by
  rw [size_eq]; positivity

/-- Lift every index without changing its numerical value. -/
def index {U : ℕ} (i : Fin U) : (d : ℕ) → Fin (size U d)
  | 0 => i
  | d+1 => point (index i d)

@[simp] theorem index_val {U : ℕ} (i : Fin U) (d : ℕ) : (index i d).val=i.val := by
  induction d with
  | zero => rfl
  | succ d ih => exact (point_val _).trans ih

/-- The uniformly zero-padded input after d squarings. -/
def matrix {U : ℕ} (A : Matrix U) : (d : ℕ) → Matrix (size U d)
  | 0 => A
  | d+1 => widen (matrix A d)

private theorem widen_true {U : ℕ} (A : Matrix U) (x y : Fin (U*U)) :
    widen A x y=true ↔ ∃ r c : Fin U, point r=x ∧ point c=y ∧ A r c=true := by
  obtain ⟨⟨rh,rl⟩,rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨ch,cl⟩,rfl⟩ := finProdFinEquiv.surjective y
  simp only [widen,Equiv.symm_apply_apply,point,code,EmbeddingLike.apply_eq_iff_eq,
    Prod.mk.injEq,Fin.ext_iff]
  constructor
  · intro hv
    split at hv
    · rename_i hh
      exact ⟨rl,cl,⟨hh.1.symm,rfl⟩,⟨hh.2.symm,rfl⟩,hv⟩
    · contradiction
  · rintro ⟨r,c,⟨hr,hrl⟩,⟨hc,hcl⟩,v⟩
    rw [if_pos ⟨hr.symm,hc.symm⟩,←Fin.ext hrl,←Fin.ext hcl]
    exact v

/-- In the enlarged matrix exactly the original leading square can contribute. -/
theorem matrix_true {U : ℕ} (A : Matrix U) (d : ℕ) (x y : Fin (size U d)) :
    matrix A d x y=true ↔ ∃ r c : Fin U, (r.val=x.val ∧ c.val=y.val) ∧ A r c=true := by
  induction d with
  | zero =>
    constructor
    · exact fun h => ⟨x,y,⟨rfl,rfl⟩,h⟩
    · rintro ⟨r,c,⟨hr,hc⟩,v⟩
      exact Fin.ext hr ▸ Fin.ext hc ▸ v
  | succ d ih =>
    rw [matrix,widen_true]
    constructor
    · rintro ⟨i,j,rfl,rfl,v⟩
      rw [ih] at v
      simpa only [point_val] using v
    · rintro ⟨r,c,⟨hr,hc⟩,v⟩
      refine ⟨index r d,index c d,Fin.ext ?_,Fin.ext ?_,(ih _ _).mpr ?_⟩
      · simpa only [point_val,index_val] using hr
      · simpa only [point_val,index_val] using hc
      · exact ⟨r,c,⟨(index_val r d).symm,(index_val c d).symm⟩,v⟩

/-- Compile the formula on a prescribed polynomial-size ambient universe. -/
noncomputable def pad {k : ℕ} : ℕ → Template k → Template k
  | 0,p => p
  | d+1,p => pad d (once p)

theorem pad_correct {k U : ℕ} (d : ℕ) (p : Template k) (A : Matrix U) (e : Fin k→Fin U)
    (hU : 0<U) : (pad d p).eval A e = p.eval (matrix A d) (fun j => index (e j) d) := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih =>
    rw [pad,ih,once_spec _ _ _ (size_pos hU d)]
    rfl

/-- Six squarings suffice for the numerical allowance in the prime-power
certificate for every element of a base domain of size at least two. -/
theorem power_budget {U : ℕ} (hU : 2≤U) (p : Fin U) : (p.val+2)^30≤size U 6 := by
  have h : p.val+2 ≤ U^2 := by
    have := p.isLt
    nlinarith [Nat.mul_le_mul_right U hU]
  rw [size_eq]
  calc (p.val+2)^30 ≤ (U^2)^30 := Nat.pow_le_pow_left h _
       _ = U^60 := by ring
       _ ≤ U^(2^6) := Nat.pow_le_pow_right (by omega) (by decide)

end DiophantineNP.HABSpacePadding
