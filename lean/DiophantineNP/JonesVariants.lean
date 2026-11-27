import DiophantineNP.JonesRegisters

/-! # Finite branches and affine register transitions for each TM2 instruction

The finite list of variants depends only on the instruction and entering finite
state. A successful branch enforces natural affine equalities between successive
register files. Reading a radix digit uses one natural quotient witness.
-/
namespace DiophantineNP.Classes.Jones.Machine
open Turing
open scoped Classical

abbrev File (tm : FinTM2) := tm.K → ℕ

inductive Op (tm : FinTM2) where
  | push (k : tm.K) (d : ℕ)
  | read (k : tm.K) (d : Fin (radix tm)) (drop : Bool)

def Op.Holds (tm : FinTM2) : Op tm → File tm → File tm → Prop
  | .push k d, R, R' => R' = Function.update R k (d + radix tm * R k)
  | .read k d drop, R, R' => ∃ q : ℕ, R k = radix tm * q + d.val ∧
      R' = (if drop then Function.update R k q else R)

private theorem read_iff (tm : FinTM2) (k : tm.K) (d : Fin (radix tm)) (drop : Bool) (R R') :
    Op.Holds tm (.read k d drop) R R' ↔
      R k % radix tm = d.val ∧ R' = (if drop then Function.update R k (R k / radix tm) else R) := by
  have hp : 0 < radix tm := by unfold radix; positivity
  constructor
  · rintro ⟨q,hq,hR⟩
    have hm : R k % radix tm = d.val := by rw [hq,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt d.isLt]
    have hd : R k / radix tm = q := by
      rw [hq,Nat.add_comm,Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt d.isLt,Nat.zero_add]
    exact ⟨hm,by rwa [hd]⟩
  · rintro ⟨hr,hR⟩
    exact ⟨_,by rw [← hr]; exact (Nat.div_add_mod (R k) (radix tm)).symm,hR⟩

def Chain (tm : FinTM2) : List (Op tm) → File tm → File tm → Prop
  | [], R, R' => R = R'
  | a :: ops, R, R' => ∃ R₁, a.Holds tm R R₁ ∧ Chain tm ops R₁ R'

structure Variant (tm : FinTM2) where
  ops : List (Op tm)
  label : Option tm.Λ
  state : tm.σ

def Variant.prepend {tm : FinTM2} (op : Op tm) (v : Variant tm) : Variant tm := {v with ops := op :: v.ops}

def Variant.Holds (tm : FinTM2) (v : Variant tm) (R : File tm) (c : Registers tm) :=
  v.label = c.label ∧ v.state = c.state ∧ Chain tm v.ops R c.stack

noncomputable def variants (tm : FinTM2) : tm.Stmt → tm.σ → List (Variant tm)
  | .push k f q, s => (variants tm q s).map (Variant.prepend (.push k (digit tm ⟨k,f s⟩)))
  | .peek k f q, s => (List.finRange (radix tm)).flatMap fun d =>
      (variants tm q (f s (peekValue tm k d.val))).map (Variant.prepend (.read k d false))
  | .pop k f q, s => (List.finRange (radix tm)).flatMap fun d =>
      (variants tm q (f s (peekValue tm k d.val))).map (Variant.prepend (.read k d true))
  | .load f q, s => variants tm q (f s)
  | .branch f q₁ q₂, s => cond (f s) (variants tm q₁ s) (variants tm q₂ s)
  | .goto f, s => [⟨[],some (f s),s⟩]
  | .halt, s => [⟨[],none,s⟩]

private theorem prepended (tm : FinTM2) (vs : List (Variant tm)) (op : Op tm) (R : File tm)
    (C : Registers tm) :
    (∃ v ∈ vs.map (Variant.prepend op), v.Holds tm R C) ↔
      ∃ R', op.Holds tm R R' ∧ ∃ v ∈ vs, v.Holds tm R' C := by
  constructor
  · rintro ⟨v,hv,hh⟩
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    obtain ⟨hl,hs,R',hstep,hchain⟩ := hh
    exact ⟨R',hstep,w,hw,hl,hs,hchain⟩
  · rintro ⟨R',hstep,w,hw,hl,hs,hchain⟩
    exact ⟨_,List.mem_map.mpr ⟨w,hw,rfl⟩,hl,hs,R',hstep,hchain⟩

private theorem peekValue_residue (tm : FinTM2) (k : tm.K) (n : ℕ) :
    peekValue tm k (n % radix tm) = peekValue tm k n := by simp [peekValue]

private theorem variants_read (tm : FinTM2) (k : tm.K) (drop : Bool) (f : Option (tm.Γ k) → tm.σ)
    (q : tm.Stmt) (R : File tm) (C : Registers tm) :
    (∃ v ∈ ((List.finRange (radix tm)).flatMap fun d =>
      (variants tm q (f (peekValue tm k d.val))).map (Variant.prepend (.read k d drop))),
        v.Holds tm R C) ↔
      ∃ v ∈ variants tm q (f (peekValue tm k (R k))),
        v.Holds tm (if drop then Function.update R k (R k / radix tm) else R) C := by
  constructor
  · rintro ⟨v,hv,h⟩
    obtain ⟨d,hd,hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨R',hd,Rw⟩ := (prepended tm _ (.read k d drop) R C).mp ⟨v,hv,h⟩
    obtain ⟨hr,rfl⟩ := (read_iff tm _ _ _ _ _).mp hd
    rwa [← hr,peekValue_residue] at Rw
  · intro h
    let d : Fin (radix tm) := ⟨R k % radix tm,Nat.mod_lt _ (by unfold radix; positivity)⟩
    have h' : ∃ v ∈ variants tm q (f (peekValue tm k d.val)),
        v.Holds tm (if drop then Function.update R k (R k / radix tm) else R) C := by
      simpa [d,peekValue_residue] using h
    obtain ⟨v,hv,hv'⟩ := (prepended tm _ (.read k d drop) R C).mpr
      ⟨_,(read_iff tm _ _ _ _ _).mpr ⟨rfl,rfl⟩,h'⟩
    exact ⟨_,List.mem_flatMap.mpr ⟨d,List.mem_finRange _,hv⟩,hv'⟩

/-- The constant finite disjunction of register branches captures a full TM2
macrostep, with its precise order of stack observations and updates. -/
theorem variants_exact (tm : FinTM2) (q : tm.Stmt) (s : tm.σ) (R : File tm) (C : Registers tm) :
    (∃ v ∈ variants tm q s, v.Holds tm R C) ↔ regAux tm q s R = C := by
  induction q generalizing s R with
  | push k f q ih =>
    rw [variants,prepended]
    simpa [Op.Holds,regAux] using ih s (Function.update R k (digit tm ⟨k,f s⟩ + radix tm * R k))
  | peek k f q ih =>
    rw [variants,variants_read]
    exact ih _ R
  | pop k f q ih =>
    rw [variants,variants_read]
    exact ih _ _
  | load f q ih => exact ih _ R
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases h : f s <;> simp [variants,regAux,h,ih₁,ih₂]
  | goto f =>
    obtain ⟨l,c,T⟩ := C
    simp [variants,Variant.Holds,regAux,Chain,Registers.mk.injEq]
  | halt =>
    obtain ⟨l,c,T⟩ := C
    simp [variants,Variant.Holds,regAux,Chain,Registers.mk.injEq]

end DiophantineNP.Classes.Jones.Machine
