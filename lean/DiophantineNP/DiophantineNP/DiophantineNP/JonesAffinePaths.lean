import DiophantineNP.JonesAffineRows

/-! # A fixed finite affine system for a complete TM2 branch -/
namespace DiophantineNP.Classes.Jones.Machine
open Turing JMTableau
open scoped Classical
attribute [local instance] FinTM2.kFin

/-- The intermediate register files and the read quotients of a branch can be
arranged in arrays whose lengths are fixed by the machine instruction. -/
theorem chain_iff_rows (tm : FinTM2) (ops : List (Op tm)) (R T : File tm) :
    Chain tm ops R T ↔ ∃ (rows : Fin (ops.length+1) → File tm) (quot : Fin ops.length → ℕ),
      rows 0 = R ∧ rows (Fin.last ops.length) = T ∧
      ∀ i : Fin ops.length, (ops.get i).HoldsWith tm (rows i.castSucc) (rows i.succ) (quot i) := by
  induction ops generalizing R with
  | nil =>
    constructor
    · intro h; exact ⟨fun _ => R,Fin.elim0,rfl,h,fun i => Fin.elim0 i⟩
    · rintro ⟨rows,_,h₀,h₁,_⟩; exact h₀.symm.trans h₁
  | cons a ops ih =>
    simp only [List.length_cons] at *
    constructor
    · rintro ⟨R',ha,ht⟩
      obtain ⟨u,hu⟩ := (holdsWith_iff tm a _ _).mpr ha
      obtain ⟨rows,quot,h₀,h₁,hops⟩ := (ih R').mp ht
      refine ⟨Fin.cons R rows,Fin.cons u quot,Fin.cons_zero ..,?_,?_⟩
      · change (Fin.cons (α := fun _ => File tm) R rows) (Fin.last ops.length).succ = T
        simp only [Fin.cons_succ]; exact h₁
      · intro i; refine Fin.cases ?_ (fun j => ?_) i
        · simpa [h₀] using hu
        · simpa [Fin.castSucc_succ] using hops j
    · rintro ⟨rows,quot,h₀,h₁,hops⟩
      refine ⟨rows (Fin.succ 0),(holdsWith_iff tm a _ _).mp ⟨quot 0,?_⟩,?_⟩
      · simpa [h₀] using hops 0
      · apply (ih _).mpr
        refine ⟨fun j => rows j.succ,fun j => quot j.succ,rfl,h₁,fun j => ?_⟩
        simpa [Fin.castSucc_succ] using hops j.succ

abbrev Cells (tm : FinTM2) (n : ℕ) := (Fin (n+1) × tm.K) ⊕ Fin n

noncomputable def cellIndex (tm : FinTM2) (n : ℕ) := Fintype.equivFin (Cells tm n)

abbrev cellCount (tm : FinTM2) (n : ℕ) := Fintype.card (Cells tm n)

noncomputable def rowCell (tm : FinTM2) {n} (j : Fin (n+1)) (k : tm.K) : Fin (cellCount tm n) :=
  cellIndex tm n (.inl (j,k))

noncomputable def quotCell (tm : FinTM2) {n} (i : Fin n) : Fin (cellCount tm n) := cellIndex tm n (.inr i)

/-- All the intermediate assignments and quotient slots are shared between
adjacent primitives. Flattening their conjunction yields a finite list. -/
noncomputable def pathEquations (tm : FinTM2) (ops : List (Op tm)) : List (Equation (cellCount tm ops.length)) :=
  (List.finRange ops.length).flatMap fun i => opEquations tm (rowCell tm i.castSucc) (rowCell tm i.succ)
    (quotCell tm i) (ops.get i)

private theorem path_rows_iff (tm : FinTM2) (ops : List (Op tm)) (x) : Satisfies (pathEquations tm ops) x ↔
    ∀ i : Fin ops.length, (ops.get i).HoldsWith tm (x ∘ rowCell tm i.castSucc) (x ∘ rowCell tm i.succ)
      (x (quotCell tm i)) := by
  constructor
  · intro h i
    apply (opEquations_exact ..).mp
    intro p hp; exact h p (List.mem_flatMap.mpr ⟨i,List.mem_finRange _,hp⟩)
  · intro h p hp
    obtain ⟨i,_,hp⟩ := List.mem_flatMap.mp hp
    exact (opEquations_exact ..).mpr (h i) p hp

theorem pathEquations_exact (tm : FinTM2) (ops : List (Op tm)) (R T : File tm) :
    Chain tm ops R T ↔ ∃ x : Fin (cellCount tm ops.length) → ℕ,
      x ∘ rowCell tm 0 = R ∧ x ∘ rowCell tm (Fin.last ops.length) = T ∧ Satisfies (pathEquations tm ops) x := by
  rw [chain_iff_rows]
  constructor
  · rintro ⟨rows,quot,h₀,h₁,h⟩
    let f : Cells tm ops.length → ℕ := Sum.elim (fun t => rows t.1 t.2) quot
    let x := f ∘ (cellIndex tm ops.length).symm
    have hr (i : Fin (ops.length+1)) : x ∘ rowCell tm i = rows i := by funext j; simp [x,f,rowCell]
    have hq (i : Fin ops.length) : x (quotCell tm i) = quot i := by simp [x,f,quotCell]
    exact ⟨x,(hr 0).trans h₀,(hr _).trans h₁,(path_rows_iff tm ops x).mpr (fun i => by simpa only [hr,hq] using h i)⟩
  · rintro ⟨x,h₀,h₁,h⟩
    exact ⟨fun i => x ∘ rowCell tm i,fun i => x (quotCell tm i),h₀,h₁,(path_rows_iff tm ops x).mp h⟩

/-- A macroinstruction is an exact finite disjunction of systems of affine
natural equations, including the determined control label and state at exit. -/
theorem macro_affine_iff (tm : FinTM2) (q : tm.Stmt) (s : tm.σ) (R : File tm) (C : Registers tm) :
    regAux tm q s R = C ↔ ∃ v ∈ variants tm q s, v.label = C.label ∧ v.state = C.state ∧
      ∃ x : Fin (cellCount tm v.ops.length) → ℕ, x ∘ rowCell tm 0 = R ∧
      x ∘ rowCell tm (Fin.last v.ops.length) = C.stack ∧ Satisfies (pathEquations tm v.ops) x := by
  rw [← variants_exact]
  simp only [Variant.Holds,pathEquations_exact]

/-- The actual one-step relation of a verifier tests a finite control label
and one of its fixed systems, even when evaluated on unreachable registers. -/
theorem regStep_affine_iff (tm : FinTM2) (A C : Registers tm) :
    regStep tm A = some C ↔ ∃ l, A.label = some l ∧
      ∃ v ∈ variants tm (tm.m l) A.state, v.label = C.label ∧ v.state = C.state ∧
        ∃ x : Fin (cellCount tm v.ops.length) → ℕ, x ∘ rowCell tm 0 = A.stack ∧
          x ∘ rowCell tm (Fin.last v.ops.length) = C.stack ∧ Satisfies (pathEquations tm v.ops) x := by
  obtain ⟨ol,s,R⟩ := A
  cases ol <;> simp [regStep,macro_affine_iff]

end DiophantineNP.Classes.Jones.Machine
