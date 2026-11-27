import DiophantineNP.JonesAffinePaths

/-! # Size bounds for the cells of a fixed register branch -/
namespace DiophantineNP.Classes.Jones.Machine
open Turing

noncomputable def Op.factor (tm : FinTM2) : Op tm → ℕ
  | .push _ d => radix tm + d + 1
  | .read _ _ _ => 1

noncomputable def pathFactor (tm : FinTM2) (ops : List (Op tm)) := (ops.map (Op.factor tm)).prod

private theorem factor_pos (tm : FinTM2) (a : Op tm) : 0 < a.factor tm := by cases a <;> simp [Op.factor]

private theorem pathFactor_pos (tm : FinTM2) (ops : List (Op tm)) : 0 < pathFactor tm ops := by
  induction ops with
  | nil => simp [pathFactor]
  | cons a ops ih => exact Nat.mul_pos (factor_pos tm a) ih

private theorem boundedOp (tm : FinTM2) (a : Op tm) (R T : File tm) {M : ℕ} (hm : 0 < M)
    (hr : ∀ k, R k ≤ M) (h : a.Holds tm R T) :
    ∃ q ≤ M, a.HoldsWith tm R T q ∧ ∀ k, T k ≤ M*a.factor tm := by
  cases a with
  | push k d =>
    change T = _ at h
    refine ⟨0,Nat.zero_le _,h,fun j => ?_⟩
    rw [h]
    by_cases hj : j=k
    · subst j; rw [Function.update_self]
      have hd : d ≤ M*d := Nat.le_mul_of_pos_left d hm
      have hr' := Nat.mul_le_mul_left (radix tm) (hr k)
      simp only [Op.factor,Nat.mul_add,Nat.mul_one]
      rw [Nat.mul_comm M (radix tm)]; omega
    · rw [Function.update_of_ne hj]
      exact (hr j).trans (Nat.le_mul_of_pos_right _ (factor_pos tm (.push k d)))
  | read k d drop =>
    obtain ⟨q,hq,hT⟩ := h
    have hB : 0 < radix tm := by unfold radix; positivity
    have hqm : q ≤ M := ((Nat.le_mul_of_pos_left q hB).trans (by omega : radix tm*q ≤ R k)).trans (hr k)
    refine ⟨q,hqm,⟨hq,hT⟩,fun j => ?_⟩
    rw [hT]; simp only [Op.factor,Nat.mul_one]
    cases drop <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact hr j
    · by_cases hj : j=k
      · subst j; simpa using hqm
      · simpa [Function.update_of_ne hj] using hr j

private theorem boundedRows (tm : FinTM2) (ops : List (Op tm)) (R T : File tm) {M : ℕ}
    (hm : 0 < M) (hr : ∀ k, R k ≤ M) (h : Chain tm ops R T) :
    ∃ (rows : Fin (ops.length+1) → File tm) (quot : Fin ops.length → ℕ),
      rows 0 = R ∧ rows (Fin.last ops.length) = T ∧
      (∀ i : Fin ops.length, (ops.get i).HoldsWith tm (rows i.castSucc) (rows i.succ) (quot i)) ∧
      (∀ i k, rows i k ≤ M*pathFactor tm ops) ∧ ∀ i, quot i ≤ M*pathFactor tm ops := by
  induction ops generalizing R M with
  | nil =>
    refine ⟨fun _ => R,Fin.elim0,rfl,h,fun i => Fin.elim0 i,fun _ k => ?_,fun i => Fin.elim0 i⟩
    simpa [pathFactor] using hr k
  | cons a ops ih =>
    obtain ⟨R',ha,ht⟩ := h
    obtain ⟨u,hu,hA,hB⟩ := boundedOp tm a R R' hm hr ha
    obtain ⟨rs,qs,h₀,h₁,hL,hR,hQ⟩ := ih R' (Nat.mul_pos hm (factor_pos tm a)) hB ht
    have he : M*pathFactor tm (a::ops) = (M*a.factor tm)*pathFactor tm ops := (Nat.mul_assoc ..).symm
    have hM : M ≤ M*pathFactor tm (a::ops) := Nat.le_mul_of_pos_right _ (pathFactor_pos tm _)
    simp only [List.length_cons] at *
    refine ⟨Fin.cons R rs,Fin.cons u qs,Fin.cons_zero ..,?_,?_,?_,?_⟩
    · change (Fin.cons (α := fun _ => File tm) R rs) (Fin.last ops.length).succ = T
      simp only [Fin.cons_succ]; exact h₁
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · simpa [h₀] using hA
      · simpa [Fin.castSucc_succ] using hL j
    · intro i; refine Fin.cases (fun k => ?_) (fun j k => ?_) i
      · exact (hr k).trans hM
      · rw [he]; exact hR j k
    · intro i; refine Fin.cases (hu.trans hM) (fun j => ?_) i
      rw [he]; exact hQ j

/-- All local scratch values of an honest operation chain are bounded by the
initial register bound times a constant determined by this fixed branch. -/
theorem boundedPathAssignment (tm : FinTM2) (ops : List (Op tm)) (R T : File tm) {M : ℕ}
    (hm : 0 < M) (hr : ∀ k, R k ≤ M) (h : Chain tm ops R T) :
    ∃ x : Fin (cellCount tm ops.length) → ℕ, x ∘ rowCell tm 0 = R ∧
      x ∘ rowCell tm (Fin.last ops.length) = T ∧ Satisfies (pathEquations tm ops) x ∧
      ∀ j, x j ≤ M*pathFactor tm ops := by
  obtain ⟨rows,quot,h₀,h₁,h,hR,hQ⟩ := boundedRows tm ops R T hm hr h
  let f : Cells tm ops.length → ℕ := Sum.elim (fun t => rows t.1 t.2) quot
  let x := f ∘ (cellIndex tm ops.length).symm
  have hh (i : Fin (ops.length+1)) : x ∘ rowCell tm i = rows i := by funext j; simp [x,f,rowCell]
  have hq (i : Fin ops.length) : x (quotCell tm i) = quot i := by simp [x,f,quotCell]
  refine ⟨x,(hh 0).trans h₀,(hh _).trans h₁,?_,fun j => ?_⟩
  · intro p hp
    obtain ⟨i,_,hp⟩ := List.mem_flatMap.mp hp
    apply (opEquations_exact ..).mpr _ p hp
    simpa only [hh,hq] using h i
  · change f ((cellIndex tm ops.length).symm j) ≤ _
    cases (cellIndex tm ops.length).symm j with
    | inl a => exact hR a.1 a.2
    | inr i => exact hQ i

end DiophantineNP.Classes.Jones.Machine
