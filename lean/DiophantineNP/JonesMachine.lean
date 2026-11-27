import DiophantineNP.EncodingFacts

/-! # Register coding for the finite TM2 machines in the verifier definition

The machine interface constrains the input alphabet, control, labels and stack
indices to be finite. Work-stack alphabets can have arbitrary ambient type.
The fixed lists of pushes identify a finite set containing every reachable
symbol, from which one can construct a radix independent of the input.
-/
namespace DiophantineNP.Classes.Jones.Machine
open Turing
open scoped Classical
attribute [local instance] FinTM2.σFin FinTM2.ΛFin FinTM2.Γk₀Fin FinTM2.kFin

abbrev Symbol (tm : FinTM2) := (k : tm.K) × tm.Γ k

/-- Symbols that the finite instruction can push, across every control state. -/
noncomputable def pushed (tm : FinTM2) : tm.Stmt → Finset (Symbol tm)
  | .push k f q => Finset.univ.image (fun s => ⟨k,f s⟩) ∪ pushed tm q
  | .peek _ _ q | .pop _ _ q | .load _ q => pushed tm q
  | .branch _ q₁ q₂ => pushed tm q₁ ∪ pushed tm q₂
  | .goto _ | .halt => ∅

/-- A fixed alphabet supporting every stack during every run of this machine. -/
noncomputable def alphabet (tm : FinTM2) : Finset (Symbol tm) :=
  Finset.univ.image (fun a : tm.Γ tm.k₀ => (⟨tm.k₀,a⟩ : Symbol tm)) ∪
    Finset.univ.biUnion (fun l : tm.Λ => pushed tm (tm.m l))

theorem pushed_sub (tm : FinTM2) (l : tm.Λ) : pushed tm (tm.m l) ⊆ alphabet tm := by
  classical
  intro a ha
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,ha⟩)

abbrev Stacks (tm : FinTM2) := (k : tm.K) → List (tm.Γ k)

def Supported (tm : FinTM2) (S : Stacks tm) : Prop :=
  ∀ k a, a ∈ S k → (⟨k,a⟩ : Symbol tm) ∈ alphabet tm

theorem support_update (tm : FinTM2) {S : Stacks tm} (h : Supported tm S)
    (k : tm.K) (s : List (tm.Γ k)) (hs : ∀ a ∈ s, (⟨k,a⟩ : Symbol tm) ∈ alphabet tm) :
    Supported tm (Function.update S k s) := by
  intro j a ha
  by_cases eq : j = k
  · subst j; exact hs a (by simpa using ha)
  · exact h j a (by simpa only [Function.update_of_ne eq] using ha)

theorem support_push (tm : FinTM2) {q : tm.Stmt} {k : tm.K} {f : tm.σ → tm.Γ k}
    (hs : pushed tm (.push k f q) ⊆ alphabet tm) (s : tm.σ) :
    (⟨k,f s⟩ : Symbol tm) ∈ alphabet tm :=
  hs (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩))

private theorem stepAux_support (tm : FinTM2) (q : tm.Stmt) (hh : pushed tm q ⊆ alphabet tm)
    (s : tm.σ) (S : Stacks tm) (h : Supported tm S) :
    Supported tm (TM2.stepAux q s S).stk := by
  induction q generalizing s S with
  | push k f q ih =>
    apply ih (Finset.Subset.trans Finset.subset_union_right hh)
    apply support_update tm h
    intro a ha; rcases List.mem_cons.mp ha with rfl | h'
    · exact support_push tm hh s
    · exact h k _ h'
  | peek k f q ih => exact ih hh _ _ h
  | pop k f q ih =>
    exact ih hh _ _ (support_update tm h k _ (fun a ha => h k a (List.mem_of_mem_tail ha)))
  | load f q ih => exact ih hh _ _ h
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases e : f s
    · simp only [TM2.stepAux, e, cond_false]
      exact ih₂ (Finset.Subset.trans Finset.subset_union_right hh) _ _ h
    · simp only [TM2.stepAux, e, cond_true]
      exact ih₁ (Finset.Subset.trans Finset.subset_union_left hh) _ _ h
  | goto f => exact h
  | halt => exact h

theorem init_support (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : Supported tm (initList tm s).stk := by
  intro k a ha
  by_cases eq : k = tm.k₀
  · subst k
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  · simp [initList,eq] at ha

/-- Maximum number of pushes along a single path through an instruction. -/
def pushes (tm : FinTM2) : tm.Stmt → ℕ
  | .push _ _ q => pushes tm q + 1
  | .peek _ _ q | .pop _ _ q | .load _ q => pushes tm q
  | .branch _ q₁ q₂ => max (pushes tm q₁) (pushes tm q₂)
  | .goto _ | .halt => 0

noncomputable def perStep (tm : FinTM2) := Finset.univ.sup (fun l : tm.Λ => pushes tm (tm.m l))

private theorem stepAux_length (tm : FinTM2) (q : tm.Stmt) (s : tm.σ) (S : Stacks tm)
    (N : ℕ) (h : ∀ i, (S i).length ≤ N) (j : tm.K) :
    ((TM2.stepAux q s S).stk j).length ≤ N + pushes tm q := by
  induction q generalizing s S N with
  | push k f q ih =>
    have h' (i) : ((Function.update S k (f s :: S k)) i).length ≤ N+1 := by
      by_cases e : i=k
      · subst i; simpa using Nat.succ_le_succ (h k)
      · simpa only [Function.update_of_ne e] using (h i).trans (Nat.le_succ _)
    exact (ih s _ (N+1) h').trans (by dsimp [pushes]; omega)
  | peek k f q ih => exact ih _ _ _ h
  | pop k f q ih =>
    apply ih
    intro i; by_cases e : i=k
    · subst i; simpa using (show (S k).tail.length ≤ N by simp; have := h k; omega)
    · simpa only [Function.update_of_ne e] using h i
  | load f q ih => exact ih _ _ _ h
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases e : f s
    · simp only [TM2.stepAux,e,cond_false,pushes]
      exact (ih₂ s S N h).trans (Nat.add_le_add_left (le_max_right ..) _)
    · simp only [TM2.stepAux,e,cond_true,pushes]
      exact (ih₁ s S N h).trans (Nat.add_le_add_left (le_max_left ..) _)
  | goto f => simpa [pushes] using h j
  | halt => simpa [pushes] using h j

/-- After exactly n TM2 macrosteps, all stacks are supported and have at most
inputLength + n·perStep symbols. A halted run has no subsequent configuration. -/
theorem reachable_stacks (tm : FinTM2) (s : List (tm.Γ tm.k₀)) (n : ℕ) (c : tm.Cfg)
    (hr : (fun v : Option tm.Cfg => v.bind tm.step)^[n] (some (initList tm s)) = some c) :
    Supported tm c.stk ∧ ∀ j, (c.stk j).length ≤ s.length+n*perStep tm := by
  induction n generalizing c with
  | zero =>
    have he : initList tm s = c := Option.some.inj hr
    subst c
    refine ⟨init_support tm s,fun j => ?_⟩
    by_cases e : j=tm.k₀
    · subst j; simp [initList]
    · simp [initList,e]
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hr
    change ((fun v : Option tm.Cfg => v.bind tm.step)^[n] (some (initList tm s))).bind tm.step = some c at hr
    cases hprev : (fun v : Option tm.Cfg => v.bind tm.step)^[n] (some (initList tm s)) with
    | none => rw [hprev] at hr; cases hr
    | some prev =>
      rw [hprev] at hr
      change tm.step prev = some c at hr
      obtain ⟨hs,hlen⟩ := ih prev hprev
      obtain ⟨l,v,S⟩ := prev
      cases l with
      | none => cases hr
      | some l =>
        have he : TM2.stepAux (tm.m l) v S = c := Option.some.inj hr
        subst c
        refine ⟨stepAux_support tm _ (pushed_sub tm l) _ _ hs,fun j => ?_⟩
        have h := stepAux_length tm (tm.m l) v S _ hlen j
        have hp : pushes tm (tm.m l) ≤ perStep tm := Finset.le_sup (f := fun a => pushes tm (tm.m a)) (Finset.mem_univ l)
        rw [Nat.succ_mul]
        omega

end DiophantineNP.Classes.Jones.Machine
