import DiophantineNP.MachineStackBlocks
import Mathlib.Tactic.FinCases

/-! # Word-register programs, scratch registers, and register embeddings -/
namespace DiophantineNP.Classes.StackModel

abbrev WordBlock (I : Type) := Block (fun _ : I => Bool)
abbrev WordStore (I : Type) := I → List Bool

structure Workspace (I : Type) where
  slot : Fin 8 ↪ I

def Workspace.Out {I : Type} (W : Workspace I) (i : I) : Prop := ∀ j, W.slot j ≠ i

def HasWordGate {I : Type} [DecidableEq I] (W : Workspace I) (dst : I)
    (f : WordStore I → List Bool) : Prop :=
  ∃ p : WordBlock I, ∃ time : Polynomial ℕ, ∀ B s, (∀ i, (s i).length ≤ B) →
    (∀ j, s (W.slot j) = []) → s dst = [] →
      ∃ n, n ≤ time.eval B ∧ p.Runs s (Function.update s dst (f s)) n

section
variable {I J : Type}

/-- Overwrite the selected registers from a local store, keeping all other registers. -/
noncomputable def overlay {α : Type} (e : I ↪ J) (base : J → α) (w : I → α) (j : J) : α :=
  open Classical in if h : ∃ i, e i = j then w h.choose else base j

@[simp] theorem overlay_hit {α : Type} (e : I ↪ J) (base : J → α) (w : I → α) (i : I) :
    overlay e base w (e i) = w i := by
  classical
  unfold overlay
  split
  next h => rw [e.injective h.choose_spec]
  next h => exact False.elim (h ⟨_,rfl⟩)

theorem overlay_miss {α : Type} (e : I ↪ J) (base : J → α) (w : I → α) (j : J)
    (h : ∀ i, e i ≠ j) : overlay e base w j = base j := by
  classical
  simp [overlay,not_exists.mpr h]

@[simp] theorem overlay_restrict {α : Type} (e : I ↪ J) (base : J → α) :
    overlay e base (fun i => base (e i)) = base := by
  classical
  funext j
  by_cases h : ∃ i, e i = j
  · obtain ⟨i,rfl⟩ := h; simp
  · exact overlay_miss _ _ _ _ (not_exists.mp h)

noncomputable def embed (e : I ↪ J) (p : WordBlock I) : WordBlock J where
  Label := p.Label
  entry := p.entry
  code l h := let act := p.code l (fun i => h (e i))
              ⟨act.next,overlay e (fun _ => idle) act.edit⟩

private theorem head_overlay (e : I ↪ J) (b : WordStore J) (s : WordStore I) :
    (fun i => heads (overlay e b s) (e i)) = heads s := by funext i; simp [heads]

private theorem edits_overlay (e : I ↪ J) (b : WordStore J) (s : WordStore I) (ed : I → Move Bool) :
    applyEdits (overlay e (fun _ => idle) ed) (overlay e b s) = overlay e b (applyEdits ed s) := by
  classical
  funext j
  by_cases h : ∃ i, e i = j
  · obtain ⟨i,rfl⟩ := h; simp [applyEdits]
  · simp [applyEdits,overlay_miss _ _ _ _ (not_exists.mp h)]

theorem Path.embedWord (e : I ↪ J) (p : WordBlock I) {l s m t n}
    (a : Path p.code l s m t n) (base : WordStore J) :
    Path (embed e p).code l (overlay e base s) m (overlay e base t) n := by
  induction a with
  | refl => exact .refl _ _
  | cons h ih =>
    apply Path.cons
    simp only [embed,head_overlay,edits_overlay]
    exact ih

theorem run_embed (e : I ↪ J) (p : WordBlock I) {s : WordStore J} {t n}
    (h : p.Runs (fun i => s (e i)) t n) :
    (embed e p).Runs s (overlay e s t) n := by
  simpa using h.embedWord e p s

end
end DiophantineNP.Classes.StackModel
