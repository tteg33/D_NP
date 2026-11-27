import DiophantineNP.MachineCircuitAllocation

/-! # Running two circuits from one framed input -/
namespace DiophantineNP.Classes.StackModel.Allocation
open MachinePolynomial

abbrev Bank {A : Type} (a b : Circuit A) := Fin 8 ⊕ (A ⊕ (Nodes a ⊕ Nodes b))

def scratch {A : Type} (a b : Circuit A) : Workspace (Bank a b) := ⟨Function.Embedding.inl⟩
def reads {A : Type} (a b : Circuit A) : A ↪ Bank a b :=
  Function.Embedding.inl.trans Function.Embedding.inr
def leftBank {A : Type} (a b : Circuit A) : Nodes a ↪ Bank a b :=
  (Function.Embedding.inl.trans Function.Embedding.inr).trans Function.Embedding.inr
def rightBank {A : Type} (a b : Circuit A) : Nodes b ↪ Bank a b :=
  (Function.Embedding.inr.trans Function.Embedding.inr).trans Function.Embedding.inr

/-- The two fixed word programs share their input and scratch bank and preserve the first
result while computing the second. The runtime and final store bounds hold on every tape. -/
theorem pairProgram {r : ℕ} (a b : Circuit (Option (Fin r)))
    [DecidableEq (Bank a b)] (G : WordGates (scratch a b)) :
    ∃ p : WordBlock (Bank a b), ∃ time space : Polynomial ℕ, ∀ s : List (Option Bool),
      ∃ t n, p.Runs (overlay (reads a b) (fun _ => []) (fieldAt s)) t n ∧
        n ≤ time.eval s.length ∧ (∀ i, (t i).length ≤ space.eval s.length) ∧
        t (leftBank a b (root a)) = a.word (fieldAt s) ∧
        t (rightBank a b (root b)) = b.word (fieldAt s) := by
  let W := scratch a b
  let e := reads a b
  let l := leftBank a b
  let v := rightBank a b
  have ew i : W.Out (e i) := fun _ h => nomatch h
  have lw i : W.Out (l i) := fun _ h => nomatch h
  have vw i : W.Out (v i) := fun _ h => nomatch h
  have le' : DisjointSlots l e := fun _ _ h => nomatch h
  have ve' : DisjointSlots v e := fun _ _ h => nomatch h
  have lv : DisjointSlots l v := fun _ _ h => nomatch h
  obtain ⟨pa,ta,sa,ha⟩ := compile W G e ew a l le' lw
  obtain ⟨pb,tb,sb,hb⟩ := compile W G e ew b v ve' vw
  refine ⟨pa.seq pb,ta+tb.comp sa,sb.comp sa,fun s => ?_⟩
  let base : WordStore (Bank a b) := overlay e (fun _ => []) (fieldAt s)
  have be (i) : base (e i) = fieldAt s i := overlay_hit .. 
  have empty (i) (hi : ∀ j, e j ≠ i) : base i = [] := overlay_miss _ _ _ _ hi
  have fit : StoreFits s.length base := by
    intro i
    by_cases h : ∃ j, e j = i
    · obtain ⟨j,rfl⟩ := h
      rw [be]; exact length_fieldAt s j
    · rw [empty _ (not_exists.mp h)]; exact Nat.zero_le _
  have emptyW j : base (W.slot j) = [] := empty _ (fun i => (ew i j).symm)
  have readBase : base ∘ e = fieldAt s := funext be
  obtain ⟨u,n,ru,nt,us,ua,uf⟩ := ha s.length base fit emptyW
    (fun i => empty _ (fun j => (le' i j).symm))
  obtain ⟨t,m,rt,mt,ts,tb',tf⟩ := hb _ u us
    (fun j => (uf _ (fun i => (lw i j).symm)).trans (emptyW _))
    (fun i => (uf _ (fun j => lv j i)).trans (empty _ (fun j => (ve' i j).symm)))
  have readU : u ∘ e = base ∘ e := funext (fun i => uf _ (fun j => le' j i))
  refine ⟨t,_,run_seq ru rt,by simpa using Nat.add_le_add nt mt,by simpa using ts,?_,?_⟩
  · rw [tf _ (fun j => (lv _ j).symm),ua,readBase]
  · rw [tb',readU,readBase]

end DiophantineNP.Classes.StackModel.Allocation
