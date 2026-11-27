import DiophantineNP.MachineStackWords

/-! # Allocation and polynomial running time for arbitrary fixed word circuits -/
namespace DiophantineNP.Classes.StackModel
open MachinePolynomial
open Computability

/-- Each gate writes a fresh result, preserves its operands, and returns the common scratch
registers empty. Each use carries an actual finite program and a polynomial runtime. -/
structure WordGates {I : Type} [DecidableEq I] (W : Workspace I) : Prop where
  literal : ∀ d, W.Out d → ∀ w : List Bool, HasWordGate W d (fun _ => w)
  copy : ∀ i d, W.Out i → W.Out d → i ≠ d → HasWordGate W d (fun s => s i)
  add : ∀ i j d, W.Out i → W.Out j → W.Out d → i ≠ j → i ≠ d → j ≠ d →
    HasWordGate W d (fun s => MachineAddition.addWords (s i) (s j) false)
  mul : ∀ i j d, W.Out i → W.Out j → W.Out d → i ≠ j → i ≠ d → j ≠ d →
    HasWordGate W d (fun s => multiply (s i) (s j))

namespace Allocation
variable {A I : Type}

/-- There is one fresh word register for each syntax-tree occurrence. -/
def Nodes (a : Circuit A) : Type :=
  match a with
  | .literal _ | .input _ => Unit
  | .add x y | .mul x y => Option (Nodes x ⊕ Nodes y)

noncomputable instance nodeFin (a : Circuit A) : Fintype (Nodes a) := by
  induction a with
  | literal | input => exact inferInstanceAs (Fintype Unit)
  | add x y ih jh | mul x y ih jh => exact inferInstanceAs (Fintype (Option (Nodes x ⊕ Nodes y)))

def root (a : Circuit A) : Nodes a := by
  cases a with
  | literal | input => exact ()
  | add | mul => exact none

def leftSlot {X Y : Type} : X ↪ Option (X ⊕ Y) :=
  ⟨some ∘ Sum.inl, fun _ _ h => Sum.inl.inj (Option.some.inj h)⟩

def rightSlot {X Y : Type} : Y ↪ Option (X ⊕ Y) :=
  ⟨some ∘ Sum.inr, fun _ _ h => Sum.inr.inj (Option.some.inj h)⟩

abbrev StoreFits (b : ℕ) (s : WordStore I) := ∀ i, (s i).length ≤ b
abbrev DisjointSlots {X Y : Type} (f : X → I) (g : Y → I) := ∀ i j, f i ≠ g j

/-- The output store may retain subexpression values only in its designated registers. -/
def Executes [DecidableEq I] (W : Workspace I) (read : A → I) (a : Circuit A)
    (slot : Nodes a ↪ I) : Prop :=
  ∃ p : WordBlock I, ∃ time space : Polynomial ℕ, ∀ B s, StoreFits B s →
    (∀ j, s (W.slot j) = []) → (∀ j, s (slot j) = []) →
    ∃ t n, p.Runs s t n ∧ n ≤ time.eval B ∧ StoreFits (space.eval B) t ∧
      t (slot (root a)) = a.word (s ∘ read) ∧ ∀ i, (∀ j, slot j ≠ i) → t i = s i

private theorem updated [DecidableEq I] (s : WordStore I) {d : I} {B K : ℕ}
    (h : StoreFits B s) (v : List Bool) (hv : v.length ≤ K) :
    StoreFits (B+K) (Function.update s d v) := by
  intro i
  by_cases e : i=d
  · subst i; simp only [Function.update_self]; omega
  · rw [Function.update_of_ne e]; exact (h i).trans (by omega)

private theorem leaf [DecidableEq I] (W : Workspace I) (read : A → I) (a : Circuit A)
    (slot : Nodes a ↪ I) (g : HasWordGate W (slot (root a)) (fun s => a.word (s ∘ read))) :
    Executes W read a slot := by
  obtain ⟨p,time,run⟩ := g
  obtain ⟨q,hq⟩ := a.polynomialBound
  refine ⟨p,time,Polynomial.X+q,fun B s hs hw he => ?_⟩
  obtain ⟨n,ht,hr⟩ := run B s hs hw (he (root a))
  refine ⟨_,n,hr,ht,?_,Function.update_self ..,?_⟩
  · simp only [Polynomial.eval_add,Polynomial.eval_X]
    exact updated s hs _ ((Nat.le_add_right ..).trans (hq B _ (fun i => hs (read i))))
  · intro i h
    exact Function.update_of_ne (Ne.symm (h _)) ..

private theorem binary [DecidableEq I] (W : Workspace I) (read : A → I)
    (x y : Circuit A) (f : List Bool → List Bool → List Bool) (a : Circuit A)
    (hword : ∀ w, a.word w = f (x.word w) (y.word w))
    (slot : Nodes a ↪ I) (lx : Nodes x ↪ I) (ry : Nodes y ↪ I)
    (incL : ∀ j, ∃ k, slot k = lx j) (incR : ∀ j, ∃ k, slot k = ry j)
    (dis : DisjointSlots lx ry) (dl : ∀ j, lx j ≠ slot (root a)) (dr : ∀ j, ry j ≠ slot (root a))
    (rd : DisjointSlots slot read) (wk : ∀ i, W.Out (slot i))
    (ex : Executes W read x lx) (ey : Executes W read y ry)
    (gate : HasWordGate W (slot (root a)) (fun s => f (s (lx (root x))) (s (ry (root y))))) :
    Executes W read a slot := by
  obtain ⟨px,tx,sx,hx⟩ := ex
  obtain ⟨py,ty,sy,hy⟩ := ey
  obtain ⟨pg,tg,hg⟩ := gate
  obtain ⟨qa,hq⟩ := a.polynomialBound
  let cap := sy.comp sx
  refine ⟨(px.seq py).seq pg,tx + ty.comp sx + tg.comp cap, cap+qa,fun B s hs hw he => ?_⟩
  have noReadL j i : lx j ≠ read i := by obtain ⟨k,h⟩ := incL j; exact h ▸ rd k i
  have noWorkL j i : lx j ≠ W.slot i := by obtain ⟨k,h⟩ := incL j; exact h ▸ (wk k i).symm
  have noWorkR j i : ry j ≠ W.slot i := by obtain ⟨k,h⟩ := incR j; exact h ▸ (wk k i).symm
  obtain ⟨u,m,rx,hm,bu,vx,fx⟩ := hx B s hs hw (fun j => by obtain ⟨k,h⟩ := incL j; rw [←h]; exact he k)
  have inputs : u ∘ read = s ∘ read := funext (fun i => fx _ (fun j => noReadL j i))
  obtain ⟨v,n,ryun,hn,bv,vy,fy⟩ := hy _ u bu (fun i => (fx _ (fun j => noWorkL j i)).trans (hw i)) (fun j => by
    obtain ⟨k,h⟩ := incR j
    exact (fx _ (fun i => dis i j)).trans (h ▸ he k))
  obtain ⟨k,hk,rg⟩ := hg _ v bv
    (fun i => (fy _ (fun j => noWorkR j i)).trans ((fx _ (fun j => noWorkL j i)).trans (hw i)))
    ((fy _ dr).trans ((fx _ dl).trans (he _)))
  have result : f (v (lx (root x))) (v (ry (root y))) = a.word (s ∘ read) := by
    rw [fy _ (fun j => (dis _ j).symm),vx,vy,inputs,hword]
  refine ⟨_,_,run_seq (run_seq rx ryun) rg,?_,?_,(Function.update_self ..).trans result,?_⟩
  · simp only [Polynomial.eval_add,Polynomial.eval_comp,cap]
    omega
  · simp only [Polynomial.eval_add,Polynomial.eval_comp,cap]
    apply updated _ bv
    rw [result]
    exact (Nat.le_add_right ..).trans (hq B _ (fun i => hs (read i)))
  · intro i hi
    rw [Function.update_of_ne (Ne.symm (hi _)),fy,fx]
    · intro j; obtain ⟨k,e⟩ := incL j; exact e ▸ hi k
    · intro j; obtain ⟨k,e⟩ := incR j; exact e ▸ hi k

/-- Allocate the expression tree in any disjoint bank. Repeated occurrences of an input
or a subexpression can be evaluated independently even for the gate x * x. -/
theorem compile [DecidableEq I] (W : Workspace I) (G : WordGates W) (read : A → I)
    (hr : ∀ i, W.Out (read i)) (a : Circuit A) (slot : Nodes a ↪ I)
    (rd : DisjointSlots slot read) (wk : ∀ i, W.Out (slot i)) : Executes W read a slot := by
  induction a with
  | literal n => exact leaf W read _ slot (G.literal _ (wk _) _)
  | input i => exact leaf W read _ slot (G.copy _ _ (hr i) (wk _) (rd _ i).symm)
  | add x y hx hy | mul x y hx hy =>
    let lx := (leftSlot (X := Nodes x) (Y := Nodes y)).trans slot
    let ry := (rightSlot (X := Nodes x) (Y := Nodes y)).trans slot
    have il j : ∃ k, slot k = lx j := ⟨_,rfl⟩
    have ir j : ∃ k, slot k = ry j := ⟨_,rfl⟩
    have dis : DisjointSlots lx ry := fun i j h => by cases Option.some.inj (slot.injective h)
    have dl j : lx j ≠ slot none := fun h => by simpa [lx,leftSlot] using slot.injective h
    have dr j : ry j ≠ slot none := fun h => by simpa [ry,rightSlot] using slot.injective h
    have ex := hx lx (fun i j => rd _ j) (fun i => wk _)
    have ey := hy ry (fun i j => rd _ j) (fun i => wk _)
    first
    | exact binary W read x y (fun a b => MachineAddition.addWords a b false) (.add x y)
        (fun _ => rfl) slot lx ry il ir dis dl dr rd wk ex ey
        (G.add _ _ _ (wk _) (wk _) (wk _) (dis _ _) (dl _) (dr _))
    | exact binary W read x y multiply (.mul x y)
        (fun _ => rfl) slot lx ry il ir dis dl dr rd wk ex ey
        (G.mul _ _ _ (wk _) (wk _) (wk _) (dis _ _) (dl _) (dr _))

end Allocation
end DiophantineNP.Classes.StackModel
