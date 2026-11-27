import DiophantineNP.MachineStackTransfer
import Mathlib.Tactic.DeriveFintype

/-! # Embedding a two-input arithmetic gate into the circuit's register file -/
namespace DiophantineNP.Classes.StackModel

inductive Port
  | x | y | dst | tmp (i : Fin 8)
  deriving DecidableEq, Fintype

def portStore (xs ys result : List Bool) (work : Fin 8 → List Bool) : WordStore Port
  | .x => xs
  | .y => ys
  | .dst => result
  | .tmp i => work i

private def portMap {I : Type} (W : Workspace I) (x y dst : I) : Port → I
  | .x => x
  | .y => y
  | .dst => dst
  | .tmp i => W.slot i

private def portEmbed {I : Type} (W : Workspace I) (x y dst : I) (hx : W.Out x) (hy : W.Out y)
    (hd : W.Out dst) (hxy : x≠y) (hxd : x≠dst) (hyd : y≠dst) : Port ↪ I where
  toFun := portMap W x y dst
  inj' := by
    intro i j h
    cases i <;> cases j <;> simp_all [portMap,Workspace.Out, W.slot.injective.eq_iff, eq_comm]

theorem gate_of_port_program {I : Type} [DecidableEq I] (p : WordBlock Port)
    (f : List Bool → List Bool → List Bool) (time : Polynomial ℕ)
    (h : ∀ (B : ℕ) (xs ys : List Bool), xs.length ≤ B → ys.length ≤ B →
        ∃ n, n ≤ time.eval B ∧ p.Runs (portStore xs ys [] (fun _ => []))
          (portStore xs ys (f xs ys) (fun _ => [])) n)
    (W : Workspace I) (x y dst : I) (hx : W.Out x) (hy : W.Out y) (hd : W.Out dst)
    (hxy : x≠y) (hxd : x≠dst) (hyd : y≠dst) : HasWordGate W dst (fun s => f (s x) (s y)) := by
  let e := portEmbed W x y dst hx hy hd hxy hxd hyd
  refine ⟨embed e p,time,?_⟩
  intro B s hsize hwork hout
  obtain ⟨n,hn,hr⟩ := h B (s x) (s y) (hsize x) (hsize y)
  have hi : (fun i => s (e i)) = portStore (s x) (s y) [] (fun _ => []) := by
    funext i; cases i <;> simp [e,portEmbed,portMap,portStore,hwork,hout]
  have he : overlay e s (portStore (s x) (s y) (f (s x) (s y)) (fun _ => [])) =
      Function.update s dst (f (s x) (s y)) := by
    classical
    funext j
    by_cases hhit : ∃ i, e i = j
    · obtain ⟨i,rfl⟩ := hhit
      rw [overlay_hit]
      cases i <;> simp [e,portEmbed,portMap,portStore,hxd,hyd]
      next i => rw [Function.update_of_ne (hd i),hwork]
    · have hne : j ≠ dst := fun hj => hhit ⟨Port.dst,by simpa [e,portEmbed,portMap] using hj.symm⟩
      rw [overlay_miss _ _ _ _ (not_exists.mp hhit), Function.update_of_ne hne]
  exact ⟨n,hn,he ▸ run_embed e p (hi.symm ▸ hr)⟩

end DiophantineNP.Classes.StackModel
