import DiophantineNP.MachineStackPorts
import DiophantineNP.MachineStackAdder

/-! # The input-preserving binary addition gate -/
namespace DiophantineNP.Classes.StackModel
open MachineAddition

private def addPortProgram : WordBlock Port :=
  (copyWord .x (.tmp 0) (.tmp 2)).seq <|
  (copyWord .y (.tmp 1) (.tmp 2)).seq <|
  (addReverse (.tmp 0) (.tmp 1) (.tmp 3)).seq
    (scatter (.tmp 3) (fun i => decide (i=.dst)))

theorem gateAdd {I : Type} [DecidableEq I] (W : Workspace I) (x y dst : I)
    (hx : W.Out x) (hy : W.Out y) (hd : W.Out dst) (hxy : x≠y) (hxd : x≠dst) (hyd : y≠dst) :
    HasWordGate W dst (fun s => addWords (s x) (s y) false) := by
  apply gate_of_port_program addPortProgram (fun a b => addWords a b false) (7*(Polynomial.X+1))
    _ W x y dst hx hy hd hxy hxd hyd
  intro B xs ys hxs hys
  let sum := addWords xs ys false
  let initial := portStore xs ys [] (fun _ => [])
  let s₁ := Function.update initial (.tmp 0) xs
  let s₂ := Function.update s₁ (.tmp 1) ys
  let s₃ := addState s₂ (.tmp 0) (.tmp 1) (.tmp 3) [] [] sum.reverse
  have h₁ : (copyWord .x (.tmp 0) (.tmp 2)).Runs initial s₁ (2*(xs.length+1)) :=
    run_copyWord _ _ _ initial (by decide) (by decide) (by decide) rfl rfl
  have h₂ : (copyWord .y (.tmp 1) (.tmp 2)).Runs s₁ s₂ (2*(ys.length+1)) :=
    run_copyWord _ _ _ s₁ (by decide) (by decide) (by decide) rfl rfl
  have h₃ : (addReverse (.tmp 0) (.tmp 1) (.tmp 3)).Runs s₂ s₃ (max xs.length ys.length+1) := by
    simpa [s₁,s₂,s₃,initial,sum,portStore,Function.update] using
      run_addReverse (.tmp 0) (.tmp 1) (.tmp 3) (by decide) (by decide) (by decide) s₂
  have h₄ := run_scatter s₃ (.tmp 3) (fun i => decide (i=.dst))
  have ho : scatterState s₃ (.tmp 3) (fun i => decide (i=.dst)) [] (s₃ (.tmp 3)).reverse =
      portStore xs ys sum (fun _ => []) := by
    funext i
    cases i with
    | x | y | dst => simp [s₁,s₂,s₃,initial,sum,portStore,Function.update,scatterState,addState]
    | tmp j => fin_cases j <;> simp [s₁,s₂,s₃,initial,sum,portStore,Function.update,scatterState,addState]
  rw [ho] at h₄
  have hz : s₃ (.tmp 3) = sum.reverse := by rfl
  rw [hz,List.length_reverse] at h₄
  refine ⟨_, ?_, run_seq h₁ (run_seq h₂ (run_seq h₃ h₄))⟩
  have hs := length_addWords xs ys false
  dsimp [sum]
  simp
  omega

end DiophantineNP.Classes.StackModel
