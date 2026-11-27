import DiophantineNP.MachineCircuitBridge
import Mathlib.Data.Finset.Dedup

/-! # Synchronous finite-stack machines compiled to mathlib TM2

A transition may inspect the heads of all finitely many stacks, pop one digit
and push one digit on each, and select the next finite control state. The
translation to TM2 collects the heads before changing any stack. -/
namespace DiophantineNP.Classes.StackModel
open Turing
open TM2.Stmt

structure Move (α : Type) where
  drop : Bool := false
  put : Option α := none
  deriving Inhabited

def Move.run {α : Type} (m : Move α) (s : List α) : List α :=
  let t := if m.drop then s.tail else s
  match m.put with | none => t | some a => a :: t

def idle {α : Type} : Move α := ⟨false,none⟩
def popOne {α : Type} : Move α := ⟨true,none⟩
def pushOne {α : Type} (a : α) : Move α := ⟨false,some a⟩

@[simp] theorem idle_run {α : Type} (s : List α) : (idle (α := α)).run s = s := rfl
@[simp] theorem pop_run {α : Type} (s : List α) : (popOne (α := α)).run s = s.tail := rfl
@[simp] theorem push_run {α : Type} (a : α) (s : List α) : (pushOne a).run s = a::s := rfl

section
variable {K : Type} [Fintype K] [DecidableEq K] {Γ : K → Type} [∀ k, Fintype (Γ k)]
  [∀ k, Inhabited (Γ k)] {Q : Type} [Fintype Q]

abbrev Memory (Γ : K → Type) := (k : K) → List (Γ k)
abbrev Heads (Γ : K → Type) := (k : K) → Option (Γ k)

/-- The optional control state records halting. Stack updates use the original heads. -/
structure Action (Q : Type) (Γ : K → Type) where
  next : Option Q
  edit : (k : K) → Move (Γ k)

abbrev Code (Q : Type) (Γ : K → Type) := Q → Heads Γ → Action Q Γ

private abbrev Ctl (Q : Type) (Γ : K → Type) := Q × Heads Γ
private abbrev Cmd (Q : Type) (Γ : K → Type) := TM2.Stmt Γ Unit (Ctl Q Γ)

private def noHeads : Heads Γ := fun _ => none

private def getHeads (ks : List K) (next : Cmd Q Γ) : Cmd Q Γ :=
  match ks with
  | [] => next
  | k::ks => peek k (fun st ch => (st.1, Function.update st.2 k ch)) (getHeads ks next)

private def pushOrSkip (k : K) (get : Ctl Q Γ → Move (Γ k)) (next : Cmd Q Γ) : Cmd Q Γ :=
  branch (fun st => (get st).put.isSome)
    (push k (fun st => (get st).put.getD default) next) next

private def writeMoves (code : Code Q Γ) (ks : List K) (next : Cmd Q Γ) : Cmd Q Γ :=
  match ks with
  | [] => next
  | k::ks =>
    let get := fun (st : Ctl Q Γ) => (code st.1 st.2).edit k
    let rest := pushOrSkip k get (writeMoves code ks next)
    branch (fun st => (get st).drop) (pop k (fun st _ => st) rest) rest

omit [Fintype K] [∀ k, Fintype (Γ k)] [∀ k, Inhabited (Γ k)] [Fintype Q] in
private theorem getHeads_spec (ks : List K) (next : Cmd Q Γ) (q : Q) (h : Heads Γ) (s : Memory Γ) :
    TM2.stepAux (getHeads ks next) (q,h) s =
      TM2.stepAux next (q, fun k => if k ∈ ks then (s k).head? else h k) s := by
  induction ks generalizing h with
  | nil => simp [getHeads]
  | cons k ks ih =>
    change TM2.stepAux (getHeads ks next) (q,Function.update h k (s k).head?) s = _
    rw [ih]
    congr 2
    funext j
    by_cases he : j=k
    · subst j; by_cases hm : k∈ks <;> simp [hm]
    · by_cases hm : j∈ks <;> simp [he,hm]

omit [Fintype K] [∀ k, Fintype (Γ k)] [Fintype Q] in
private theorem writeMoves_spec (code : Code Q Γ) (ks : List K) (hs : ks.Nodup)
    (next : Cmd Q Γ) (st : Ctl Q Γ) (s : Memory Γ) :
    TM2.stepAux (writeMoves code ks next) st s =
      TM2.stepAux next st (fun k => if k ∈ ks then ((code st.1 st.2).edit k).run (s k) else s k) := by
  induction ks generalizing s with
  | nil => simp [writeMoves]
  | cons k ks ih =>
    obtain ⟨hk, hs'⟩ := List.nodup_cons.mp hs
    let e := (code st.1 st.2).edit k
    let t : Memory Γ := Function.update s k (e.run (s k))
    have eq1 : TM2.stepAux (writeMoves code (k::ks) next) st s =
        TM2.stepAux (writeMoves code ks next) st t := by
      cases he : (code st.1 st.2).edit k with
      | mk drop put =>
        cases drop <;> cases put <;>
          simp [writeMoves,pushOrSkip,TM2.stepAux,he,t,e,Move.run,Function.update_self]
    rw [eq1, ih hs']
    congr 1
    funext j
    by_cases he : j=k
    · subst j; simp [hk,t,e]
    · simp [he,t]

/-- A single TM2 transition implements one parallel stack step. -/
noncomputable def machine (input output : K) (q₀ : Q) (code : Code Q Γ) : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ := Γ
  Λ := Unit
  main := ()
  σ := Ctl Q Γ
  initialState := (q₀,noHeads)
  m _ := getHeads Finset.univ.toList <| writeMoves code Finset.univ.toList <|
    branch (fun st => (code st.1 st.2).next.isSome)
      (load (fun st => ((code st.1 st.2).next.getD q₀,noHeads)) (goto (fun _ => ())))
      (load (fun _ => (q₀,noHeads)) halt)

structure Config (Q : Type) (Γ : K → Type) where
  state : Option Q
  mem : Memory Γ

def step (code : Code Q Γ) (c : Config Q Γ) : Option (Config Q Γ) :=
  match c.state with
  | none => none
  | some q =>
    let action := code q (fun k => (c.mem k).head?)
    some ⟨action.next, fun k => (action.edit k).run (c.mem k)⟩

def config (q₀ : Q) (c : Config Q Γ) : TM2.Cfg Γ Unit (Ctl Q Γ) :=
  ⟨c.state.map (fun _ => ()), (c.state.getD q₀,noHeads), c.mem⟩

theorem compile_step (input output : K) (q₀ : Q) (code : Code Q Γ) (c : Config Q Γ) :
    (machine input output q₀ code).step (config q₀ c) = (step code c).map (config q₀) := by
  rcases c with ⟨_ | q, s⟩
  · rfl
  · change some (TM2.stepAux (getHeads _ _) (q,noHeads) s) = _
    rw [getHeads_spec]
    simp only [Finset.mem_toList,Finset.mem_univ,if_true]
    rw [writeMoves_spec _ _ (Finset.nodup_toList _)]
    simp only [Finset.mem_toList,Finset.mem_univ,if_true]
    cases h : (code q (fun k => (s k).head?)).next <;>
      simp [TM2.stepAux,h,step,config]

theorem compile_iterate (input output : K) (q₀ : Q) (code : Code Q Γ)
    (n : ℕ) (c : Option (Config Q Γ)) :
    (flip Bind.bind (machine input output q₀ code).step)^[n] (c.map (config q₀)) =
      (((flip Bind.bind (step code))^[n] c).map (config q₀)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
    cases c with
    | none => exact ih none
    | some c => change _^[n] ((machine input output q₀ code).step (config q₀ c)) = _
                rw [compile_step]
                exact ih _

end
end DiophantineNP.Classes.StackModel
