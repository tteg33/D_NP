import DiophantineNP.MachineStackPorts
import DiophantineNP.MachineStackAdder
import DiophantineNP.MachinePolynomial

/-! # A finite-stack binary multiplier

The machine preserves both source words. It consumes the multiplier from
highest to lowest bit and stores the partial product in the destination. Each
round shifts that word and conditionally adds a fresh copy of the multiplicand.
-/
namespace DiophantineNP.Classes.StackModel
open MachineAddition MachinePolynomial
private abbrev todo : Port := .tmp 0
private abbrev copy : Port := .tmp 1
private abbrev scratch : Port := .tmp 2

private def mulStore (xs ys acc pending copyVal scratchVal : List Bool) : WordStore Port :=
  portStore xs ys acc (fun j => if j=0 then pending else if j=1 then copyVal else if j=2 then scratchVal else [])

/-- Fixed control over eight scratch ports; only the first three are touched. -/
private def prepare : WordBlock Port := (copyWord .y copy scratch).seq (scatter copy (fun i => decide (i=todo)))

private def shiftMove (_ : Heads (fun _ : Port => Bool)) (i : Port) : Move Bool :=
  if i=todo then popOne else if i=.dst then pushOne false else idle

private def restore : WordBlock Port := scatter scratch (fun i => decide (i=Port.dst))
private def addRow : WordBlock Port := (copyWord .x copy scratch).seq ((addReverse copy .dst scratch).seq restore)
private def row : WordBlock Port := choose (fun h => decide (h todo=some true))
  ((atomic shiftMove).seq addRow) (atomic shiftMove)
private def rows : WordBlock Port := loop (fun h => (h todo).isSome) row

-- Compare concrete port stores one port at a time. Numeric tests on the
-- eight temporary ports reduce by kernel computation.
local macro "ports" : tactic => `(tactic| (funext i; cases i <;> (try rename_i j; fin_cases j) <;>
  simp [mulStore,portStore,todo,copy,scratch,applyEdits,shiftMove,addState,scatterState,Function.update]))

private theorem run_prepare (xs ys : List Bool) :
    prepare.Runs (mulStore xs ys [] [] [] []) (mulStore xs ys [] ys.reverse [] [])
      (2*(ys.length+1)+(ys.length+1)) := by
  have c := run_copyWord Port.y copy scratch (mulStore xs ys [] [] [] []) (by decide) (by decide) (by decide) rfl rfl
  have ce : Function.update (mulStore xs ys [] [] [] []) copy ((mulStore xs ys [] [] [] []) .y) = mulStore xs ys [] [] ys [] := by ports
  rw [ce] at c
  have r := run_scatter (mulStore xs ys [] [] ys []) copy (fun i => decide (i=todo))
  have re : scatterState (mulStore xs ys [] [] ys []) copy (fun i => decide (i=todo)) []
      ((mulStore xs ys [] [] ys []) copy).reverse = mulStore xs ys [] ys.reverse [] [] := by ports
  rw [re] at r
  exact run_seq c r

private theorem run_shift (xs ys acc tl : List Bool) (b : Bool) :
    (atomic shiftMove).Runs (mulStore xs ys acc (b::tl) [] []) (mulStore xs ys (false::acc) tl [] []) 1 := by
  have e : applyEdits (shiftMove (heads (mulStore xs ys acc (b::tl) [] []))) (mulStore xs ys acc (b::tl) [] []) =
      mulStore xs ys (false::acc) tl [] [] := by ports
  simpa only [e] using run_atomic shiftMove (mulStore xs ys acc (b::tl) [] [])

private theorem run_addRow (xs ys acc tl : List Bool) :
    ∃ n ≤ 4*(xs.length + acc.length + 2),
      addRow.Runs (mulStore xs ys acc tl [] []) (mulStore xs ys (addWords xs acc false) tl [] []) n := by
  have c := run_copyWord Port.x copy scratch (mulStore xs ys acc tl [] []) (by decide) (by decide) (by decide) rfl rfl
  have ce : Function.update (mulStore xs ys acc tl [] []) copy ((mulStore xs ys acc tl [] []) .x) = mulStore xs ys acc tl xs [] := by ports
  rw [ce] at c
  have a := run_addReverse copy Port.dst scratch (by decide) (by decide) (by decide) (mulStore xs ys acc tl xs [])
  have ae : addState (mulStore xs ys acc tl xs []) copy .dst scratch [] []
      ((addWords xs acc false).reverse ++ []) = mulStore xs ys [] tl [] (addWords xs acc false).reverse := by ports
  change (addReverse copy .dst scratch).Runs _ (addState _ copy .dst scratch [] [] ((addWords xs acc false).reverse ++ [])) _ at a
  rw [ae] at a
  have r := run_scatter (mulStore xs ys [] tl [] (addWords xs acc false).reverse) scratch (fun i => decide (i=Port.dst))
  have re : scatterState (mulStore xs ys [] tl [] (addWords xs acc false).reverse) scratch (fun i => decide (i=Port.dst)) []
      ((mulStore xs ys [] tl [] (addWords xs acc false).reverse) scratch).reverse = mulStore xs ys (addWords xs acc false) tl [] [] := by ports
  rw [re] at r
  refine ⟨_,?_,run_seq c (run_seq a r)⟩
  change 2*(xs.length+1)+(max xs.length acc.length+1+((addWords xs acc false).reverse.length+1)) ≤ _
  rw [List.length_reverse]
  have := length_addWords xs acc false; omega

private def rowValue (xs acc : List Bool) (b : Bool) := if b then addWords xs (false::acc) false else false::acc

private theorem run_row (xs ys acc tl : List Bool) (b : Bool) :
    ∃ n ≤ 4*(xs.length+acc.length+4),
      row.Runs (mulStore xs ys acc (b::tl) [] []) (mulStore xs ys (rowValue xs acc b) tl [] []) n := by
  cases b with
  | false => exact ⟨2,by omega,run_choose_false (by rfl) (run_shift xs ys acc tl false)⟩
  | true =>
    obtain ⟨n,hn,ha⟩ := run_addRow xs ys (false::acc) tl
    simp only [List.length_cons] at hn
    refine ⟨1+n+1,by omega,run_choose_true (by rfl) (run_seq (run_shift xs ys acc tl true) ha)⟩

private theorem run_rows (B : ℕ) (xs ys pend past : List Bool) (hx : xs.length ≤ B)
    (hy : pend.length + past.length ≤ B) :
    ∃ n ≤ (pend.length+1)*(16*B+20),
      rows.Runs (mulStore xs ys (multiply xs past) pend [] [])
        (mulStore xs ys (multiply xs (pend.reverse++past)) [] [] []) n := by
  induction pend generalizing past with
  | nil => exact ⟨1,by simp,run_loop_stop rfl⟩
  | cons b tl ih =>
    obtain ⟨m,hm,hr⟩ := run_row xs ys (multiply xs past) tl b
    have hnext : tl.length + (b::past).length ≤ B := by simp at hy ⊢; omega
    obtain ⟨n,hn,ht⟩ := ih (b::past) hnext
    have len := length_multiply xs past
    simp only [List.length_cons] at hy
    refine ⟨m+n+1,?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hn ⊢; omega
    · have hh := run_loop_step (cond:=fun h : Heads (fun _ : Port => Bool) => (h todo).isSome)
        (body:=row) (by rfl) hr ht
      simpa [rows,List.reverse_cons,List.append_assoc] using hh

/-- A finite word-stack gate for the literal schoolbook multiplier. Inputs
are restored and every scratch port is empty again at exit. -/
theorem gateMul {I : Type} [DecidableEq I] (W : Workspace I) (x y dst : I)
    (hx : W.Out x) (hy : W.Out y) (hd : W.Out dst) (hxy : x≠y) (hxd : x≠dst) (hyd : y≠dst) :
    HasWordGate W dst (fun s => MachinePolynomial.multiply (s x) (s y)) := by
  let time : Polynomial ℕ := 3*(Polynomial.X+1)+(Polynomial.X+1)*(16*Polynomial.X+20)
  apply gate_of_port_program (prepare.seq rows) MachinePolynomial.multiply time _ W x y dst hx hy hd hxy hxd hyd
  intro B xs ys hx hy
  obtain ⟨n,hn,tr⟩ := run_rows B xs ys ys.reverse [] hx (by simpa)
  simp only [List.reverse_reverse,List.append_nil] at tr
  have hi : portStore xs ys [] (fun _ => []) = mulStore xs ys [] [] [] [] := by ports
  have ht : mulStore xs ys (multiply xs ys) [] [] [] = portStore xs ys (multiply xs ys) (fun _ => []) := by ports
  rw [hi,←ht]
  refine ⟨_,?_,run_seq (run_prepare xs ys) tr⟩
  simp only [List.length_reverse] at hn
  simp [time]; nlinarith [Nat.mul_le_mul_right (16*B+20) (Nat.succ_le_succ hy)]

end DiophantineNP.Classes.StackModel
