import DiophantineNP.MachineStackTransfer

/-! # A composable binary-adder program on arbitrary word registers -/
namespace DiophantineNP.Classes.StackModel
open MachineAddition
variable {I : Type} [DecidableEq I]

/-- An adder that consumes two operands and emits digits onto an output stack. -/
def addReverse (x y z : I) : WordBlock I where
  Label := Bool
  entry := false
  code c h :=
    if h x = none ∧ h y = none then
      ⟨none, fun i => if i=z ∧ c=true then pushOne true else idle⟩
    else
      let a := (h x).getD false
      let b := (h y).getD false
      ⟨some (carry a b c), fun i => if i=x ∨ i=y then popOne else if i=z then pushOne (digit a b c) else idle⟩

def addState (s : WordStore I) (x y z : I) (xs ys out : List Bool) : WordStore I :=
  fun i => if i=x then xs else if i=y then ys else if i=z then out else s i

private theorem add_step_words {xs ys : List Bool} (c : Bool) (h : ¬(xs=[] ∧ ys=[])) :
    addWords xs ys c = digit (xs.head?.getD false) (ys.head?.getD false) c ::
        addWords xs.tail ys.tail (carry (xs.head?.getD false) (ys.head?.getD false) c) := by
  cases xs <;> cases ys <;> simp_all [addWords]

private theorem word_ticks {xs ys : List Bool} (h : ¬(xs=[] ∧ ys=[])) :
    max xs.length ys.length = max xs.tail.length ys.tail.length+1 := by
  cases xs <;> cases ys <;> simp_all [Nat.succ_max_succ]

private theorem run_add_state (s : WordStore I) (x y z : I)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) (xs ys out : List Bool) (c : Bool) :
    Path (addReverse x y z).code (some c) (addState s x y z xs ys out) none
      (addState s x y z [] [] ((addWords xs ys c).reverse ++ out)) (max xs.length ys.length+1) := by
  let st := addState s x y z xs ys out
  have hx : heads st x = xs.head? := by simp [st,heads,addState]
  have hy : heads st y = ys.head? := by simp [st,heads,addState,Ne.symm hxy]
  by_cases done : xs=[] ∧ ys=[]
  · obtain ⟨rfl,rfl⟩ := done
    apply Path.cons
    have ha : (addReverse x y z).code c (heads st) = (⟨none, fun i => if i=z ∧ c=true then pushOne true else idle⟩ : Action Bool _) := by
      simp only [addReverse,hx,hy,List.head?_nil,and_self,↓reduceIte]
    change Path _ ((addReverse x y z).code c (heads st)).next (applyEdits ((addReverse x y z).code c (heads st)).edit st) _ _ _
    rw [ha]
    have he : applyEdits (fun i => if i=z ∧ c=true then pushOne true else idle) st =
        addState s x y z [] [] ((addWords [] [] c).reverse ++ out) := by
      funext i
      cases c <;> by_cases a : i=x <;> by_cases b : i=y <;> by_cases t : i=z <;>
        simp_all [applyEdits,st,addState,addWords]
    rw [he]
    exact .refl _ _
  · let a := xs.head?.getD false
    let b := ys.head?.getD false
    let d := digit a b c
    let c' := carry a b c
    have hstep : ¬(heads st x = none ∧ heads st y = none) := by simpa [hx,hy] using done
    have he : applyEdits (fun i => if i=x ∨ i=y then popOne else if i=z then pushOne d else idle) st =
        addState s x y z xs.tail ys.tail (d::out) := by
      funext i
      by_cases a₁ : i=x <;> by_cases b₁ : i=y <;> by_cases t : i=z <;>
        simp_all [applyEdits,st,addState]
    rw [word_ticks done]
    apply Path.cons
    have ha : (addReverse x y z).code c (heads st) = (⟨some c', fun i => if i=x ∨ i=y then popOne else if i=z then pushOne d else idle⟩ : Action Bool _) := by
      simp [addReverse,hx,hy,c',a,b,d,done]
    change Path _ ((addReverse x y z).code c (heads st)).next (applyEdits ((addReverse x y z).code c (heads st)).edit st) _ _ _
    rw [ha]
    change Path _ (some c') (applyEdits (fun i => if i=x ∨ i=y then popOne else if i=z then pushOne d else idle) st) _ _ _
    rw [he,add_step_words c done,List.reverse_cons,List.append_assoc,List.singleton_append]
    exact run_add_state s x y z hxy hxz hyz xs.tail ys.tail (d::out) c'
termination_by xs.length + ys.length
decreasing_by cases xs <;> cases ys <;> simp_all; omega

theorem run_addReverse (x y z : I) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) (s : WordStore I) :
    (addReverse x y z).Runs s (addState s x y z [] [] ((addWords (s x) (s y) false).reverse ++ s z))
      (max (s x).length (s y).length+1) := by
  have he : addState s x y z (s x) (s y) (s z) = s := by
    funext i; by_cases a : i=x <;> by_cases b : i=y <;> by_cases c : i=z <;> simp_all [addState]
  simpa [he] using run_add_state s x y z hxy hxz hyz (s x) (s y) (s z) false

end DiophantineNP.Classes.StackModel
