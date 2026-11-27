import DiophantineNP.EncodingFacts

/-! # An unbounded binary-adder fragment on actual TM2 tapes

The input tapes contain little-endian binary words, of independently arbitrary
width. The output stack receives the bits in reverse, as it must when pushing
the successive low-order digits. The final carry is included. -/
namespace DiophantineNP.Classes.MachineAddition

open Turing TM2.Stmt Computability

/-- Numerical value of a little-endian bit word; leading high zeroes are allowed. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

def digit (a b c : Bool) : Bool := xor (xor a b) c

def carry (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

private theorem fullAdder (a b c : Bool) :
    (digit a b c).toNat + 2*(carry a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

def addWords : List Bool → List Bool → Bool → List Bool
  | [], [], c => if c then [true] else []
  | a::xs, [], c => digit a false c :: addWords xs [] (carry a false c)
  | [], b::ys, c => digit false b c :: addWords [] ys (carry false b c)
  | a::xs, b::ys, c => digit a b c :: addWords xs ys (carry a b c)
termination_by xs ys _ => xs.length + ys.length

private theorem addInd {M : List Bool → List Bool → Bool → Prop}
    (done : ∀ c, M [] [] c)
    (left : ∀ a xs c, M xs [] (carry a false c) → M (a::xs) [] c)
    (right : ∀ b ys c, M [] ys (carry false b c) → M [] (b::ys) c)
    (both : ∀ a xs b ys c, M xs ys (carry a b c) → M (a::xs) (b::ys) c)
    (xs ys : List Bool) (c : Bool) : M xs ys c := by
  cases xs with
  | nil =>
    cases ys with
    | nil => exact done c
    | cons b ys => exact right b ys c (addInd done left right both [] ys _)
  | cons a xs =>
    cases ys with
    | nil => exact left a xs c (addInd done left right both xs [] _)
    | cons b ys => exact both a xs b ys c (addInd done left right both xs ys _)
termination_by xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

theorem value_addWords (xs ys : List Bool) (c : Bool) :
    value (addWords xs ys c) = value xs + value ys + c.toNat := by
  induction xs,ys,c using addInd with
  | done c => cases c <;> simp [addWords,value]
  | left a xs c ih => rw [addWords]; simp only [value,ih]; have h := fullAdder a false c; simp at h; omega
  | right b ys c ih => rw [addWords]; simp only [value,ih]; have h := fullAdder false b c; simp at h; omega
  | both a xs b ys c ih => rw [addWords]; simp only [value,ih]; have := fullAdder a b c; omega

theorem length_addWords (xs ys : List Bool) (c : Bool) :
    (addWords xs ys c).length ≤ max xs.length ys.length + 1 := by
  induction xs,ys,c using addInd with
  | done c => cases c <;> simp [addWords]
  | left a xs c ih => simpa [addWords] using ih
  | right b ys c ih => simpa [addWords] using ih
  | both a xs b ys c ih => simpa [addWords, Nat.succ_max_succ] using ih

private abbrev K := Option Bool
private abbrev Γ := fun _ : K => Bool
private abbrev State := Bool × Option Bool × Option Bool

/-- Main label of the TM2 program. The finite state caches one digit per input and the carry. -/
def program : Unit → TM2.Stmt Γ Unit State := fun _ =>
  pop none (fun st a => (st.1,a,none))
    (pop (some false) (fun st b => (st.1,st.2.1,b))
      (branch (fun st => st.2.1.isNone && st.2.2.isNone)
        (branch Prod.fst
          (push (some true) (fun _ => true) (load (fun _ => (false,none,none)) halt))
          (load (fun _ => (false,none,none)) halt))
        (push (some true) (fun st => digit (st.2.1.getD false) (st.2.2.getD false) st.1)
          (load (fun st => (carry (st.2.1.getD false) (st.2.2.getD false) st.1,none,none))
            (goto (fun _ => ()))))))

private def tapes (xs ys out : List Bool) : K → List Bool
  | none => xs
  | some false => ys
  | some true => out

private theorem update_a (x x' y o : List Bool) :
    Function.update (tapes x y o) none x' = tapes x' y o := by
  funext k; rcases k with _ | ( _ | _) <;> simp [tapes, Function.update]
private theorem update_b (x y y' o : List Bool) :
    Function.update (tapes x y o) (some false) y' = tapes x y' o := by
  funext k; rcases k with _ | ( _ | _) <;> simp [tapes, Function.update]
private theorem update_o (x y o o' : List Bool) :
    Function.update (tapes x y o) (some true) o' = tapes x y o' := by
  funext k; rcases k with _ | ( _ | _) <;> simp [tapes, Function.update]

/-- Configuration immediately before reading the next pair of digits. -/
def active (x y o : List Bool) (c : Bool) : TM2.Cfg Γ Unit State :=
  ⟨some (), (c,none,none), tapes x y o⟩

/-- A clean stopped configuration with both operands consumed. -/
def finished (o : List Bool) : TM2.Cfg Γ Unit State :=
  ⟨none,(false,none,none),tapes [] [] o⟩

private theorem next_nil (o : List Bool) (c : Bool) :
    TM2.step program (active [] [] o c) = some (finished (if c then true :: o else o)) := by
  cases c <;> simp [TM2.step, program, TM2.stepAux, active, finished, update_a, update_b, update_o, tapes]

private theorem next_a (a : Bool) (x o : List Bool) (c : Bool) :
    TM2.step program (active (a::x) [] o c) = some (active x [] (digit a false c::o) (carry a false c)) := by
  simp [TM2.step,program,TM2.stepAux,active,update_a,update_b,update_o,tapes]

private theorem next_b (b : Bool) (y o : List Bool) (c : Bool) :
    TM2.step program (active [] (b::y) o c) = some (active [] y (digit false b c::o) (carry false b c)) := by
  simp [TM2.step,program,TM2.stepAux,active,update_a,update_b,update_o,tapes]

private theorem next_ab (a b : Bool) (x y o : List Bool) (c : Bool) :
    TM2.step program (active (a::x) (b::y) o c) =
      some (active x y (digit a b c::o) (carry a b c)) := by
  simp [TM2.step,program,TM2.stepAux,active,update_a,update_b,update_o,tapes]

/-- Exact execution including halting. Neither canonical numerals nor a width bound are assumed. -/
theorem steps_add (xs ys : List Bool) (c : Bool) (out : List Bool) :
    (flip Bind.bind (TM2.step program))^[max xs.length ys.length+1] (some (active xs ys out c)) =
      some (finished ((addWords xs ys c).reverse ++ out)) := by
  induction xs,ys,c using addInd generalizing out with
  | done c =>
    rw [addWords]
    cases c <;> simpa using next_nil out _
  | left a xs c ih =>
    rw [addWords]
    simp only [List.length_cons, List.length_nil, Nat.max_zero, List.reverse_cons, List.append_assoc,
       List.singleton_append, Function.iterate_succ_apply]
    change _^[xs.length+1] (TM2.step program (active (a::xs) [] out c)) = _
    rw [next_a]
    simpa only [List.length_nil, Nat.max_zero] using ih (digit a false c :: out)
  | right b ys c ih =>
    rw [addWords]
    simp only [List.length_cons, List.length_nil, Nat.zero_max, List.reverse_cons, List.append_assoc,
       List.singleton_append, Function.iterate_succ_apply]
    change _^[ys.length+1] (TM2.step program (active [] (b::ys) out c)) = _
    rw [next_b]
    simpa only [List.length_nil, Nat.zero_max] using ih (digit false b c :: out)
  | both a xs b ys c ih =>
    rw [addWords]
    rw [List.length_cons, List.length_cons, Nat.succ_max_succ, Function.iterate_succ_apply]
    change _^[max xs.length ys.length+1] (TM2.step program (active (a::xs) (b::ys) out c)) = _
    rw [next_ab]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (digit a b c :: out)

end DiophantineNP.Classes.MachineAddition
