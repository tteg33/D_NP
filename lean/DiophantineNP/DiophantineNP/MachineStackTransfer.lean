import DiophantineNP.MachineStackWords

/-! # Linear-time word transfer, fan-out, and constants -/
namespace DiophantineNP.Classes.StackModel
variable {I : Type} [DecidableEq I]

/-- Pop the source word and push each consumed digit onto all selected destinations. -/
def scatter (src : I) (dest : I → Bool) : WordBlock I where
  Label := Unit
  entry := ()
  code _ h := match h src with
    | none => ⟨none,fun _ => idle⟩
    | some a => ⟨some (),fun i => if i=src then popOne else if dest i then pushOne a else idle⟩

def scatterState (s : WordStore I) (src : I) (dest : I → Bool) (rest sent : List Bool) : WordStore I :=
  fun i => if i=src then rest else if dest i then sent ++ s i else s i

private theorem scatter_it (s : WordStore I) (src : I) (dest : I → Bool) (xs sent : List Bool) :
    (scatter src dest).Runs (scatterState s src dest xs sent)
      (scatterState s src dest [] (xs.reverse ++ sent)) (xs.length+1) := by
  induction xs generalizing sent with
  | nil =>
    apply Path.cons
    simpa [scatter, heads, scatterState] using (Path.refl
      (c := (scatter src dest).code) none (scatterState s src dest [] sent))
  | cons a xs ih =>
    apply Path.cons
    have hs : heads (scatterState s src dest (a::xs) sent) src = some a := by simp [heads,scatterState]
    simp only [scatter,hs]
    have he : applyEdits (fun i => if i=src then popOne else if dest i then pushOne a else idle)
          (scatterState s src dest (a::xs) sent) = scatterState s src dest xs (a::sent) := by
      funext i
      by_cases hi : i=src <;> by_cases hd : dest i <;> simp [applyEdits,scatterState,hi,hd]
    rw [he]
    simpa [scatter, List.append_assoc] using ih (a::sent)

theorem run_scatter (s : WordStore I) (src : I) (dest : I → Bool) :
    (scatter src dest).Runs s (scatterState s src dest [] (s src).reverse) ((s src).length+1) := by
  have h : scatterState s src dest (s src) [] = s := by
    funext i; by_cases hi : i=src <;> simp [scatterState,hi]
  simpa [h] using scatter_it s src dest (s src) []

/-- Push one fixed word onto a register without consuming any other register. -/
def pushWord (dst : I) : List Bool → WordBlock I
  | [] => atomic (fun _ _ => idle)
  | b::bs => (pushWord dst bs).seq (atomic (fun _ i => if i=dst then pushOne b else idle))

theorem run_pushWord (dst : I) (w : List Bool) (s : WordStore I) :
    (pushWord dst w).Runs s (Function.update s dst (w ++ s dst)) (w.length+1) := by
  induction w with
  | nil => simpa [pushWord] using run_atomic (fun _ _ => idle) s
  | cons b w ih =>
    let t := Function.update s dst (w ++ s dst)
    have he : applyEdits (fun i => if i=dst then pushOne b else idle) t =
        Function.update s dst ((b::w) ++ s dst) := by
      funext i
      by_cases hi : i=dst <;> simp [t,applyEdits,hi,Function.update]
    rw [pushWord]
    simpa [he] using run_seq ih (run_atomic (fun _ i => if i=dst then pushOne b else idle) t)

theorem gateLiteral (W : Workspace I) (dst : I) (_ : W.Out dst) (w : List Bool) :
    HasWordGate W dst (fun _ => w) := by
  refine ⟨pushWord dst w, Polynomial.C (w.length+1),?_⟩
  intro B s _ _ hd
  exact ⟨w.length+1, by simp, by simpa [hd] using run_pushWord dst w s⟩

/-- Copy a word through an empty reverse stack, restoring the source. -/
def copyWord (src dst tmp : I) : WordBlock I :=
  (scatter src (fun i => decide (i=tmp))).seq
    (scatter tmp (fun i => decide (i=src ∨ i=dst)))

theorem run_copyWord (src dst tmp : I) (s : WordStore I) (hsd : src ≠ dst)
    (hts : tmp ≠ src) (htd : tmp ≠ dst) (ht : s tmp = []) (hd : s dst = []) :
    (copyWord src dst tmp).Runs s (Function.update s dst (s src)) (2*((s src).length+1)) := by
  let first := scatterState s src (fun i => decide (i=tmp)) [] (s src).reverse
  have htmp : first tmp = (s src).reverse := by simp [first,scatterState,hts,ht]
  have he : scatterState first tmp (fun i => decide (i=src ∨ i=dst)) [] (first tmp).reverse =
      Function.update s dst (s src) := by
    funext i
    by_cases hs : i=src
    · subst i; simp [scatterState,hsd,Ne.symm hts,htmp,first]
    by_cases hd' : i=dst
    · subst i; simp [scatterState,Ne.symm hsd,Ne.symm htd,htmp,first,hd]
    by_cases ht' : i=tmp
    · subst i; simp [scatterState,htd,ht]
    · simp [scatterState,hs,hd',ht',first]
  have run := run_seq (run_scatter s src (fun i => decide (i=tmp)))
    (run_scatter first tmp (fun i => decide (i=src ∨ i=dst)))
  change (copyWord src dst tmp).Runs s _ _ at run
  rw [he,htmp,List.length_reverse] at run
  simpa [two_mul] using run

theorem gateCopy (W : Workspace I) (src dst : I) (hs : W.Out src) (hd : W.Out dst) (hsd : src ≠ dst) :
    HasWordGate W dst (fun s => s src) := by
  refine ⟨copyWord src dst (W.slot 0), 2*(Polynomial.X+1),?_⟩
  intro B s hB he hempty
  exact ⟨_, by simp; have := hB src; omega, run_copyWord _ _ _ _ hsd (hs 0) (hd 0) (he 0) hempty⟩

end DiophantineNP.Classes.StackModel
