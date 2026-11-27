import DiophantineNP.MachineStackWords
import Mathlib.Tactic.DeriveFintype

/-! # Framing a Boolean-register program as a total mathlib TM2

The parser scans the raw tape into one reversed scratch stack per field.
Parallel transfers restore bit order. After running the word program, the
comparison phase checks the two numerical words with zero extension and
empties all working stacks as required by mathlib's halting convention.
-/
namespace DiophantineNP.Classes.StackModel
open MachinePolynomial Turing Computability

private abbrev Key (r : ℕ) := Option (Fin r)
private inductive FramePort (r : ℕ) (I : Type)
  | input | tmp (i : Key r) | reg (i : I) | output
  deriving DecidableEq, Fintype

private def alphabet {r : ℕ} {I : Type} : FramePort r I → Type
  | .input => Option Bool
  | _ => Bool

private instance {r : ℕ} {I : Type} (k : FramePort r I) : Fintype (alphabet k) := by cases k <;> dsimp [alphabet] <;> infer_instance
private instance {r : ℕ} {I : Type} (k : FramePort r I) : Inhabited (alphabet k) := by cases k <;> dsimp [alphabet] <;> infer_instance

private def frame {r : ℕ} {I : Type} (s : List (Option Bool)) (tmp : Key r → List Bool)
    (w : I → List Bool) (o : List Bool) : Memory (@alphabet r I)
  | .input => s
  | .tmp i => tmp i
  | .reg i => w i
  | .output => o

private def ordinal {r : ℕ} : Key r → ℕ
  | none => 0
  | some i => i.val+1

private theorem ordinal_le {r : ℕ} (i : Key r) : ordinal i ≤ r := by
  cases i with
  | none => simp [ordinal]
  | some i => exact i.isLt

private def advance {r : ℕ} (q : Fin (r+2)) : Fin (r+2) := ⟨min (q.val+1) (r+1),by omega⟩

private def select {r : ℕ} (i : Key r) : Fin (r+2) → List (Option Bool) → List Bool
  | _, [] => []
  | q, none::t => select i (advance q) t
  | q, some b::t => if q.val=ordinal i then b::select i q t else select i q t

private def nthWord : ℕ → List (Option Bool) → List Bool
  | _, [] => []
  | 0, none::_ => []
  | n+1, none::s => nthWord n s
  | 0, some b::s => b::nthWord 0 s
  | n+1, some _::s => nthWord (n+1) s

private theorem split_nonempty (s : List (Option Bool)) : ∃ h t, splitWords s=h::t := by
  cases s with
  | nil => exact ⟨_,_,rfl⟩
  | cons c s =>
    cases c with
    | none => exact ⟨_,_,rfl⟩
    | some b => cases hh : splitWords s <;> simp [splitWords,hh]

private theorem nthWord_eq (n : ℕ) (s : List (Option Bool)) : nthWord n s=(splitWords s)[n]?.getD [] := by
  induction s generalizing n with
  | nil => cases n <;> rfl
  | cons c s ih =>
    obtain ⟨h,t,hh⟩ := split_nonempty s
    cases c <;> cases n <;> simp [nthWord,splitWords,ih,hh]

private theorem select_eq {r : ℕ} (i : Key r) (q : Fin (r+2)) (s : List (Option Bool)) :
    select i q s = if q.val ≤ ordinal i then nthWord (ordinal i-q.val) s else [] := by
  induction s generalizing q with
  | nil => simp [select,nthWord]
  | cons c s ih =>
    have hi := ordinal_le i
    cases c with
    | none =>
      rw [select,ih]
      by_cases h : q.val < ordinal i
      · have hq : (advance q).val=q.val+1 := by unfold advance; simp; omega
        have hs : ordinal i - q.val = (ordinal i-(q.val+1))+1 := by omega
        simp [hq,h.le,show q.val+1≤ordinal i by omega,hs,nthWord]
      · have hq : ¬(advance q).val≤ordinal i := by unfold advance; simp; omega
        rw [if_neg hq]
        by_cases he : q.val≤ordinal i
        · rw [if_pos he,show ordinal i-q.val=0 by omega]; rfl
        · rw [if_neg he]
    | some b =>
      rw [select,ih]
      by_cases h : q.val=ordinal i
      · simp [h,nthWord]
      · rw [if_neg h]
        by_cases hq : q.val≤ordinal i
        · have hs : ordinal i-q.val=(ordinal i-q.val-1)+1 := by omega
          rw [if_pos hq,if_pos hq]
          conv_rhs => rw [hs,nthWord]; rw [← hs]
        · simp [hq]

private theorem select_start {r : ℕ} (s : List (Option Bool)) (i : Key r) :
    select i 0 s=fieldAt s i := by
  rw [select_eq]
  simp only [Fin.val_zero,Nat.zero_le,if_true,Nat.sub_zero,nthWord_eq]
  cases i <;> rfl

private def scan {r : ℕ} (I : Type) : Block (@alphabet r I) where
  Label := Fin (r+2)
  entry := 0
  code q h := match h .input with
    | none => ⟨none,fun _ => idle⟩
    | some none => ⟨some (advance q),fun k => match k with | .input => popOne | _ => idle⟩
    | some (some b) => ⟨some q,fun k => match k with
      | .input => popOne | .tmp i => if q.val=ordinal i then pushOne b else idle | _ => idle⟩

private theorem scan_path {r : ℕ} {I : Type} (s : List (Option Bool)) (q : Fin (r+2))
    (buf : Key r → List Bool) (w : WordStore I) (o : List Bool) :
    Path (scan I).code (some q) (frame s buf w o) none
      (frame [] (fun i => (select i q s).reverse ++ buf i) w o) (s.length+1) := by
  induction s generalizing q buf with
  | nil =>
    apply Path.cons
    simpa [scan,heads,frame,select] using (Path.refl (c:=(scan I).code) none (frame [] buf w o))
  | cons ch s ih =>
    cases ch with
    | none =>
      apply Path.cons
      have he : applyEdits (((scan I).code q (heads (frame (none::s) buf w o))).edit) (frame (none::s) buf w o) = frame s buf w o := by
        funext k; cases k <;> rfl
      rw [he]
      exact ih (advance q) buf
    | some b =>
      let g := fun i => if q.val=ordinal i then b::buf i else buf i
      have he : applyEdits (((scan I).code q (heads (frame (some b::s) buf w o))).edit) (frame (some b::s) buf w o) = frame s g w o := by
        funext k
        cases k with
        | tmp i => by_cases h:q.val=ordinal i <;> simp [scan,heads,frame,applyEdits,g,h]
        | _ => rfl
      apply Path.cons
      rw [he]
      change Path _ (some q) _ _ _ _
      convert ih q g using 1
      congr 1
      funext i
      by_cases h:q.val=ordinal i <;> simp [select,g,h]

private abbrev blank {I : Type} : I → List Bool := fun _ => []

private def prepend {α : Type} (h : Option α) (x : List α) : List α :=
  match h with | none => x | some a => a::x

private theorem tail_prepend (x y : List Bool) :
    x.tail.reverse ++ prepend x.head? y = x.reverse ++ y := by
  cases x <;> simp [prepend]

private noncomputable def transfer {r : ℕ} {I : Type} [DecidableEq I] (read : Key r ↪ I) :
    Block (@alphabet r I) := by
  classical
  exact { Label := Unit, entry := (), code := fun _ h =>
    if ∃ i, h (.tmp i) ≠ none then
      ⟨some (), fun k => match k with
        | .tmp _ => popOne
        | .reg j => overlay read (fun _ => idle) (fun i => ⟨false,h (.tmp i)⟩) j
        | _ => idle⟩
    else ⟨none,fun _ => idle⟩ }

private theorem transfer_run {r : ℕ} {I : Type} [DecidableEq I] (read : Key r ↪ I)
    (buf w : Key r → List Bool) (B : ℕ) (hB : ∀ i,(buf i).length≤B) :
    ∃ n≤B+1, (transfer read).Runs (frame [] buf (overlay read blank w) [])
      (frame [] blank (overlay read blank (fun i => (buf i).reverse ++ w i)) []) n := by
  classical
  induction B generalizing buf w with
  | zero =>
    have hbuf : buf=blank := funext fun i => List.length_eq_zero_iff.mp (by have := hB i; omega)
    subst buf
    refine ⟨1,by omega,Path.cons ?_⟩
    simpa [transfer,heads,frame,blank] using (Path.refl (c:=(transfer read).code) none
      (frame [] blank (overlay read blank w) []))
  | succ B ih =>
    by_cases h : ∃ i, (buf i).head? ≠ none
    · have hne : ∃ i,buf i ≠ [] := by simpa using h
      let g := fun i => prepend (buf i).head? (w i)
      obtain ⟨n,hn,hr⟩ := ih (fun i => (buf i).tail) g (fun i => by have := hB i; simp; omega)
      refine ⟨n+1,by omega,Path.cons ?_⟩
      have he : applyEdits (((transfer read).code (transfer read).entry (heads (frame [] buf (overlay read blank w) []))).edit)
          (frame [] buf (overlay read blank w) []) = frame [] (fun i => (buf i).tail) (overlay read blank g) [] := by
        funext k
        cases k with
        | reg j =>
          by_cases hj : ∃ i,read i=j
          · obtain ⟨i,rfl⟩ := hj
            simp [transfer,hne,heads,applyEdits,frame,g,Move.run,prepend]
            cases (buf i).head? <;> rfl
          · simp [transfer,hne,heads,applyEdits,frame,g,overlay_miss _ _ _ _ (not_exists.mp hj)]
        | _ => simp [transfer,hne,heads,applyEdits,frame]
      rw [he]
      have heq : (fun i => (buf i).tail.reverse ++ g i) = fun i => (buf i).reverse ++ w i := funext fun i => tail_prepend _ _
      rw [heq] at hr
      simpa [transfer,heads,hne,frame] using hr
    · have hbuf : buf=blank := funext fun i => List.head?_eq_none_iff.mp (by by_contra hn; exact h ⟨i,hn⟩)
      subst buf
      refine ⟨1,by omega,Path.cons ?_⟩
      simpa [transfer,heads,frame,blank] using (Path.refl (c:=(transfer read).code) none
        (frame [] blank (overlay read blank w) []))

private theorem select_length {r : ℕ} (i : Key r) (q : Fin (r+2)) (s : List (Option Bool)) :
    (select i q s).length ≤ s.length := by
  induction s generalizing q with
  | nil => rfl
  | cons c s ih =>
    cases c with
    | none => exact (ih (advance q)).trans (by simp)
    | some b => by_cases h : q.val=ordinal i <;> simp [select,h] <;> have := ih q <;> omega

private noncomputable def parse {r : ℕ} {I : Type} [DecidableEq I] (read : Key r ↪ I) :=
  (scan I).seq (transfer read)

private theorem parse_run {r : ℕ} {I : Type} [DecidableEq I] (read : Key r ↪ I) (s : List (Option Bool)) :
    ∃ n ≤ 2*s.length+2, (parse read).Runs (frame s blank blank [])
      (frame [] blank (overlay read blank (fieldAt s)) []) n := by
  let b := fun i : Key r => (select i 0 s).reverse
  have hs := scan_path s (0 : Fin (r+2)) (blank : Key r → _) (blank : WordStore I) []
  have hs' : (scan I).Runs (frame s blank blank []) (frame [] b blank []) (s.length+1) := by
    simpa [b,blank] using hs
  obtain ⟨n,hn,ht⟩ := transfer_run read b blank s.length (fun i => by simp [b]; exact select_length ..)
  have hg : overlay read (blank : WordStore I) blank = blank := overlay_restrict _ _
  rw [hg] at ht
  have hfinish : (fun i => (b i).reverse ++ blank i)=fieldAt s := by
    funext i
    simp [b,blank,select_start]
  rw [hfinish] at ht
  exact ⟨s.length+1+n,by omega,run_seq hs' ht⟩

private def wordLift {r : ℕ} {I : Type} (p : WordBlock I) : Block (@alphabet r I) where
  Label := p.Label
  entry := p.entry
  code q h :=
    let a := p.code q (fun i => h (.reg i))
    ⟨a.next,fun k => match k with | .reg i => a.edit i | _ => idle⟩

private theorem lift_path {r : ℕ} {I : Type} (p : WordBlock I) {l s m t n} (h : Path p.code l s m t n) :
    Path (wordLift (r:=r) p).code l (frame [] blank s []) m (frame [] blank t []) n := by
  induction h with
  | refl => exact .refl _ _
  | @cons q s l t n h ih =>
    apply Path.cons
    have he : applyEdits (((wordLift (r:=r) p).code q (heads (frame [] blank s []))).edit) (frame [] blank s []) =
        frame [] blank (applyEdits (p.code q (heads s)).edit s) [] := by
      funext k; cases k <;> rfl
    rw [he]; exact ih

private theorem equal_tails (a b : List Bool) :
    equalWords a b = ((a.head?.getD false == b.head?.getD false) && equalWords a.tail b.tail) := by
  cases a with
  | nil => cases b with
           | nil => rfl
           | cons b bs => cases b <;> simp [equalWords]
  | cons a as => cases b with
                 | nil =>
                   cases a <;> simp [equalWords]
                   cases as <;> simp [equalWords]
                 | cons b bs => rfl

private def sameBit (a b : Bool) := a == b

private noncomputable def compareClear {r : ℕ} {I : Type} (u v : I) : Block (@alphabet r I) := by
  classical
  exact { Label := Bool, entry := true, code := fun ok h =>
    if ∃ i, h (.reg i) ≠ none then
      ⟨some (ok && sameBit ((h (.reg u)).getD false) ((h (.reg v)).getD false)),fun k => match k with
        | .reg _ => popOne | _ => idle⟩
    else ⟨none,fun k => match k with | .output => pushOne ok | _ => idle⟩ }

private theorem compare_path {r : ℕ} {I : Type} (u v : I) (w : WordStore I) (B : ℕ) (hB : ∀ i,(w i).length≤B)
    (ok : Bool) : ∃ n≤B+1, Path (compareClear (r:=r) u v).code (some ok) (frame [] blank w []) none
      (frame [] blank blank [ok && equalWords (w u) (w v)]) n := by
  classical
  have done (ok : Bool) : Path (compareClear (r:=r) u v).code (some ok) (frame [] blank blank []) none
      (frame [] blank blank [ok]) 1 := by
    apply Path.cons
    have he : applyEdits (((compareClear (r:=r) u v).code ok (heads (frame [] blank blank []))).edit)
      (frame [] blank blank []) = frame [] blank blank [ok] := by
      funext k; cases k <;> simp [compareClear,heads,applyEdits,frame,blank]
    rw [he]
    simpa [compareClear,heads,frame,blank] using (Path.refl (c:=(compareClear (r:=r) u v).code) none (frame [] blank blank [ok]))
  induction B generalizing w ok with
  | zero =>
    have h : w=blank := funext fun i => List.length_eq_zero_iff.mp (by have := hB i; omega)
    subst w; exact ⟨1,by omega,by simpa [blank,equalWords] using done ok⟩
  | succ B ih =>
    by_cases h : ∃ i, (w i).head? ≠ none
    · have hnon : ∃ i, w i ≠ [] := by simpa using h
      let flag := ok && ((w u).head?.getD false == (w v).head?.getD false)
      obtain ⟨n,hn,hr⟩ := ih (fun i => (w i).tail) (fun i => by have := hB i; simp; omega) flag
      refine ⟨n+1,by omega,Path.cons ?_⟩
      have he : applyEdits (((compareClear (r:=r) u v).code ok (heads (frame [] blank w []))).edit)
          (frame [] blank w []) = frame [] blank (fun i => (w i).tail) [] := by
        funext k; cases k <;> simp [compareClear,hnon,heads,applyEdits,frame]
      rw [he]
      have hf : (flag && equalWords (w u).tail (w v).tail) = (ok && equalWords (w u) (w v)) := by
        rw [equal_tails (w u) (w v)]; simp [flag,Bool.and_assoc]
      rw [hf] at hr
      simpa [compareClear,heads,frame,hnon,flag,sameBit] using hr
    · have hw : w=blank := funext fun i => List.head?_eq_none_iff.mp (by by_contra hn; exact h ⟨i,hn⟩)
      subst w; exact ⟨1,by omega,by simpa [blank,equalWords] using done ok⟩

private theorem frame_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  induction p using Polynomial.induction_on' with
  | monomial n c => simpa using Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)
  | add p q hp hq => simpa using Nat.add_le_add hp hq

/-- Parse all raw tapes, run the two fixed arithmetic circuits, compare their
little-endian output words, and clear all auxiliary stacks before halting.
The total time is polynomial on every raw tape, including malformed tapes. -/
theorem framed_of_wordProgram {r : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (a b : Circuit (Option (Fin r))) (read : Option (Fin r) ↪ I) (p : WordBlock I) (u v : I)
    (runtime space : Polynomial ℕ) (run : ∀ s : List (Option Bool), ∃ t n,
      p.Runs (overlay read (fun _ => []) (fieldAt s)) t n ∧ n ≤ runtime.eval s.length ∧
      (∀ i, (t i).length ≤ space.eval s.length) ∧ t u = a.word (fieldAt s) ∧ t v = b.word (fieldAt s)) :
    Nonempty (FramedCircuitMachine a b) := by
  classical
  let program := ((parse read).seq (wordLift (r:=r) p)).seq (compareClear u v)
  let overhead : Polynomial ℕ := 2*Polynomial.X+3+runtime+space
  let M := machine (@FramePort.input r I) FramePort.output program.entry program.code
  have exec (s : List (Option Bool)) : ∃ n, n ≤ overhead.eval (circuitWork a b s) ∧
      program.Runs (frame s blank blank []) (frame [] blank blank [circuitDecision a b s]) n := by
    obtain ⟨l,hl,rl⟩ := parse_run read s
    obtain ⟨t,k,rk,hk,hs,hu,hv⟩ := run s
    obtain ⟨j,hj,rj⟩ := compare_path (r:=r) u v t _ hs true
    have last : (compareClear (r:=r) u v).Runs (frame [] blank t []) (frame [] blank blank [circuitDecision a b s]) j := by
      simpa only [Bool.true_and,hu,hv,circuitDecision] using rj
    have hlen : s.length ≤ circuitWork a b s := by
      dsimp only [circuitWork]
      have h := Nat.le_mul_of_pos_right (s.length+1) (show 0<r+2 by omega)
      omega
    refine ⟨(l+k)+j,?_,run_seq (run_seq rl (lift_path p rk)) last⟩
    have htime : l+k+j ≤ overhead.eval s.length := by simp [overhead]; omega
    exact htime.trans (frame_mono overhead hlen)
  have start (s : List (Option Bool)) : initList M s = config program.entry (⟨some program.entry,frame s blank blank []⟩ : Config program.Label (@alphabet r I)) := by
    unfold initList config
    congr 1
    funext k; cases k <;> simp [M,machine,frame,blank]
  have finish (b : Bool) : haltList M [b] = config program.entry (⟨none,frame [] blank blank [b]⟩ : Config program.Label (@alphabet r I)) := by
    unfold haltList config
    congr 1
    funext k; cases k <;> simp [M,machine,frame,blank]
  refine ⟨{tm := M, inputAlphabet := Equiv.refl _, outputAlphabet := Equiv.refl _, overhead := overhead,outputs := fun s => Classical.choice ?_}⟩
  obtain ⟨n,hn,hr⟩ := exec s
  have hi := compile_iterate (@FramePort.input r I) FramePort.output program.entry program.code n
    (some (⟨some program.entry,frame s blank blank []⟩ : Config program.Label (@alphabet r I)))
  rw [hr.iterate] at hi
  have fin : (flip Bind.bind M.step)^[n] (some (initList M s)) = some (haltList M [circuitDecision a b s]) := by
    rw [start,finish]; exact hi
  refine ⟨⟨⟨n,?_⟩,hn⟩⟩
  change (flip Bind.bind M.step)^[n] (some (initList M (s.map id))) = some (haltList M ([circuitDecision a b s].map id))
  simpa using fin

end DiophantineNP.Classes.StackModel
