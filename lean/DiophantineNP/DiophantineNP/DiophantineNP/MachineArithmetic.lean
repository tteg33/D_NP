import DiophantineNP.EncodingFacts
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.List

/-! # Finite-state arithmetic verifiers on the project’s TM2 tapes -/
namespace DiophantineNP.Classes.MachineArithmetic

open Turing Computability
open TM2.Stmt

private def alphabet : Bool → Type
  | false => Option Bool
  | true => Bool

/-- A two-stack machine consuming one framed input symbol per iteration. The final
iteration emits the decision and resets the finite control. -/
private def scanner {S : Type} [Fintype S] (initial : S) (read : S → Option Bool → S)
    (accept : S → Bool) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := alphabet
  Λ := Unit
  main := ()
  σ := S × Bool
  initialState := (initial, false)
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m _ := pop false (fun st ch => match ch with
      | some c => (read st.1 c, false)
      | none => (st.1, true))
    (branch Prod.snd (push true (fun st => accept st.1) (load (fun _ => (initial,false)) halt))
      (goto (fun _ => ())))

private def scanStacks (s : List (Option Bool)) (out : List Bool) : (k : Bool) → List (alphabet k)
  | false => s
  | true => out

private theorem update_input (s s' : List (Option Bool)) (out : List Bool) :
    Function.update (scanStacks s out) false s' = scanStacks s' out := by
  funext k
  cases k <;> simp [scanStacks, Function.update]

private theorem update_output (s : List (Option Bool)) (out out' : List Bool) :
    Function.update (scanStacks s out) true out' = scanStacks s out' := by
  funext k
  cases k <;> simp [scanStacks, Function.update]

private def active {S : Type} (q : S) (s : List (Option Bool)) : TM2.Cfg alphabet Unit (S × Bool) :=
  ⟨some (), (q, false), scanStacks s []⟩

private def doneCfg {S : Type} (initial : S) (b : Bool) : TM2.Cfg alphabet Unit (S × Bool) :=
  ⟨none, (initial,false), scanStacks [] [b]⟩

private theorem scan_cons {S : Type} [Fintype S] (initial : S) (read : S → Option Bool → S)
    (accept : S → Bool) (q : S) (c : Option Bool) (s : List (Option Bool)) :
    (scanner initial read accept).step (active q (c::s)) = some (active (read q c) s) := by
  change some (TM2.stepAux _ _ _) = _
  simp [scanner, TM2.stepAux, active, update_input, scanStacks]

private theorem scan_nil {S : Type} [Fintype S] (initial : S) (read : S → Option Bool → S)
    (accept : S → Bool) (q : S) :
    (scanner initial read accept).step (active q []) = some (doneCfg initial (accept q)) := by
  change some (TM2.stepAux _ _ _) = _
  simp [scanner, TM2.stepAux, doneCfg, update_input, update_output, scanStacks]

private theorem scan_all {S : Type} [Fintype S] (initial : S) (read : S → Option Bool → S)
    (accept : S → Bool) (s : List (Option Bool)) (q : S) :
    (flip Bind.bind (scanner initial read accept).step)^[s.length+1] (some (active q s)) =
       some (doneCfg initial (accept (s.foldl read q))) := by
  induction s generalizing q with
  | nil => simpa using scan_nil initial read accept q
  | cons c s ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (flip Bind.bind (scanner initial read accept).step)^[s.length+1] ((scanner initial read accept).step (active q (c::s))) = _
    rw [scan_cons]
    exact ih (read q c)

/-- A total decision procedure given by a finite-state left fold runs in exactly
the tape length plus one TM2 transitions, including on malformed tapes. -/
noncomputable def foldMachine {S : Type} [Fintype S] (initial : S) (read : S → Option Bool → S)
    (accept : S → Bool) :
    TM2ComputableInPolyTime tapeEncoding finEncodingBoolBool (fun s => accept (s.foldl read initial)) where
  tm := scanner initial read accept
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun s := by
    have hi : initList (scanner initial read accept) s = active initial s := by
      unfold initList active
      congr 1
      funext k
      cases k <;> rfl
    have hh (b : Bool) : haltList (scanner initial read accept) [b] = doneCfg initial b := by
      unfold haltList doneCfg
      congr 1
      funext k
      cases k <;> rfl
    refine ⟨⟨s.length+1, ?_⟩, ?_⟩
    · change (flip Bind.bind (scanner initial read accept).step)^[s.length+1]
        (some (initList _ (List.map id s))) = some (haltList _ [accept (s.foldl read initial)])
      simpa only [List.map_id_fun, id_eq, hi, hh] using scan_all initial read accept s initial
    · simp [tapeEncoding]

theorem of_state_fold {r : ℕ} {V : ℕ → (Fin r → ℕ) → Bool} {S : Type} [Fintype S]
    (initial : S) (read : S → Option Bool → S) (accept : S → Bool)
    (correct : ∀ x w, accept ((tape x w).foldl read initial) = V x w) : PolytimePredicate V :=
  ⟨_, ⟨foldMachine initial read accept⟩, correct⟩

private abbrev Prefix (N : ℕ) := {s : List (Option Bool) // s.length ≤ N}

private def pack (N : ℕ) (s : List (Option Bool)) : Option (Prefix N) :=
  if h : s.length ≤ N then some ⟨s,h⟩ else none

private def record (N : ℕ) : Option (Prefix N) → Option Bool → Option (Prefix N)
  | none, _ => none
  | some s, c => pack N (c :: s.val)

private theorem record_pack (N : ℕ) (s : List (Option Bool)) (c : Option Bool) :
    record N (pack N s) c = pack N (c :: s) := by
  by_cases hs : s.length ≤ N
  · simp [hs,pack,record]
  · simp [pack,hs,record]; omega

private theorem fold_record (N : ℕ) (s t : List (Option Bool)) :
    s.foldl (record N) (pack N t) = pack N (s.reverse ++ t) := by
  induction s generalizing t with
  | nil => rfl
  | cons c s ih => simp only [List.foldl_cons, record_pack, ih, List.reverse_cons, List.append_assoc,
                              List.singleton_append]

/-- Any finite set of entire tapes has a total TM2 recognizer running in linear time.
The set itself is fixed, so bounded prefixes fit in the machine's finite control. -/
theorem finiteLanguage (L : Set (List (Option Bool))) (hL : L.Finite) :
    Nonempty (TM2ComputableInPolyTime tapeEncoding finEncodingBoolBool
      (fun s => @decide (s ∈ L) (Classical.propDecidable _))) := by
  classical
  obtain ⟨word,hN⟩ := Set.exists_upper_bound_image _ List.length hL
  let N := word.length
  letI : Fintype (Prefix N) := (List.finite_length_le (Option Bool) N).fintype
  let accept : Option (Prefix N) → Bool := fun st =>
    match st with
    | none => false
    | some s => decide (s.val.reverse ∈ L)
  have heq (s : List (Option Bool)) :
      accept (s.foldl (record N) (pack N [])) = decide (s ∈ L) := by
    rw [fold_record]
    by_cases hs : s.length ≤ N
    · simp [accept,pack,hs]
    · have hh : s ∉ L := fun h => hs (hN s h)
      simp [accept,pack,hs,hh]
  simpa [funext heq] using (show Nonempty (TM2ComputableInPolyTime tapeEncoding finEncodingBoolBool
    (fun s => accept (s.foldl (record N) (pack N [])))) from ⟨foldMachine _ _ _⟩)

private theorem field_inj : Function.Injective field := by
  intro a b h
  have : (encodeNat a).map (some : Bool → Option Bool) =
      (encodeNat b).map some := List.append_cancel_right h
  have h' := congrArg (List.filterMap id) this
  have h'' : encodeNat a = encodeNat b := by simpa [List.filterMap_map, Function.comp_def] using h'
  simpa using congrArg decodeNat h''

private noncomputable def specialize {r : ℕ} (P : MvPolynomial (Option (Fin r)) ℤ) :
    Polynomial ℤ := MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X) P

private theorem specialize_eval (P : MvPolynomial (Option (Fin 0)) ℤ) (x : ℕ) (w : Fin 0 → ℕ) :
    (specialize P).eval (x : ℤ) = polyValue P x w := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [specialize,polyValue]
  | add P Q hp hq => simpa [specialize,polyValue] using congrArg₂ (· + ·) hp hq
  | mul_X P i hp =>
    have hi : i = none := by cases i with
                            | none => rfl
                            | some j => exact Fin.elim0 j
    subst i
    simpa [specialize,polyValue] using congrArg (· * (x : ℤ)) hp

/-- Exact zero testing for every fixed polynomial on the native input with no witness
fields. Its nonzero specialization has finitely many roots; the zero specialization
has a constant accepting machine. -/
theorem univariateEvaluation (P : MvPolynomial (Option (Fin 0)) ℤ) :
    PolytimePredicate (fun x w => decide (polyValue P x w = 0)) := by
  classical
  let Q := specialize P
  by_cases hQ : Q = 0
  · apply of_state_fold () (fun _ _ => ()) (fun _ => true)
    intro x w
    rw [← specialize_eval P x w, show specialize P = 0 from hQ]
    simp
  · let roots : Set ℕ := {x | Q.IsRoot (x : ℤ)}
    have hR : roots.Finite := (Polynomial.finite_setOf_isRoot hQ).preimage (show Function.Injective (fun n : ℕ => (n : ℤ)) from fun a b h => by change (a : ℤ) = (b : ℤ) at h; exact_mod_cast h).injOn
    let L := field '' roots
    obtain ⟨machine⟩ := finiteLanguage L (hR.image _)
    refine ⟨_, ⟨machine⟩, ?_⟩
    intro x w
    have hm : tape x w ∈ L ↔ Q.IsRoot (x : ℤ) := by
      simp only [tape, List.ofFn_zero, List.flatten_nil, List.append_nil]
      exact field_inj.mem_set_image
    simp only [decide_eq_decide]
    exact hm.trans (by rw [Polynomial.IsRoot.def, ← specialize_eval])

/-- The parser accumulates a binary numeral with its next place value. Encountering
a delimiter commits that residue, then starts the next field at place value one. -/
private def arithmeticRead {R S : Type} [Semiring R] (commit : S → R → S) :
    (S × R × R) → Option Bool → S × R × R
  | (q,a,p), some false => (q,a,p+p)
  | (q,a,p), some true => (q,a+p,p+p)
  | (q,a,_), none => (commit q a,0,1)

private theorem arithmetic_pos {R S : Type} [CommSemiring R] (commit : S → R → S)
    (q : S) (n : PosNum) (a p : R) :
    ∃ p' : R, ((encodePosNum n).map some).foldl (arithmeticRead commit) (q,a,p) =
      (q,a+p*((n:ℕ):R),p') := by
  induction n generalizing a p with
  | one => exact ⟨p+p, by simp [encodePosNum,arithmeticRead]⟩
  | bit0 n ih =>
    obtain ⟨p',h⟩ := ih a (p+p)
    refine ⟨p', ?_⟩
    simp only [encodePosNum, List.map_cons, List.foldl_cons, arithmeticRead, h]
    simp [PosNum.cast_bit0]; ring
  | bit1 n ih =>
    obtain ⟨p',h⟩ := ih (a+p) (p+p)
    refine ⟨p', ?_⟩
    simp only [encodePosNum, List.map_cons, List.foldl_cons, arithmeticRead, h]
    simp [PosNum.cast_bit1]; ring

private theorem arithmetic_field {R S : Type} [CommSemiring R] (commit : S → R → S)
    (q : S) (n : ℕ) :
    (field n).foldl (arithmeticRead commit) (q,0,1) = (commit q (n:R),0,1) := by
  change (((encodeNat n).map some ++ [none]).foldl _ _) = _
  rw [List.foldl_append]
  rw [← Num.to_of_nat n]
  generalize (n : Num) = a
  cases a with
  | zero => simp [encodeNat, encodeNum, arithmeticRead]
  | pos a =>
    rw [encodeNat, Num.of_to_nat]
    change List.foldl _ (List.foldl _ _ ((encodePosNum a).map some)) [none] = _
    obtain ⟨p',h⟩ := arithmetic_pos commit q a (0:R) 1
    rw [h]
    simp [arithmeticRead]

private abbrev Residues (R : Type) (N : ℕ) := {l : List R // l.length ≤ N}

private def saveResidue {R : Type} (N : ℕ) (q : Residues R N) (a : R) : Residues R N :=
  ⟨(a::q.val).take N, by simp⟩

private theorem arithmetic_fields {R : Type} [CommSemiring R] (N : ℕ)
    (l : List ℕ) (seed : Residues R N) (h : l.length + seed.val.length ≤ N) :
    ((l.map field).flatten).foldl (arithmeticRead (saveResidue (R := R) N)) (seed,0,1) =
      (⟨(l.map fun n : ℕ => (n:R)).reverse ++ seed.val, by simpa using h⟩,0,1) := by
  induction l generalizing seed with
  | nil => rfl
  | cons n l ih =>
    have hsmall : (n::l).length + seed.val.length ≤ N := h
    simp only [List.length_cons] at hsmall
    have htake : (saveResidue N seed (n:R)).val = (n:R)::seed.val := by
      apply List.take_of_length_le
      simp; omega
    simp only [List.map_cons, List.flatten_cons, List.foldl_append, arithmetic_field]
    rw [ih (saveResidue N seed (n:R)) (by rw [htake]; simp; omega)]
    simp only [htake, List.reverse_cons, List.append_assoc, List.singleton_append]

/-- For any fixed number of fields and any fixed finite commutative semiring,
every predicate of the tuple of residues has a linear-time total TM2 verifier. -/
theorem finiteArithmetic {r : ℕ} (R : Type) [CommSemiring R] [Fintype R]
    (test : List R → Bool) :
    PolytimePredicate (fun x (w : Fin r → ℕ) =>
      test ((x::List.ofFn w).map fun n : ℕ => (n:R))) := by
  classical
  let N := r+1
  letI : Fintype (Residues R N) := (List.finite_length_le R N).fintype
  let start : Residues R N := ⟨[],by simp⟩
  apply of_state_fold (start, (0:R), (1:R)) (arithmeticRead (saveResidue N))
    (fun st => test st.1.val.reverse)
  intro x w
  have ht : tape x w = (((x::List.ofFn w).map field).flatten) := by
    simp [tape, List.map_ofFn, Function.comp_def]
  rw [ht, arithmetic_fields N _ start (by simp [N,start])]
  simp [start]

end DiophantineNP.Classes.MachineArithmetic
