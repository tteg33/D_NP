import DiophantineNP.RegisterMachineTrace
import DiophantineNP.TracePorts
import DiophantineNP.BoundedClass

/-! # From bounded native verifiers to short packed-table relations -/
namespace DiophantineNP.Classes.Jones.Machine
open Turing Computability JMTableau BoundedRelation
open scoped Classical
attribute [local instance] FinTM2.kFin
noncomputable section

private def start (M : VerifierMachine) (s : List (Option Bool)) :=
  encode M.tm (initList M.tm (verifierInput M s))

private def finish (M : VerifierMachine) := encode M.tm (verifierHalt M true)

private def inputPort (M : VerifierMachine) : Fin (machineTable M.tm).k :=
  Fintype.equivFin (Port M.tm) (some M.tm.k₀)

private theorem firstInput (M : VerifierMachine) (s : List (Option Bool)) :
    tableSnapshot M.tm (start M s) (inputPort M) = stackCode M.tm M.tm.k₀ (verifierInput M s) := by
  simp [tableSnapshot,start,inputPort,snapshot,encode,initList]

private theorem firstOther (M : VerifierMachine) (s : List (Option Bool)) (j : Fin (machineTable M.tm).k)
    (hj : j ≠ inputPort M) : tableSnapshot M.tm (start M s) j = tableSnapshot M.tm (start M []) j := by
  let e := Fintype.equivFin (Port M.tm)
  have he : e.symm j ≠ some M.tm.k₀ := by
    intro h; apply hj; exact e.symm_apply_eq.mp h
  change snapshot M.tm _ (e.symm j) = snapshot M.tm _ (e.symm j)
  cases hx : e.symm j with
  | none => rfl
  | some k =>
    have hk : k ≠ M.tm.k₀ := by intro hh; apply he; simp [hx,hh]
    simp [snapshot,start,encode,initList,hk]

private def PortsOK (M : VerifierMachine) (s : List (Option Bool)) (z : (machineTable M.tm).Port → ℕ) :=
  z (.first (inputPort M)) = stackCode M.tm M.tm.k₀ (verifierInput M s) ∧
  (∀ j : {j : Fin (machineTable M.tm).k // j ≠ inputPort M},
    z (.first j) = tableSnapshot M.tm (start M []) j) ∧
  (∀ j, z (.last j) = tableSnapshot M.tm (finish M) j) ∧ (machineTable M.tm).Accepts z

private theorem portsOK_iff (M : VerifierMachine) (s : List (Option Bool)) (z) : PortsOK M s z ↔
    (fun j => z (.first j)) = tableSnapshot M.tm (start M s) ∧
    (fun j => z (.last j)) = tableSnapshot M.tm (finish M) ∧ (machineTable M.tm).Accepts z := by
  constructor
  · rintro ⟨hx,ho,hl,hr⟩
    refine ⟨funext fun j => ?_,funext hl,hr⟩
    by_cases hj : j=inputPort M
    · subst j; exact hx.trans (firstInput M s).symm
    · exact (ho ⟨j,hj⟩).trans (firstOther M s j hj).symm
  · rintro ⟨ha,hb,hr⟩
    exact ⟨(congrFun ha _).trans (firstInput M s),fun j => (congrFun ha _).trans (firstOther M s _ j.2),
      fun j => congrFun hb j,hr⟩

private theorem portsOK_sound {f : List (Option Bool) → Bool}
    (M : TM2ComputableInPolyTime tapeEncoding finEncodingBoolBool f)
    (hsup : Supported M.tm (verifierHalt M.toTM2ComputableAux true).stk) {s} {z}
    (h : PortsOK M.toTM2ComputableAux s z) : f s = true := by
  let tm := M.tm
  obtain ⟨a,b,n,v,_,_,_,hr⟩ := (portsOK_iff ..).mp h
  rw [a,b] at hr
  obtain ⟨row,h₀,hn,hstep⟩ := tableRun_sound tm _ _ hr
  let B := Finset.univ.sup fun p : Fin (n+1) × tm.K => ((row p.1).stack p.2).size
  exact acceptingTrace_sound M (B:=B) ⟨hsup,row,h₀,hn,hstep,fun j k =>
    Finset.le_sup (f := fun p : Fin (n+1) × tm.K => ((row p.1).stack p.2).size) (Finset.mem_univ (j,k))⟩

private theorem poly_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b h
  induction p using Polynomial.induction_on' with
  | monomial n c => simpa using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)
  | add p q hp hq => simpa using Nat.add_le_add hp hq

private theorem bits_of_lt {a v : ℕ} (h : a < 2^v) : bits a ≤ v+1 := by
  simpa [bits] using FourSquare.bits_mono h.le

private theorem portsOK_complete {f : List (Option Bool) → Bool}
    (M : TM2ComputableInPolyTime tapeEncoding finEncodingBoolBool f) (r : ℕ) (q : Polynomial ℕ) :
    ∃ p : Polynomial ℕ, ∀ H x (w : Fin r → ℕ), bits x ≤ H → natCost w ≤ q.eval (bits x) →
      f (tape x w) = true → ∃ z, Fits (p.eval H) z ∧ PortsOK M.toTM2ComputableAux (tape x w) z := by
  let tm := M.tm
  let table := machineTable tm
  let P : Polynomial ℕ := Polynomial.X+q+Polynomial.C (r+1)
  let T := M.time.comp P
  let V := Polynomial.C (blockSize tm)*(P+T*Polynomial.C (perStep tm)) + Polynomial.C (bits (machineFactor tm))
  let p := (Polynomial.C table.guard + V + 1)*(T + 1) + 1
  refine ⟨p,fun H x w hx hw hyes => ?_⟩
  let s := tape x w
  obtain ⟨n,hN,_,row,h₀,hn,hs,hS⟩ := acceptingTrace_complete M s hyes
  let S := blockSize tm * (s.length + n*perStep tm)
  let v := S+bits (machineFactor tm)
  have hv := tableRun_complete tm row hs hS
  rw [h₀,hn] at hv
  let z : table.Port → ℕ
    | .first j => tableSnapshot tm (start M.toTM2ComputableAux s) j
    | .last j => tableSnapshot tm (finish M.toTM2ComputableAux) j
    | .capacity => 2^v
    | .clock => 2^((table.guard+v)*n)
  have hend (j) : z (.first j) < 2^v ∧ z (.last j) < 2^v := by
    constructor
    · simpa only [z,start,← h₀] using tableSnapshot_lt tm (row 0) S (hS 0) j
    · simpa only [z,finish,← hn] using tableSnapshot_lt tm (row (Fin.last n)) S (hS _) j
  have hlen : s.length ≤ P.eval H := by
    have := (tape_length_bounds x w).2
    have := hw.trans (poly_mono q hx)
    simpa [P,s] using (tape_length_bounds x w).2.trans (Nat.add_le_add_right (Nat.add_le_add hx this) _)
  have ht : n ≤ T.eval H := by simpa [T,Polynomial.eval_comp] using hN.trans (poly_mono _ hlen)
  have hV : v ≤ V.eval H := by
    simpa [S,v,V] using Nat.add_le_add_right (Nat.mul_le_mul_left (blockSize tm)
      (Nat.add_le_add hlen (Nat.mul_le_mul_right (perStep tm) ht))) (bits (machineFactor tm))
  have hp : (table.guard+v+1)*(n+1)+1 ≤ p.eval H := by
    simpa [p] using Nat.add_le_add_right (Nat.mul_le_mul (Nat.succ_le_succ (Nat.add_le_add_left hV _))
      (Nat.succ_le_succ ht)) 1
  have hvle : v+1 ≤ (table.guard+v+1)*(n+1)+1 := by
    calc v+1 ≤ table.guard+v+1 := by omega
      _ ≤ (table.guard+v+1)*(n+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos n)
      _ ≤ _ := Nat.le_succ _
  refine ⟨z,?_,(portsOK_iff ..).mpr ⟨rfl,rfl,n,v,rfl,rfl,hend,hv⟩⟩
  intro j; cases j with
  | first j => exact ((bits_of_lt (hend j).1).trans hvle).trans hp
  | last j => exact ((bits_of_lt (hend j).2).trans hvle).trans hp
  | capacity => simpa [z,bits] using hvle.trans hp
  | clock =>
    simp only [z,bits,Nat.log2_two_pow]
    exact (Nat.add_le_add_right (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)) 1).trans hp

private theorem const_short {σ : Type} (j : σ) (c : ℕ) : Short (fun x : Env σ => x j = c) := by
  apply (Short.formula (.zero (MvPolynomial.X j - MvPolynomial.C (c : ℤ)))).congr
  intro x; simp [Compiler.Formula.Holds,ints,sub_eq_zero]

/-- A fixed natural polynomial checker for the native certificate budget. -/
abbrev ShortCutoff := ∀ {σ : Type} (x : σ) {r} (w : Fin r → σ) (q : Polynomial ℕ),
  Short (fun z : Env σ => natCost (z ∘ w) ≤ q.eval (bits (z x)))

/-- A fixed checker connecting the accounted numeric certificate with the
actual framed TM2 input stack. -/
abbrev ShortInput := ∀ (M : VerifierMachine) {σ : Type} (x : σ) {r} (w : Fin r → σ) (s : σ),
  Short (fun z : Env σ => z s = stackCode M.tm M.tm.k₀ (verifierInput M (tape (z x) (z ∘ w))))

/-- Bounded actual verifier computations give D membership once their three
fixed numerical checks are available. The ordinary NP certificate cutoff is
checked even on a dishonest, arbitrarily long or large table certificate. -/
theorem np_subset_d_of_short_tables (cut : ShortCutoff) (input : ShortInput)
    (tables : ∀ T : TraceTable, Short T.Accepts) : NP ⊆ D := by
  intro L hL
  obtain ⟨r,q,V,⟨f,⟨M⟩,hV⟩,hL⟩ := hL
  let A := M.toTM2ComputableAux
  let T := machineTable M.tm
  by_cases hs : Supported M.tm (verifierHalt A true).stk
  · let W := Fin r ⊕ T.Port
    let σ := Unit ⊕ W
    let ins : σ := .inl ()
    let field (i : Fin r) : σ := .inr (.inl i)
    let port (i : T.Port) : σ := .inr (.inr i)
    let S : Relation σ := fun z => natCost (z ∘ field) ≤ q.eval (bits (z ins)) ∧
      PortsOK A (tape (z ins) (z ∘ field)) (z ∘ port)
    have hchk : Short S := by
      apply (cut ins field q).and
      apply (input A ins field (port (.first (inputPort A)))).and
      apply (Short.all (fun j : {j : Fin T.k // j ≠ inputPort A} =>
        const_short (port (.first j)) (tableSnapshot M.tm (start A []) j))).and
      exact (Short.all (fun j : Fin T.k => const_short (port (.last j)) (tableSnapshot M.tm (finish A) j))).and
        ((tables T).reindex port)
    obtain ⟨p,hp⟩ := portsOK_complete M r q
    apply Short.mem_D
    apply Short.exists_of S hchk (p+q)
    · intro z u hcheck
      let w (i : Fin r) := u (.inl i)
      have a := hcheck.1
      apply (hL (z ())).2
      exact ⟨w,a,(hV _ _).symm.trans (portsOK_sound M hs hcheck.2)⟩
    · intro H z hz hzL
      obtain ⟨w,hw,hver⟩ := (hL (z ())).1 hzL
      obtain ⟨y,hy,hport⟩ := hp H (z ()) w (hz ()) hw ((hV _ _).trans hver)
      refine ⟨Sum.elim w y,?_,hw,hport⟩
      rintro (i|i) <;> simp only [Sum.elim_inl,Sum.elim_inr,Polynomial.eval_add]
      · have hcoord : bits (w i) ≤ natCost w := Finset.single_le_sum (f := fun j => bits (w j))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        exact ((hcoord.trans hw).trans (poly_mono q (hz ()))).trans (Nat.le_add_left ..)
      · exact (hy i).trans (Nat.le_add_right ..)
  · have empty (x : ℕ) : x ∉ L := by
      intro h
      obtain ⟨w,_,hw⟩ := (hL x).1 h
      obtain ⟨_,_,hy,_⟩ := acceptingTrace_complete M _ ((hV x w).trans hw)
      exact hs hy
    apply Short.mem_D
    apply (Short.formula (σ:=Unit) (.zero 1)).congr
    intro x; simp [Compiler.Formula.Holds,empty]

end
end DiophantineNP.Classes.Jones.Machine
