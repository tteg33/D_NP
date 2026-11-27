import DiophantineNP.HABSourceArithmetic

/-! # Relativizing majority formulas to a finite prefix

Among the positions outside the prefix, accept exactly the odd ones. Their
number is the difference between the two strict majority thresholds. This
gives a syntax translation even when the smaller and larger sizes have
different parities. -/
namespace DiophantineNP.HAB
open scoped Classical

private def up {k a} (σ : Fin k → Fin a) : Fin (k+1) → Fin (a+1) :=
  Fin.cases 0 (Fin.succ ∘ σ)

private def oddIndex {k} (i : Fin k) : Form k :=
  .ex (.conj (indexNat 0 0) (.BIT 0 i.succ))

private theorem oddIndex_correct {k U} (i : Fin k) (A : Matrix U) (e : Fin k → Fin U) :
    (oddIndex i).Holds A e ↔ (e i).val % 2 = 1 := by
  simp only [oddIndex,Form.Holds,indexNat_correct,Fin.cases_zero,Fin.cases_succ]
  constructor
  · rintro ⟨z,hz,h⟩; simpa [hz,Nat.testBit_zero] using h
  · intro h
    exact ⟨⟨0,by have := (e i).isLt; omega⟩,rfl,by simpa [Nat.testBit_zero] using h⟩

/-- Run a fixed formula on the elements strictly below the cutoff variable. -/
def Form.onPrefix : {k : ℕ} → Form k → {a : ℕ} → (Fin k → Fin a) → Fin a → Form a
  | _, .eq i j, _, σ, _ => .eq (σ i) (σ j)
  | _, .lt i j, _, σ, _ => .lt (σ i) (σ j)
  | _, .BIT i j, _, σ, _ => .BIT (σ i) (σ j)
  | _, .input i j, _, σ, _ => .input (σ i) (σ j)
  | _, .neg p, _, σ, v => .neg (p.onPrefix σ v)
  | _, .disj p q, _, σ, v => .disj (p.onPrefix σ v) (q.onPrefix σ v)
  | _, .conj p q, _, σ, v => .conj (p.onPrefix σ v) (q.onPrefix σ v)
  | _, .ex p, _, σ, v => .ex (.conj (.lt 0 v.succ) (p.onPrefix (up σ) v.succ))
  | _, .all p, _, σ, v => .all (.disj (.neg (.lt 0 v.succ)) (p.onPrefix (up σ) v.succ))
  | _, .many p, _, σ, v =>
    .many (.disj (.conj (.lt 0 v.succ) (p.onPrefix (up σ) v.succ))
      (.conj (.neg (.lt 0 v.succ)) (oddIndex 0)))

private noncomputable def prefixVote {V} (P : Fin V → Prop) (n : ℕ) : ℕ :=
  if h : n<V then (if P ⟨n,h⟩ then 1 else 0) else if n%2=1 then 1 else 0

private theorem voteCount {V U} (P : Fin V → Prop) (hu : V≤U) :
    (∑ z : Fin U, prefixVote P z.val) =
      (Finset.univ.filter P).card + (U/2-V/2) := by
  classical
  induction U, hu using Nat.le_induction with
  | base =>
    simp only [Nat.sub_self,Nat.add_zero,Finset.card_filter]
    apply Finset.sum_congr rfl
    intro z _; simp [prefixVote,z.isLt]
  | succ U h ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ z : Fin U, prefixVote P z.val) + prefixVote P U = _
    rw [ih]
    by_cases ho : U%2=1 <;> simp [prefixVote,Nat.not_lt.mpr h,ho] <;> omega

/-- Restrict the input matrix to its leading square. -/
def prefixMatrix {U V} (A : Matrix U) (h : V≤U) : Matrix V :=
  fun i j => A (i.castLE h) (j.castLE h)

private abbrev prepend {n T : ℕ} (i : Fin T) (e : Fin n → Fin T) : Fin (n+1) → Fin T :=
  Fin.cases i e

private theorem up_env {k a U V} (h : V≤U) (σ : Fin k → Fin a)
    {e : Fin a → Fin U} {s : Fin k → Fin V}
    (he : ∀ i, e (σ i) = (s i).castLE h) (z : Fin V) :
    ∀ i : Fin (k+1), Fin.cases (motive := fun _ => Fin U) (z.castLE h) e (up σ i) =
        (Fin.cases (motive := fun _ => Fin V) z s i).castLE h := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact he j

/-- Truth is preserved for every input matrix and assignment in the prefix. -/
theorem Form.onPrefix_correct {k a U V} (p : Form k) (σ : Fin k → Fin a) (v : Fin a)
    (A : Matrix U) (h : V≤U) (e : Fin a → Fin U) (s : Fin k → Fin V)
    (hv : (e v).val=V) (he : ∀ i, e (σ i)=(s i).castLE h) :
    (p.onPrefix σ v).Holds A e ↔ p.Holds (prefixMatrix A h) s := by
  classical
  induction p generalizing a with
  | eq i j => simp [Form.onPrefix,Form.Holds,he,Fin.ext_iff]
  | lt i j | BIT i j | input i j => simp only [Form.onPrefix,Form.Holds,he,prefixMatrix,Fin.lt_def,Fin.coe_castLE]
  | neg p ih => exact not_congr (ih σ v e s hv he)
  | disj p q ih jh => exact or_congr (ih σ v e s hv he) (jh σ v e s hv he)
  | conj p q ih jh => exact and_congr (ih σ v e s hv he) (jh σ v e s hv he)
  | ex p ih =>
    simp only [Form.onPrefix,Form.Holds,Fin.cases_zero,Fin.cases_succ,Fin.lt_def,hv]
    constructor
    · rintro ⟨z,hz,hp⟩
      let t : Fin V := ⟨z.val,hz⟩
      exact ⟨t,(ih (up σ) v.succ (prepend (t.castLE h) e) (prepend t s) hv (up_env h σ he t)).mp hp⟩
    · rintro ⟨z,hp⟩
      exact ⟨z.castLE h,z.isLt,(ih (up σ) v.succ (prepend (z.castLE h) e) (prepend z s) hv (up_env h σ he z)).mpr hp⟩
  | all p ih =>
    simp only [Form.onPrefix,Form.Holds,Fin.cases_zero,Fin.cases_succ,Fin.lt_def,hv]
    constructor
    · intro hall z
      exact (ih (up σ) v.succ (prepend (z.castLE h) e) (prepend z s) hv (up_env h σ he z)).mp ((hall (z.castLE h)).resolve_left (not_not_intro z.isLt))
    · intro hall z
      by_cases hz : z.val<V
      · let t : Fin V := ⟨z.val,hz⟩
        exact Or.inr ((ih (up σ) v.succ (prepend (t.castLE h) e) (prepend t s) hv (up_env h σ he t)).mpr (hall t))
      · exact Or.inl hz
  | many p ih =>
    let P (z : Fin V) := p.Holds (prefixMatrix A h) (Fin.cases z s)
    simp only [Form.onPrefix,Form.Holds,Fin.cases_zero,Fin.cases_succ,Fin.lt_def,hv,oddIndex_correct]
    rw [Finset.card_filter]
    have hc : (∑ x : Fin U, if (x.val<V ∧ (p.onPrefix (up σ) v.succ).Holds A (Fin.cases x e)) ∨
                (¬x.val<V ∧ x.val%2=1) then 1 else 0) = ∑ x : Fin U, prefixVote P x.val := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z.val<V
      · let t : Fin V := ⟨z.val,hz⟩
        have hh := ih (up σ) v.succ (prepend (t.castLE h) e) (prepend t s) hv (up_env h σ he t)
        change ((p.onPrefix (up σ) v.succ).Holds A (Fin.cases z e) ↔ P t) at hh
        simp [prefixVote,hz,hh,t]
      · simp [prefixVote,hz]
    rw [hc,voteCount P h]
    change _ ↔ V < 2 * (Finset.univ.filter P).card
    omega

end DiophantineNP.HAB
