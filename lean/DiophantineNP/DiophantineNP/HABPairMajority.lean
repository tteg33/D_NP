import DiophantineNP.HABIndependentSum
import DiophantineNP.HABMatrixBind
import DiophantineNP.SmallUniverses
import Mathlib.Data.Nat.Bitwise

/-! # Strict majority over a square universe using unary majority

The formula first counts each row, then adds all rows and compares the two
binary populations. Its parameterized version quantifies two variables of an
arbitrary template, preserving its free variables and its input relation.
-/
namespace DiophantineNP.HABPairMajority
open Counting PrimeFormula WidthFormula FiniteArithmeticGap Finset ShortResidue
open scoped Classical

/-- The number of true ordered pairs in the input relation. -/
def population {U : ℕ} (A : Fin U → Fin U → Bool) : ℕ :=
  (univ.filter (fun p : Fin U × Fin U => A p.1 p.2 = true)).card

private def extendTable {U : ℕ} (A : Fin U → Fin U → Bool) (r c : ℕ) : Bool :=
  if h : r<U ∧ c<U then A ⟨r,h.1⟩ ⟨c,h.2⟩ else false

private def row (U : ℕ) (t : ℕ → ℕ → Bool) (r : ℕ) : ℕ :=
  ((range U).filter (fun c => t r c=true)).card

private noncomputable def rowBit {k} (r j : Fin k) : Template k :=
  (HABCounting.countBitP 0 1 (Predicate.entry 2 0)).syntaxF (fun z => if z=1 then j else r)

private theorem rowBit_spec {k U} (t : ℕ→ℕ→Bool) (r j : Fin k) (e : Fin k → Fin U) :
    (rowBit r j).eval (fun i c => t i.val c.val) e = (row U t (e r).val).testBit (e j).val := by
  apply Bool.eq_iff_iff.mpr
  rw [rowBit, Predicate.valid]
  simp [HABCounting.countBitP,HABCounting.cardP,Predicate.entry,Function.update,row]

/-- A bit of the ordered-pair count, including when a row is entirely true. -/
noncomputable def countBits : Template 1 := rewriteMatrix @rowBit HABIndependentSum.formula id

theorem countBits_correct {U : ℕ} (A : Fin U → Fin U → Bool) (j : Fin U) :
    countBits.eval A (fun _ => j) = (population A).testBit j.val := by
  let t := extendTable A
  have he : A = (fun r c : Fin U => t r.val c.val) := by
    funext r c; simp [t,extendTable,r.isLt,c.isLt]
  have bridge : Readout.prefixSum (row U t) U = population A := by
    have hprefix (n : ℕ) : Readout.prefixSum (row U t) n = ∑ i ∈ range n, row U t i := by
      induction n with
      | zero => simp [Readout.prefixSum]
      | succ n ih => rw [Readout.prefixSum, ih, sum_range_succ]
    rw [hprefix]
    rw [population,Finset.card_filter,Fintype.sum_prod_type]
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro r _
    rw [row,Finset.card_filter,← Fin.sum_univ_eq_sum_range]
    simp [t,extendTable]
  rw [countBits,rewriteMatrix_eval @rowBit A (fun r c : Fin U => (row U t r.val).testBit c.val)
    (fun r c env => by rw [he]; exact rowBit_spec t r c env)]
  rw [← bridge]
  apply HABIndependentSum.formula_correct
  intro i _
  exact (card_filter_le _ _).trans_lt (by rw [card_range]; exact Nat.lt_two_pow_self)

private def readBit {k : ℕ} (p : Template 1) (j : Fin k) : Template k :=
  rewriteMatrix (fun r c => .entry r c) p (fun _ => j)

private theorem readBit_eval {k U : ℕ} (p : Template 1) (j : Fin k) (A : Fin U → Fin U → Bool)
    (e : Fin k → Fin U) : (readBit p j).eval A e = p.eval A (fun _ => e j) :=
  rewriteMatrix_eval _ A A (by intros; rfl) _ _ _

private def diff {k} (p q : Template k) : Template k :=
  .disj (.conj p (.neg q)) (.conj (.neg p) q)

private theorem diff_eval {k U} (p q : Template k) (A : Fin U → Fin U → Bool) (e : Fin k → Fin U) :
    (diff p q).eval A e=true ↔ p.eval A e ≠ q.eval A e := by
  cases hp : p.eval A e <;> cases hq : q.eval A e <;> simp [diff,Template.eval,hp,hq]

/-- Unsigned comparison using the most significant differing bit. -/
def wordLt {k : ℕ} (p q : Template 1) : Template k :=
  .ex (.conj (.neg (readBit p 0)) (.conj (readBit q 0)
    (.neg (.ex (.conj (fromFormula (ltF 1 0)) (diff (readBit p 0) (readBit q 0)))))))

private theorem neg_eval {k U} (p : Template k) (A : Fin U → Fin U → Bool) (e : Fin k → Fin U) :
    p.neg.eval A e = true ↔ ¬ p.eval A e = true := by simp [Template.eval]

theorem wordLt_correct {k U x y : ℕ} (p q : Template 1) (A : Fin U → Fin U → Bool)
    (e : Fin k → Fin U) (hx : x<2^U) (hy : y<2^U)
    (hp : ∀ i : Fin U, p.eval A (fun _ => i) = x.testBit i.val)
    (hq : ∀ i : Fin U, q.eval A (fun _ => i) = y.testBit i.val) :
    (wordLt p q).eval A e=true ↔ x<y := by
  simp only [wordLt,Tex_true,Tconj_true,neg_eval,readBit_eval,diff_eval,fromFormula_eval,
    ltF_true,Fin.cases_zero,hp,hq]
  change (∃ i : Fin U, ¬x.testBit i.val=true ∧ y.testBit i.val=true ∧
    ¬∃ j : Fin U, i.val<j.val ∧ x.testBit j.val≠y.testBit j.val) ↔ x<y
  have high (j : ℕ) (h : U≤j) : x.testBit j=false ∧ y.testBit j=false := by
    have hb : 2^U ≤ 2^j := Nat.pow_le_pow_right (by decide) h
    exact ⟨Nat.testBit_lt_two_pow (hx.trans_le hb),Nat.testBit_lt_two_pow (hy.trans_le hb)⟩
  constructor
  · rintro ⟨i,hi,hy',eq⟩
    apply Nat.lt_of_testBit i.val (by simpa using hi) hy'
    intro j hj
    by_cases hj' : j<U
    · exact Classical.byContradiction (fun h => eq ⟨⟨j,hj'⟩,hj,h⟩)
    · obtain ⟨h₁,h₂⟩ := high j (by omega)
      rw [h₁,h₂]
  · intro hxy
    let s := (range U).filter (fun i => x.testBit i ≠ y.testBit i)
    have hn : s.Nonempty := by
      by_contra h
      apply hxy.ne
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j<U
      · exact Classical.byContradiction fun hne => h ⟨j,mem_filter.mpr ⟨mem_range.mpr hj,hne⟩⟩
      · obtain ⟨h₁,h₂⟩ := high j (by omega)
        rw [h₁,h₂]
    let i := s.max' hn
    obtain ⟨hi,hd⟩ := mem_filter.mp (s.max'_mem hn)
    have later (j : ℕ) (hij : i<j) : x.testBit j=y.testBit j := by
      by_cases hj : j<U
      · by_contra hne
        exact (Nat.not_le_of_gt hij) (s.le_max' j (mem_filter.mpr ⟨mem_range.mpr hj,hne⟩))
      · obtain ⟨h₁,h₂⟩ := high j (by omega)
        rw [h₁,h₂]
    change x.testBit i ≠ y.testBit i at hd
    have impossible (h₁ : x.testBit i=true) (h₂ : y.testBit i=false) : False :=
      hxy.asymm (Nat.lt_of_testBit i h₂ h₁ (fun j hj => (later j hj).symm))
    refine ⟨⟨i,mem_range.mp hi⟩,?_,?_,fun ⟨j,hij,hne⟩ => hne (later j hij)⟩
    all_goals
      cases hx' : x.testBit i <;> cases hy' : y.testBit i <;>
        simp_all only [not_true_eq_false,not_false_eq_true,Bool.false_eq_true]

private noncomputable def negativeBits : Template 1 :=
  rewriteMatrix (fun r c => .neg (.entry r c)) countBits id

private theorem negativeBits_spec {U : ℕ} (A : Fin U → Fin U → Bool) (j : Fin U) :
    negativeBits.eval A (fun _ => j) = (population (fun r c => !(A r c))).testBit j.val := by
  rw [negativeBits,rewriteMatrix_eval _ A (fun r c => !(A r c)) (by intros; rfl)]
  exact countBits_correct _ j

private theorem splitPopulation {U : ℕ} (A : Fin U → Fin U → Bool) :
    population A + population (fun r c => !(A r c)) = U*U := by
  simpa [population,Bool.not_eq_true'] using
    (univ (α:=Fin U × Fin U)).filter_card_add_filter_neg_card_eq_card (fun p => A p.1 p.2=true)

theorem squareFits {U : ℕ} (h : 5≤U) : U*U<2^U := by
  induction U,h using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ]
    have h : (n+1)*(n+1) ≤ 2*(n*n) := by nlinarith [Nat.mul_self_le_mul_self hn]
    omega

private noncomputable def large : Template 1 := wordLt negativeBits countBits

private theorem large_spec {U : ℕ} (hU : 5≤U) (A : Fin U → Fin U → Bool) (j : Fin U) :
    large.eval A (fun _ => j)=true ↔ U*U/2<population A := by
  have h := splitPopulation A
  have hcap := squareFits hU
  rw [large,wordLt_correct _ _ _ _ (x:=population (fun r c => !(A r c))) (y:=population A)
    (by omega) (by omega) (negativeBits_spec A) (countBits_correct A)]
  omega

private def above (n : ℕ) : Template 1 := fromFormula (.ex (isNat n 0))

private theorem above_spec {U : ℕ} (n : ℕ) (A : Fin U → Fin U → Bool) (j : Fin U) :
    (above n).eval A (fun _ => j)=true ↔ n<U := by
  rw [above,fromFormula_eval,exists_true]
  simp only [isNat_spec,Fin.cases_zero]
  exact ⟨fun ⟨i,hi⟩ => hi ▸ i.isLt,fun h => ⟨⟨n,h⟩,rfl⟩⟩

private noncomputable def fixed (n : ℕ) : Template 1 :=
  fixedTable n (fun A _ => decide (n*n/2<population A))

private noncomputable def patch : ℕ → Template 1 → Template 1
  | 0, p => p
  | n+1, p => patch n (.disj (.conj (above n) p) (.conj (.neg (above n)) (fixed n)))

private theorem patch_spec (n : ℕ) (p : Template 1)
    (h : ∀ {U}, n≤U → ∀ (A : Fin U → Fin U → Bool) (j : Fin U),
      p.eval A (fun _ => j)=true ↔ U*U/2 < population A)
    {U : ℕ} (A : Fin U → Fin U → Bool) (j : Fin U) :
    (patch n p).eval A (fun _ => j)=true ↔ U*U/2 < population A := by
  induction n generalizing p with
  | zero => exact h (Nat.zero_le _) A j
  | succ n ih =>
    apply ih
    intro V hv B k
    rw [Tdisj_true,Tconj_true,Tconj_true,neg_eval,above_spec]
    by_cases hgt : n<V
    · simp [hgt,h hgt B k]
    · have eq : V=n := by omega
      subst V
      simp [fixed,fixedTable_eval]

/-- Majority of the input relation over all ordered pairs of the index domain. -/
noncomputable def formula : Template 0 := .ex (patch 5 large)

theorem formula_correct {U : ℕ} (A : Fin U → Fin U → Bool) (e : Fin 0 → Fin U) :
    formula.eval A e=true ↔ U*U/2 < population A := by
  rw [formula,Tex_true]
  have step (i : Fin U) : (patch 5 large).eval A (Fin.cases i e)=true ↔ U*U/2 < population A := by
    have eq : Fin.cases i e = (fun _ : Fin 1 => i) := funext fun z => by fin_cases z; rfl
    rw [eq]; exact patch_spec 5 large (fun h => large_spec h) A i
  constructor
  · exact fun ⟨i,hi⟩ => (step i).mp hi
  · intro h
    have hu : 0<U := by
      by_contra! h'
      have hz : U=0 := by omega
      subst U; simp [population] at h
    exact ⟨⟨0,hu⟩,(step _).mpr h⟩

/-- A two-variable strict majority quantifier in ordinary unary-majority syntax.
Slot 0 of the body is its column, slot 1 is its row, and the rest are free. -/
noncomputable def pairMaj {k} (body : Template (k+2)) : Template k :=
  HABMatrix.bind body formula id Fin.elim0

theorem pairMaj_correct {k U : ℕ} (body : Template (k+2)) (A : Fin U → Fin U → Bool)
    (e : Fin k → Fin U) :
    (pairMaj body).eval A e=true ↔ U*U/2 <
      (univ.filter (fun p : Fin U × Fin U => body.eval A (extend p.2 p.1 e)=true)).card := by
  rw [pairMaj,HABMatrix.bind_spec,formula_correct]
  rfl

end DiophantineNP.HABPairMajority
