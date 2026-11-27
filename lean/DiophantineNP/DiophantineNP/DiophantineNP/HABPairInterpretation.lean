import DiophantineNP.HABPairMajority
import DiophantineNP.HABSourceTranslation

/-! # Interpreting the HAB language on a square universe

Each element of the larger domain has two base-U digits. Lexicographic order
yields its rank, whose binary digits can be read by counting the preceding
pairs. This gives the source BIT atom even when U is not a power of two.
-/
namespace DiophantineNP.HABPairInterpretation
open Counting WidthFormula PrimeFormula FiniteArithmeticGap Finset HAB HABPairMajority
open scoped Classical

/-- The first digit is the major (row) coordinate. -/
abbrev code {U : ℕ} (h l : Fin U) : Fin (U*U) := finProdFinEquiv (h,l)

private theorem code_lt {U : ℕ} (h l h' l' : Fin U) :
    code h l < code h' l' ↔ h<h' ∨ (h=h' ∧ l<l') := by
  change l.val+U*h.val < l'.val+U*h'.val ↔ _
  have gap {a b : Fin U} (hab : a<b) : U*a.val+U ≤ U*b.val := by
    simpa [Nat.mul_succ] using Nat.mul_le_mul_left U (show a.val+1≤b.val from hab)
  rcases lt_trichotomy h h' with hlt | rfl | hgt
  · have := gap hlt
    simp [hlt]; omega
  · simp only [lt_self_iff_false,false_or,true_and,Nat.add_lt_add_iff_right,Fin.lt_def]
  · have := gap hgt
    simp [hgt.ne',hgt.not_gt]; omega

private def lex {k : ℕ} (h l h' l' : Fin k) : Template k :=
  .disj (fromFormula (ltF h h')) (.conj (.atom (.eqv h h')) (fromFormula (ltF l l')))

private theorem lex_spec {k U : ℕ} (h l h' l' : Fin k) (A : Matrix U) (e : Fin k → Fin U) :
    (lex h l h' l').eval A e=true ↔ code (e h) (e l) < code (e h') (e l') := by
  rw [lex,Tdisj_true,Tconj_true,fromFormula_eval,fromFormula_eval,ltF_true,ltF_true,code_lt]
  simp only [Template.eval,Atom.eval,decide_eq_true_eq,Fin.ext_iff,Fin.lt_def]

private def rankBody {k : ℕ} (h l : Fin k) : Template (k+2) :=
  lex 1 0 h.succ.succ l.succ.succ

private noncomputable def rankBit {k : ℕ} (h l j : Fin k) : Template k :=
  HABMatrix.bind (rankBody h l) countBits id (fun _ => j)

private theorem rankBit_spec {k U : ℕ} (h l j : Fin k) (A : Matrix U) (e : Fin k → Fin U) :
    (rankBit h l j).eval A e = (code (e h) (e l)).val.testBit (e j).val := by
  rw [rankBit,HABMatrix.bind_spec]
  simp only [Function.comp_def,id_eq,countBits_correct]
  congr 1
  rw [population,← Fin.card_Iio (code (e h) (e l))]
  apply card_equiv finProdFinEquiv
  intro p
  simp only [mem_filter,mem_univ,true_and,mem_Iio,rankBody,lex_spec]
  rfl

private def numeral {k} (n : ℕ) (x : Fin k) := fromFormula (isNat n x)

private def small {k : ℕ} : Template k := .neg (.ex (fromFormula (isNat 3 0)))

private theorem small_spec {k U : ℕ} (A : Matrix U) (e : Fin k → Fin U) :
    small.eval A e=true ↔ U≤3 := by
  simp only [small,Template.eval.eq_4,Bool.not_eq_true',← Bool.not_eq_true,Tex_true,fromFormula_eval,
    isNat_spec,Fin.cases_zero,not_exists]
  exact ⟨fun h => by by_contra! h'; exact h ⟨3,h'⟩ rfl,
    fun h i hi => by have := i.isLt; omega⟩

private def overflowBit {k} (ph pl nh nl : Fin k) : Template k :=
  .conj small (.conj (numeral 1 ph) (.conj (numeral 0 pl) (.conj (numeral 2 nh) (numeral 2 nl))))

/-- The only nonzero bit whose index requires a nonzero major digit occurs
in a three-element base domain: number 8, position 3. -/
private theorem overflow_spec {U : ℕ} (ph pl nh nl : Fin U) :
    (ph.val ≠ 0 ∧ (code nh nl).val.testBit (code ph pl).val=true) ↔
    U≤3 ∧ ph.val=1 ∧ pl.val=0 ∧ nh.val=2 ∧ nl.val=2 := by
  by_cases h : 5≤U
  · have hb := squareFits h
    have ht : ¬U≤3 := by omega
    simp only [ht,false_and,iff_false,not_and]
    intro hp
    have hpos : U≤(code ph pl).val := by
      have hh := Nat.mul_le_mul_left U (show 1≤ph.val by omega)
      simp only [Nat.mul_one] at hh
      change U ≤ pl.val+U*ph.val; omega
    rw [Nat.testBit_lt_two_pow
      ((code nh nl).isLt.trans (hb.trans_le (Nat.pow_le_pow_right (by decide) hpos)))]
    decide
  · have hh : U≤4 := by omega
    clear h
    interval_cases U <;> revert ph pl nh nl <;> decide

/-- BIT(position, number) on two-digit arguments in base U. -/
noncomputable def pairBIT {k} (ph pl nh nl : Fin k) : Template k :=
  .disj (.conj (numeral 0 ph) (rankBit nh nl pl)) (overflowBit ph pl nh nl)

theorem pairBIT_correct {k U : ℕ} (ph pl nh nl : Fin k) (A : Matrix U) (e : Fin k → Fin U) :
    (pairBIT ph pl nh nl).eval A e=true ↔
      (code (e nh) (e nl)).val.testBit (code (e ph) (e pl)).val=true := by
  simp only [pairBIT,overflowBit,Tdisj_true,Tconj_true,numeral,fromFormula_eval,isNat_spec,
    rankBit_spec,small_spec,← overflow_spec]
  by_cases hz : (e ph).val=0
  · simp [finProdFinEquiv_apply_val,hz,code]
  · simp [hz]

/-- Replaces an input atom on the square domain by a formula over its four digits,
in the order row high, row low, column high, column low. -/
abbrev Input := {k : ℕ} → Fin k → Fin k → Fin k → Fin k → Template k

private def liftDigit {a k : ℕ} (z : Fin (k+2)) (σ : Fin a → Fin k) : Fin (a+1) → Fin (k+2) :=
  Fin.cases z (fun i => (σ i).succ.succ)

/-- Compile a source formula over the square universe into one ordinary
formula over the base universe. Each free variable has two target slots. -/
noncomputable def compile (input : Input) {a : ℕ} (p : Form a) :
    {k : ℕ} → (Fin a → Fin k) → (Fin a → Fin k) → Template k :=
  match p with
  | .eq x y => fun hi lo => .conj (.atom (.eqv (hi x) (hi y))) (.atom (.eqv (lo x) (lo y)))
  | .lt x y => fun hi lo => lex (hi x) (lo x) (hi y) (lo y)
  | .BIT i x => fun hi lo => pairBIT (hi i) (lo i) (hi x) (lo x)
  | .input x y => fun hi lo => input (hi x) (lo x) (hi y) (lo y)
  | .neg p => fun hi lo => .neg (compile @input p hi lo)
  | .conj p q => fun hi lo => .conj (compile @input p hi lo) (compile @input q hi lo)
  | .disj p q => fun hi lo => .disj (compile @input p hi lo) (compile @input q hi lo)
  | .ex p => fun hi lo => .ex (.ex (compile @input p (liftDigit 1 hi) (liftDigit 0 lo)))
  | .all p => fun hi lo => .neg (.ex (.ex (.neg (compile @input p (liftDigit 1 hi) (liftDigit 0 lo)))))
  | .many p => fun hi lo => pairMaj (compile @input p (liftDigit 1 hi) (liftDigit 0 lo))

private theorem neg_spec {k U : ℕ} (p : Template k) (A : Matrix U) (e : Fin k → Fin U) :
    p.neg.eval A e=true ↔ ¬ p.eval A e=true := by simp [Template.eval]

private theorem extend_spec {a k U : ℕ} (e : Fin k→Fin U) (hi lo : Fin a→Fin k) (r c : Fin U) :
    (fun i => code (extend c r e (liftDigit 1 hi i)) (extend c r e (liftDigit 0 lo i))) =
    Fin.cases (code r c) (fun i => code (e (hi i)) (e (lo i))) := by
  funext i; refine Fin.cases rfl (fun _ => rfl) i

private theorem ex_code {U : ℕ} (p : Fin (U*U)→Prop) :
    (∃ r c : Fin U, p (code r c)) ↔ ∃ i, p i := by
  constructor
  · exact fun ⟨r,c,h⟩ => ⟨_,h⟩
  · rintro ⟨i,hi⟩
    obtain ⟨⟨r,c⟩,rfl⟩ := finProdFinEquiv.surjective i
    exact ⟨r,c,hi⟩

theorem compile_correct (input : Input) {a k U : ℕ} (p : Form a) (hi lo : Fin a→Fin k)
    (A : Matrix U) (B : Matrix (U*U)) (e : Fin k→Fin U)
    (hInput : ∀ {m : ℕ} (rh rl ch cl : Fin m) (env : Fin m→Fin U),
      (input rh rl ch cl).eval A env = B (code (env rh) (env rl)) (code (env ch) (env cl))) :
    (compile @input p hi lo).eval A e=true ↔
      p.Holds B (fun i => code (e (hi i)) (e (lo i))) := by
  induction p generalizing k with
  | eq x y =>
    simp only [compile,Template.eval,Atom.eval,Bool.and_eq_true,decide_eq_true_eq,Form.Holds,code,
      EmbeddingLike.apply_eq_iff_eq,Prod.mk.injEq]
  | lt x y => exact lex_spec .. 
  | BIT x y => exact pairBIT_correct ..
  | input x y => exact (hInput _ _ _ _ _).symm ▸ Iff.rfl
  | neg p ih => rw [compile,neg_spec,ih,Form.Holds]
  | conj p q ih jh => rw [compile,Tconj_true,ih,jh,Form.Holds]
  | disj p q ih jh => rw [compile,Tdisj_true,ih,jh,Form.Holds]
  | ex p ih =>
    rw [compile,Tex_true]
    simp only [Tex_true,ih]
    change (∃ r c : Fin U, p.Holds B (fun i =>
      code (extend c r e (liftDigit 1 hi i)) (extend c r e (liftDigit 0 lo i)))) ↔ _
    simp only [extend_spec,Form.Holds]
    exact ex_code (fun j => p.Holds B (Fin.cases j (fun i => code (e (hi i)) (e (lo i)))))
  | all p ih =>
    rw [compile,neg_spec,Tex_true]
    simp only [Tex_true,neg_spec,ih]
    change (¬ ∃ r c : Fin U, ¬p.Holds B (fun i =>
      code (extend c r e (liftDigit 1 hi i)) (extend c r e (liftDigit 0 lo i)))) ↔ _
    simp only [extend_spec,Form.Holds,not_exists,not_not]
    constructor
    · intro h j
      obtain ⟨⟨r,c⟩,rfl⟩ := finProdFinEquiv.surjective j
      exact h r c
    · exact fun h r c => h (code r c)
  | many p ih =>
    rw [compile,pairMaj_correct,Form.Holds]
    have eq : (univ.filter (fun rc : Fin U × Fin U =>
        (compile @input p (liftDigit 1 hi) (liftDigit 0 lo)).eval A (extend rc.2 rc.1 e)=true)).card =
        (univ.filter (fun i : Fin (U*U) => p.Holds B (Fin.cases i
          (fun j => code (e (hi j)) (e (lo j)))))).card := by
      apply card_equiv finProdFinEquiv
      intro rc
      simp only [mem_filter,mem_univ,true_and,ih,extend_spec]
    rw [eq]; omega

/-- The square interpretation can be iterated on arithmetic templates by
first eliminating the bounded arithmetic atoms in the enlarged structure. -/
noncomputable def compileTemplate (input : Input) {a k : ℕ} (p : Template a)
    (hi lo : Fin a→Fin k) : Template k :=
  compile @input (toSource p) hi lo

theorem compileTemplate_correct (input : Input) {a k U : ℕ} (p : Template a)
    (hi lo : Fin a→Fin k) (A : Matrix U) (B : Matrix (U*U)) (e : Fin k→Fin U)
    (hInput : ∀ {m : ℕ} (rh rl ch cl : Fin m) (env : Fin m→Fin U),
      (input rh rl ch cl).eval A env = B (code (env rh) (env rl)) (code (env ch) (env cl))) :
    (compileTemplate @input p hi lo).eval A e =
      p.eval B (fun i => code (e (hi i)) (e (lo i))) := by
  apply Bool.eq_iff_iff.mpr
  exact (compile_correct @input (toSource p) hi lo A B e hInput).trans (toSource_correct p B _)

end DiophantineNP.HABPairInterpretation
