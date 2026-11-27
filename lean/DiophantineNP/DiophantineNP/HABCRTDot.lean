import DiophantineNP.HABBinaryResidue
import DiophantineNP.HABSpacePadding
import DiophantineNP.HABCRTShift
import DiophantineNP.HABCRTCoefficients
import DiophantineNP.HABIndependentSum
import DiophantineNP.HABMatrixBind
import Mathlib.Data.Nat.Bitwise

/-! # A uniform binary dot product for the corrected CRT comparison words

Rows and bit positions range over the interpretation domain. Products, row sums,
and the bias may overflow: a query at position j requires only bits through j.
-/
namespace DiophantineNP.HABCRTDot
open Counting WidthFormula PrimeFormula FiniteArithmeticGap

private def rename {n k : ℕ} (p : Template n) (f : Fin n → Fin k) :=
  rewriteMatrix (fun i j => .entry i j) p f

private theorem rename_eval {n k U : ℕ} (p : Template n) (f : Fin n → Fin k)
    (A : Fin U → Fin U → Bool) (e : Fin k → Fin U) :
    (rename p f).eval A e = p.eval A (e ∘ f) :=
  rewriteMatrix_eval _ A A (by intros; rfl) _ _ _

private def lane (n : ℕ) : Template 1 :=
  .ex (.conj (fromFormula (isNat n 0)) (.entry 0 1))

private theorem lane_eval {U : ℕ} (A : Fin U → Fin U → Bool) (n : ℕ) (hn : n<U)
    (j : Fin U) : (lane n).eval A (fun _ => j) = A ⟨n,hn⟩ j := by
  apply Bool.eq_iff_iff.mpr
  simp only [lane,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,Tentry_eval,Fin.cases_zero]
  exact ⟨fun ⟨r,h,bit⟩ => (show r=⟨n,hn⟩ from Fin.ext h) ▸ bit,
    fun bit => ⟨⟨n,hn⟩,rfl,bit⟩⟩

/-- Select one of two parameterized words. The row label is temporary and the
original table is available to both input queries. -/
private def pick {n : ℕ} (a b : Template (n+1)) : Template (n+2) :=
  let lift := Fin.cases 0 (fun i : Fin n => i.succ.succ)
  let zero := fromFormula (isNat 0 (1 : Fin (n+2)))
  .disj (.conj zero (rename a lift)) (.conj (.neg zero) (rename b lift))

private theorem pick_eval {n U : ℕ} (a b : Template (n+1)) (A : Fin U→Fin U→Bool)
    (e : Fin n→Fin U) (r c : Fin U) :
    (pick a b).eval A (extend c r e) =
      if r.val=0 then a.eval A (Fin.cases c e) else b.eval A (Fin.cases c e) := by
  have he : extend c r e ∘ Fin.cases 0 (fun i : Fin n => i.succ.succ) = Fin.cases c e := by
    funext j; refine Fin.cases rfl (fun _ => rfl) j
  have hz : (fromFormula (isNat 0 (1 : Fin (n+2)))).eval A (extend c r e) = decide (r.val=0) := by
    apply Bool.eq_iff_iff.mpr
    rw [fromFormula_eval,isNat_spec,decide_eq_true_eq]; rfl
  simp only [pick,Template.eval.eq_6,Template.eval.eq_5,Template.eval.eq_4,rename_eval,he,hz]
  by_cases h : r.val=0 <;> simp [h]

private noncomputable def binary {n : ℕ} (op : Template 1) (a b : Template (n+1)) :
    Template (n+1) :=
  HABMatrix.bind (pick a b) op Fin.succ (fun _ => 0)

private theorem binary_eval {n U : ℕ} (op : Template 1) (a b : Template (n+1))
    (A : Fin U→Fin U→Bool) (e : Fin n→Fin U) (j : Fin U) :
    (binary op a b).eval A (Fin.cases j e) =
      op.eval (fun r c => if r.val=0 then a.eval A (Fin.cases c e)
        else b.eval A (Fin.cases c e)) (fun _ => j) := by
  rw [binary,HABMatrix.bind_spec]
  simp only [pick_eval]; rfl

/-- Bit j of the product of two words at the same outer parameters. -/
noncomputable def rowMul {n : ℕ} (a b : Template (n+1)) : Template (n+1) :=
  binary (HABIndependentSum.multiply (lane 0) (lane 1)) a b

theorem rowMul_correct {n U x y : ℕ} (a b : Template (n+1))
    (A : Fin U→Fin U→Bool) (e : Fin n→Fin U) (hU : 2≤U)
    (ha : ∀ j : Fin U, a.eval A (Fin.cases j e) = x.testBit j.val)
    (hb : ∀ j : Fin U, b.eval A (Fin.cases j e) = y.testBit j.val) (j : Fin U) :
    (rowMul a b).eval A (Fin.cases j e) = (x*y).testBit j.val := by
  rw [rowMul,binary_eval]
  apply HABIndependentSum.multiply_correct
  · intro i; rw [lane_eval _ _ (by omega)]; exact ha i
  · intro i; rw [lane_eval _ _ (by omega)]; exact hb i

attribute [local irreducible] rowMul

private theorem prefix_sum (f : ℕ→ℕ) (n : ℕ) :
    Readout.prefixSum f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [Readout.prefixSum]
  | succ n ih => rw [Readout.prefixSum,Finset.sum_range_succ,ih]

/-- Rows may be arbitrary naturals; truncation to the available bits commutes
with summing modulo 2^U. -/
noncomputable def sumRows {n : ℕ} (cells : Template (n+2)) : Template (n+1) :=
  HABMatrix.bind cells HABIndependentSum.formula Fin.succ (fun _ => 0)

theorem sumRows_correct {n U : ℕ} (cells : Template (n+2)) (A : Fin U→Fin U→Bool)
    (e : Fin n→Fin U) (f : ℕ→ℕ)
    (h : ∀ r c : Fin U, cells.eval A (extend c r e) = (f r.val).testBit c.val) (j : Fin U) :
    (sumRows cells).eval A (Fin.cases j e) = (∑ i ∈ Finset.range U, f i).testBit j.val := by
  let g := fun i => f i % 2^U
  have hg (r c : Fin U) : cells.eval A (extend c r e) = (g r.val).testBit c.val := by
    simpa [g,Nat.testBit_mod_two_pow,c.isLt] using h r c
  rw [sumRows,HABMatrix.bind_spec]
  change HABIndependentSum.formula.eval (fun r c => cells.eval A (extend c r e)) (fun _=>j) = _
  simp_rw [hg]
  rw [HABIndependentSum.formula_correct g (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _)),prefix_sum]
  have all_eq (S : Finset ℕ) : ∑ i ∈ S, g i ≡ ∑ i ∈ S, f i [MOD 2^U] := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; rfl
    | insert i S hi ih =>
        simp only [Finset.sum_insert hi]
        exact (Nat.mod_modEq _ _).add ih
  have eq := all_eq (Finset.range U)
  simpa [Nat.testBit_mod_two_pow,j.isLt] using congrArg (fun t : ℕ => t.testBit j.val) eq

/-- Each input formula has free slots for the bit position, row, and ambient
parameters. Every row contributes the product of its two supplied words. -/
noncomputable def dot {n : ℕ} (a b : Template (n+2)) : Template (n+1) :=
  sumRows (rowMul a b)

theorem dot_correct {n U : ℕ} (a b : Template (n+2)) (A : Fin U→Fin U→Bool)
    (e : Fin n→Fin U) (hU : 2≤U) (f g : ℕ→ℕ)
    (ha : ∀ r c : Fin U, a.eval A (extend c r e) = (f r.val).testBit c.val)
    (hb : ∀ r c : Fin U, b.eval A (extend c r e) = (g r.val).testBit c.val) (j : Fin U) :
    (dot a b).eval A (Fin.cases j e) = (∑ i ∈ Finset.range U, f i*g i).testBit j.val := by
  have cells (r c : Fin U) : (rowMul (n:=n+1) a b).eval A (extend c r e) = (f r.val*g r.val).testBit c.val :=
    rowMul_correct (n:=n+1) (U:=U) (x:=f r.val) (y:=g r.val) a b A (Fin.cases r e) hU (ha r) (hb r) c
  unfold dot
  exact sumRows_correct (rowMul a b) A e (fun i => f i*g i) cells j

/-- Bit j of the sum of two parameterized words, with the incoming carry from
all lower positions and with no bound on the mathematical values. -/
noncomputable def rowAdd {n : ℕ} (a b : Template (n+1)) : Template (n+1) :=
  binary (addWords (lane 0) (lane 1)) a b

theorem rowAdd_correct {n U x y : ℕ} (a b : Template (n+1))
    (A : Fin U→Fin U→Bool) (e : Fin n→Fin U) (hU : 2≤U)
    (ha : ∀ j : Fin U, a.eval A (Fin.cases j e) = x.testBit j.val)
    (hb : ∀ j : Fin U, b.eval A (Fin.cases j e) = y.testBit j.val) (j : Fin U) :
    (rowAdd a b).eval A (Fin.cases j e) = (x+y).testBit j.val := by
  rw [rowAdd,binary_eval]
  apply addWords_correct
  · intro i; rw [lane_eval _ _ (by omega)]; exact ha i
  · intro i; rw [lane_eval _ _ (by omega)]; exact hb i

attribute [local irreducible] rowAdd sumRows

private def different {k : ℕ} (a b : Template k) : Template k :=
  .disj (.conj a (.neg b)) (.conj (.neg a) b)

private theorem different_eval {k U : ℕ} (a b : Template k)
    (A : Fin U→Fin U→Bool) (e : Fin k→Fin U) :
    (different a b).eval A e = true ↔ a.eval A e ≠ b.eval A e := by
  cases h : a.eval A e <;> cases h' : b.eval A e <;> simp [different,Template.eval,h,h']

private theorem neg_iff {k U : ℕ} (a : Template k)
    (A : Fin U→Fin U→Bool) (e : Fin k→Fin U) :
    a.neg.eval A e = true ↔ ¬ a.eval A e = true := by simp [Template.eval]

private def higher {n : ℕ} (p : Template (n+1)) : Template (n+2) :=
  rename p (Fin.cases 0 (fun i : Fin n => i.succ.succ))

private theorem higher_eval {n U : ℕ} (p : Template (n+1)) (A : Fin U→Fin U→Bool)
    (e : Fin n→Fin U) (i j : Fin U) :
    (higher p).eval A (extend j i e) = p.eval A (Fin.cases j e) := by
  rw [higher,rename_eval]
  congr 1
  funext a; refine Fin.cases rfl (fun _ => rfl) a

/-- Lexicographic binary comparison, selecting the last differing bit. -/
def wordLt {n : ℕ} (a b : Template (n+1)) : Template n :=
  .ex (.conj (.neg a) (.conj b (.neg (.ex (.conj (fromFormula (ltF 1 0))
    (different (higher a) (higher b)))))))

private theorem finite_lt {x y U : ℕ} (hx : x<2^U) (hy : y<2^U) :
    (∃ i : Fin U, x.testBit i.val=false ∧ y.testBit i.val=true ∧
      ∀ t : Fin U, i.val<t.val → x.testBit t.val=y.testBit t.val) ↔ x<y := by
  have above (j : ℕ) (hj : U≤j) : x.testBit j=false ∧ y.testBit j=false := by
    have pow := Nat.pow_le_pow_right (by decide : 0<2) hj
    exact ⟨Nat.testBit_lt_two_pow (hx.trans_le pow), Nat.testBit_lt_two_pow (hy.trans_le pow)⟩
  constructor
  · rintro ⟨i,hx',hy',eq⟩
    apply Nat.lt_of_testBit i.val hx' hy'
    intro t ht
    by_cases h : t<U
    · exact eq ⟨t,h⟩ ht
    · exact (above t (by omega)).1.trans (above t (by omega)).2.symm
  · intro h
    obtain ⟨i,hi,rest⟩ := Nat.exists_most_significant_bit (Nat.xor_ne_zero.mpr h.ne)
    have diff : x.testBit i ≠ y.testBit i := by
      intro he; simp [Nat.testBit_xor,he] at hi
    have eq (t : ℕ) (ht : i<t) : x.testBit t=y.testBit t := by
      have hh := rest t ht
      simpa [Nat.testBit_xor] using hh
    have bound : i<U := by
      by_contra! h'
      exact diff ((above i h').1.trans (above i h').2.symm)
    refine ⟨⟨i,bound⟩,?_,?_,fun t ht => eq _ ht⟩
    · cases he : x.testBit i with
      | false => rfl
      | true =>
        have he' : y.testBit i=false := by cases hy' : y.testBit i <;> simp_all
        exact (h.asymm (Nat.lt_of_testBit i he' he (fun t ht => (eq t ht).symm))).elim
    · cases he : y.testBit i with
      | true => rfl
      | false =>
        have he' : x.testBit i=true := by cases hx' : x.testBit i <;> simp_all
        exact (h.asymm (Nat.lt_of_testBit i he he' (fun t ht => (eq t ht).symm))).elim

theorem wordLt_correct {n U x y : ℕ} (a b : Template (n+1))
    (A : Fin U→Fin U→Bool) (e : Fin n→Fin U)
    (ha : ∀ j : Fin U, a.eval A (Fin.cases j e) = x.testBit j.val)
    (hb : ∀ j : Fin U, b.eval A (Fin.cases j e) = y.testBit j.val)
    (hx : x<2^U) (hy : y<2^U) :
    (wordLt a b).eval A e = true ↔ x<y := by
  rw [←finite_lt hx hy]
  simp only [wordLt,Tex_true,Tconj_true,neg_iff,fromFormula_eval,ltF_true,
    different_eval,Fin.cases_zero,ha,hb]
  simp only [higher_eval,ha,hb,Bool.not_eq_true,not_exists,not_and,not_not]
  rfl

/-- The first argument selects rows; the second supplies bits at (column,row).
The syntax returns zero on every row outside the selected basis. -/
private def masked {n : ℕ} (active : Template (n+1)) (cells : Template (n+2)) : Template (n+2) :=
  .conj (rename active Fin.succ) cells

private theorem maskedSum {n U : ℕ} (active : Template (n+1)) (cells : Template (n+2))
    (A : Fin U→Fin U→Bool) (e : Fin n→Fin U) (s : Finset ℕ) (f : ℕ→ℕ)
    (fit : ∀ p ∈ s, p<U)
    (sel : ∀ r : Fin U, active.eval A (Fin.cases r e) = true ↔ r.val ∈ s)
    (bit : ∀ r c : Fin U, r.val ∈ s → cells.eval A (extend c r e) = (f r.val).testBit c.val)
    (j : Fin U) :
    (sumRows (masked active cells)).eval A (Fin.cases j e) = (∑ i ∈ s, f i).testBit j.val := by
  let g := fun i => if i ∈ s then f i else 0
  have hb (r c : Fin U) : (masked active cells).eval A (extend c r e) = (g r.val).testBit c.val := by
    apply Bool.eq_iff_iff.mpr
    rw [masked,Tconj_true,rename_eval]
    change (active.eval A (Fin.cases r e)=true ∧ _) ↔ _
    rw [sel]
    by_cases h : r.val ∈ s
    · simp [g,h,bit _ _ h]
    · simp [g,h]
  rw [sumRows_correct _ A e g hb j]
  have hf : (Finset.range U).filter (· ∈ s) = s := by
    ext i; simp only [Finset.mem_filter,Finset.mem_range]; exact ⟨And.right,fun h=>⟨fit _ h,h⟩⟩
  rw [←hf] at ⊢
  congr 1
  rw [Finset.sum_filter]

/-- Bit predicate for HAB's corrected, dyadically truncated reciprocal sum.
`keep` selects bit positions below the chosen precision, `active` selects
the prime rows, and the remaining two arguments supply coefficient and
reciprocal bits. The bias is computed directly from the active prime indices. -/
noncomputable def crtWord {n : ℕ} (keep active : Template (n+1))
    (coefficient reciprocal : Template (n+2)) : Template (n+1) :=
  .conj keep (rowAdd (sumRows (masked active (rowMul coefficient reciprocal)))
    (sumRows (masked active (.bit 1 0))))

theorem crtWord_correct {n U L : ℕ} (keep active : Template (n+1))
    (coefficient reciprocal : Template (n+2)) (A : Fin U→Fin U→Bool)
    (e : Fin n→Fin U) (s : Finset ℕ) (f : ℕ→ℕ) (hU : 2≤U)
    (fit : ∀ p ∈ s, p<U)
    (cut : ∀ j : Fin U, keep.eval A (Fin.cases j e) = decide (j.val<L))
    (sel : ∀ r : Fin U, active.eval A (Fin.cases r e) = true ↔ r.val ∈ s)
    (cf : ∀ r c : Fin U, r.val ∈ s → coefficient.eval A (extend c r e) = (f r.val).testBit c.val)
    (rc : ∀ r c : Fin U, r.val ∈ s → reciprocal.eval A (extend c r e) = (2^L/r.val).testBit c.val)
    (j : Fin U) :
    (crtWord keep active coefficient reciprocal).eval A (Fin.cases j e) =
      (HABCRTRecovery.word s (2^L) (HABCRTRecovery.budget s) f).testBit j.val := by
  have prod (r c : Fin U) (hr : r.val ∈ s) :
      (rowMul coefficient reciprocal).eval A (extend c r e) = (f r.val*(2^L/r.val)).testBit c.val :=
    rowMul_correct (n:=n+1) (x:=f r.val) (y:=2^L/r.val) coefficient reciprocal A (Fin.cases r e)
      hU (fun i=>cf r i hr) (fun i=>rc r i hr) c
  have left := maskedSum active (rowMul coefficient reciprocal) A e s (fun p => f p*(2^L/p)) fit sel prod
  have right := maskedSum active (.bit 1 0) A e s id fit sel (fun _ _ _ => rfl)
  have hsum := rowAdd_correct (x:=HABCRTRecovery.approx s (2^L) f) (y:=HABCRTRecovery.budget s)
    _ _ A e hU left right j
  rw [crtWord,Template.eval.eq_5,cut,hsum,HABCRTRecovery.word,Nat.testBit_mod_two_pow]

/-- Strict comparison of two CRT inputs assembled from their coefficient bits,
a shared reciprocal table, and the basis selector. -/
noncomputable def crtLt {n : ℕ} (keep active : Template (n+1))
    (a b reciprocal : Template (n+2)) : Template n :=
  wordLt (crtWord keep active a reciprocal) (crtWord keep active b reciprocal)

theorem crtLt_correct {n U L x y : ℕ} (keep active : Template (n+1))
    (a b reciprocal : Template (n+2)) (A : Fin U→Fin U→Bool)
    (e : Fin n→Fin U) (s : Finset ℕ) (inv : ℕ→ℕ) (hU : 2≤U)
    (fit : ∀ p ∈ s, p<U) (precision_fits : L≤U)
    (primes : ∀ p ∈ s, Nat.Prime p)
    (hinv : ∀ p ∈ s, HABCRTRecovery.cofactor s p * inv p ≡ 1 [MOD p])
    (hx : x < HABCRTRecovery.modulus s) (hy : y < HABCRTRecovery.modulus s)
    (precise : HABCRTRecovery.modulus s * HABCRTRecovery.budget s < 2^L)
    (cut : ∀ j : Fin U, keep.eval A (Fin.cases j e) = decide (j.val<L))
    (sel : ∀ r : Fin U, active.eval A (Fin.cases r e) = true ↔ r.val ∈ s)
    (ha : ∀ r c : Fin U, r.val ∈ s → a.eval A (extend c r e) =
      (HABCRTRecovery.coeff inv x r.val).testBit c.val)
    (hb : ∀ r c : Fin U, r.val ∈ s → b.eval A (extend c r e) =
      (HABCRTRecovery.coeff inv y r.val).testBit c.val)
    (rc : ∀ r c : Fin U, r.val ∈ s → reciprocal.eval A (extend c r e) = (2^L/r.val).testBit c.val) :
    (crtLt keep active a b reciprocal).eval A e = true ↔ x<y := by
  let w := fun z => HABCRTRecovery.word s (2^L) (HABCRTRecovery.budget s) (HABCRTRecovery.coeff inv z)
  have cap (z : ℕ) : w z<2^U := (Nat.mod_lt _ (Nat.two_pow_pos L)).trans_le
    (Nat.pow_le_pow_right (by decide) precision_fits)
  have left := crtWord_correct keep active a reciprocal A e s (HABCRTRecovery.coeff inv x) hU fit cut sel ha rc
  have right := crtWord_correct keep active b reciprocal A e s (HABCRTRecovery.coeff inv y) hU fit cut sel hb rc
  exact (wordLt_correct (x:=w x) (y:=w y) _ _ A e left right (cap x) (cap y)).trans
    (HABCRTRecovery.compare_crt primes hinv hx hy precise).symm

/-- A graph of short field values is converted into little-endian bit queries.
The value and row are slots 0 and 1 in the graph. -/
def graphBits {n : ℕ} (graph : Template (n+2)) : Template (n+2) :=
  .ex (.conj (rename graph (Fin.cases 0 (fun i => i.succ.succ))) (.bit 0 1))

theorem graphBits_correct {n U z : ℕ} (graph : Template (n+2)) (A : Fin U→Fin U→Bool)
    (e : Fin n→Fin U) (p c : Fin U) (hz : z<U)
    (hg : ∀ v : Fin U, graph.eval A (extend v p e)=true ↔ v.val=z) :
    (graphBits graph).eval A (extend c p e) = z.testBit c.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphBits,Tex_true,Tconj_true,rename_eval]
  have eq (v : Fin U) : Fin.cases v (extend c p e) ∘ Fin.cases 0 (fun i : Fin (n+1) => i.succ.succ) =
      extend v p e := by
    funext i; refine Fin.cases rfl (fun _ => rfl) i
  simp only [eq,hg]
  change (∃ v : Fin U, v.val=z ∧ v.val.testBit c.val=true) ↔ _
  exact ⟨fun ⟨_,eqv,h⟩ => eqv ▸ h,fun h => ⟨⟨z,hz⟩,rfl,h⟩⟩

private def primePower {k : ℕ} (s p v : Fin k) : Template k :=
  (HABBinaryResidue.powerAtPosition 1 2).syntaxF (fun i => if i=1 then s else if i=2 then v else p)

private theorem primePower_correct {k U K : ℕ} (s p v : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U)
    (prime : (e p).val.Prime) (hK : 2≤K) (hpK : (e p).val≤2^K) (cap : 2^((K+1)*K)<U) :
    (primePower s p v).eval A e=true ↔ (e v).val=2^(e s).val % (e p).val := by
  let T (r j : ℕ) := if h : r<U ∧ j<U then A ⟨r,h.1⟩ ⟨j,h.2⟩ else false
  have tab : A=fun r j => T r.val j.val := by funext r j; simp [T,r.isLt,j.isLt]
  rw [tab,primePower,ShortResidue.Predicate.valid _ _ T]
  exact HABBinaryResidue.powerAtPosition_spec T _ _ _ (by decide) (by decide) rfl prime
    (e p).isLt (e s).isLt (e v).isLt hK hpK cap

private def oddValue {k : ℕ} (x : Fin k) : Template k :=
  .ex (.conj (fromFormula (isNat 0 0)) (.bit x.succ 0))

private theorem oddValue_correct {k U : ℕ} (x : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U) :
    (oddValue x).eval A e=true ↔ (e x).val%2=1 := by
  simp only [oddValue,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,Fin.cases_zero]
  change (∃ o : Fin U, o.val=0 ∧ (e x).val.testBit o.val=true) ↔ _
  have h : (e x).val.testBit 0=true ↔ (e x).val%2=1 := by simp [Nat.testBit_zero]
  exact ⟨fun ⟨_,ho,hb⟩ => h.mp (ho ▸ hb), fun hb => ⟨⟨0,(e x).pos⟩,rfl,h.mpr hb⟩⟩

private def nextAt {k : ℕ} (j l : Fin k) : Template k :=
  .ex (.conj (fromFormula (isNat 1 0)) (.atom (.add j.succ 0 l.succ)))

private theorem nextAt_correct {k U : ℕ} (j l : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U) :
    (nextAt j l).eval A e=true ↔ (e j).val+1=(e l).val := by
  simp only [nextAt,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,Fin.cases_zero]
  change (∃ v : Fin U, v.val=1 ∧ decide ((e j).val+v.val=(e l).val)=true) ↔ _
  simp only [decide_eq_true_eq]
  exact ⟨fun ⟨_,h1,h⟩ => h1 ▸ h,
    fun h => ⟨⟨1,by have := (e l).isLt; omega⟩,rfl,h⟩⟩

private def oddReciprocalWith (power : {a : ℕ} → Fin a → Fin a → Fin a → Template a) {k : ℕ} (l j p : Fin k) : Template k :=
  .conj (fromFormula (ltF j l)) (.ex (.conj (.atom (.add j.succ 0 l.succ))
    (.ex (.conj (power 1 p.succ.succ 0) (oddValue 0)))))

private theorem oddReciprocalWith_correct (power : {a : ℕ} → Fin a → Fin a → Fin a → Template a) {k U : ℕ} (l j p : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U)
    (prime : (e p).val.Prime) (odd : (e p).val%2=1) (powerOK : ∀ {a : ℕ} (d p' v : Fin a) (E : Fin a→Fin U), (E p').val=(e p).val →
      ((power d p' v).eval A E=true ↔ (E v).val=2^(E d).val%(e p).val)) :
    (oddReciprocalWith @power l j p).eval A e = (2^(e l).val/(e p).val).testBit (e j).val := by
  apply Bool.eq_iff_iff.mpr
  rw [HABCRTRecovery.scaled_reciprocal_bit prime.one_lt]
  have hpw (d v : Fin U) : (power 1 p.succ.succ 0).eval A (extend v d e)=true ↔
      v.val=2^d.val%(e p).val :=
    powerOK 1 p.succ.succ 0 (extend v d e) rfl
  simp only [oddReciprocalWith,Tconj_true,fromFormula_eval,ltF_true,Tex_true,oddValue_correct,Fin.cases_zero]
  change ((e j).val<(e l).val ∧ ∃ d : Fin U, decide ((e j).val+d.val=(e l).val)=true ∧
    ∃ v : Fin U, (power 1 p.succ.succ 0).eval A (extend v d e)=true ∧ v.val%2=1) ↔ _
  simp only [hpw,decide_eq_true_eq]
  constructor
  · rintro ⟨h,d,hd,v,hv,ho⟩
    obtain ed : d.val=(e l).val-(e j).val := by omega
    refine ⟨h,?_⟩
    rw [HABCRTRecovery.reciprocal_parity odd (Nat.sub_pos_of_lt h),←ed,←hv]; exact ho
  · rintro ⟨h,hb⟩
    let d : Fin U := ⟨(e l).val-(e j).val,(Nat.sub_le ..).trans_lt (e l).isLt⟩
    let v : Fin U := ⟨2^d.val%(e p).val,(Nat.mod_lt _ prime.pos).trans (e p).isLt⟩
    rw [HABCRTRecovery.reciprocal_parity odd (Nat.sub_pos_of_lt h)] at hb
    exact ⟨h,d,by dsimp [d]; omega,v,rfl,hb⟩

/-- Dyadic reciprocal digits using any formula for powers of two modulo the row prime. -/
def reciprocalCellsWith (power : {a : ℕ} → Fin a → Fin a → Fin a → Template a) {n : ℕ} (L : Fin n) : Template (n+2) :=
  let two := fromFormula (isNat 2 (1 : Fin (n+2)))
  .disj (.conj two (nextAt 0 L.succ.succ))
    (.conj (.neg two) (oddReciprocalWith @power L.succ.succ 0 1))

theorem reciprocalCellsWith_correct (power : {a : ℕ} → Fin a → Fin a → Fin a → Template a) {n U : ℕ} (L : Fin n) (A : HAB.Matrix U) (e : Fin n→Fin U)
    (p c : Fin U) (prime : p.val.Prime) (powerOK : ∀ {a : ℕ} (d p' v : Fin a) (E : Fin a→Fin U), (E p').val=p.val →
      ((power d p' v).eval A E=true ↔ (E v).val=2^(E d).val%p.val)) :
    (reciprocalCellsWith @power L).eval A (extend c p e) = (2^(e L).val/p.val).testBit c.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [reciprocalCellsWith,Tdisj_true,Tconj_true,neg_iff,fromFormula_eval,isNat_spec,nextAt_correct]
  change (p.val=2 ∧ c.val+1=(e L).val ∨ p.val≠2 ∧ _) ↔ _
  by_cases ht : p.val=2
  · simp only [ht,true_and,ne_self_iff_false,false_and,or_false]
    cases hL : (e L).val with
    | zero => simp
    | succ t => simp [Nat.pow_succ,Nat.testBit_two_pow,eq_comm]
  · have H := oddReciprocalWith_correct @power L.succ.succ 0 1 A (extend c p e) prime
        (Nat.odd_iff.mp (prime.odd_of_ne_two ht)) powerOK
    simp only [ht,false_and,false_or,and_iff_right ht,H]
    rfl

/-- Reciprocal digits with the packed short-prime implementation of powering. -/
def reciprocalCells {n : ℕ} (L : Fin n) : Template (n+2) := reciprocalCellsWith @primePower L

theorem reciprocalCells_correct {n U K : ℕ} (L : Fin n) (A : HAB.Matrix U) (e : Fin n→Fin U)
    (p c : Fin U) (prime : p.val.Prime) (hK : 2≤K) (hpK : p.val≤2^K)
    (cap : 2^((K+1)*K)<U) :
    (reciprocalCells L).eval A (extend c p e) = (2^(e L).val/p.val).testBit c.val := by
  apply reciprocalCellsWith_correct @primePower L A e p c prime
  intro a d r v E hr
  rw [←hr]
  exact primePower_correct _ _ _ A E (hr ▸ prime) hK (hr ▸ hpK) cap

/-- Positions below L, where slot zero is the current bit query. -/
def cutoff {n : ℕ} (L : Fin n) : Template (n+1) := fromFormula (ltF 0 L.succ)

theorem cutoff_correct {n U : ℕ} (L : Fin n) (A : HAB.Matrix U) (e : Fin n→Fin U) (c : Fin U) :
    (cutoff L).eval A (Fin.cases c e) = decide (c.val<(e L).val) := by
  apply Bool.eq_iff_iff.mpr
  rw [cutoff,fromFormula_eval,ltF_true,decide_eq_true_eq]; rfl

/-- Short-prime CRT comparison with endogenous reciprocal and bias. The caller
supplies the selected prime rows and the bits of the two short coefficients. -/
noncomputable def primeLt {n : ℕ} (L : Fin n) (active : Template (n+1)) (a b : Template (n+2)) :=
  crtLt (cutoff L) active a b (reciprocalCells L)

theorem primeLt_correct {n U K x y : ℕ} (L : Fin n) (active : Template (n+1))
    (a b : Template (n+2)) (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ)
    (inv : ℕ→ℕ) (primes : ∀ p ∈ s, Nat.Prime p) (small : ∀ p ∈ s, p ≤ 2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U)
    (hinv : ∀ p ∈ s, HABCRTRecovery.cofactor s p * inv p ≡ 1 [MOD p])
    (hx : x < HABCRTRecovery.modulus s) (hy : y < HABCRTRecovery.modulus s)
    (precise : HABCRTRecovery.modulus s * HABCRTRecovery.budget s < 2^(e L).val)
    (sel : ∀ r : Fin U, active.eval A (Fin.cases r e) = true ↔ r.val ∈ s)
    (ha : ∀ r c : Fin U, r.val ∈ s → a.eval A (extend c r e) = (HABCRTRecovery.coeff inv x r.val).testBit c.val)
    (hb : ∀ r c : Fin U, r.val ∈ s → b.eval A (extend c r e) = (HABCRTRecovery.coeff inv y r.val).testBit c.val) :
    (primeLt L active a b).eval A e = true ↔ x<y := by
  have hle : 2^K ≤ 2^((K+1)*K) := Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ (by omega))
  have fit (p : ℕ) (hp : p ∈ s) : p<U := ((small p hp).trans hle).trans_lt cap
  exact crtLt_correct _ _ _ _ _ A e s inv (by have := Nat.one_lt_two_pow (by omega : K≠0); omega)
    fit (e L).isLt.le primes hinv hx hy precise (cutoff_correct L A e) sel ha hb
    (fun p c h => reciprocalCells_correct L A e p c (primes _ h) hK (small _ h) cap)

/-- Translate a query at j to a query at L+j. Queries past the domain
have value false; the pointwise specification below makes the capacity explicit. -/
def highBits {n : ℕ} (L : Fin n) (w : Template (n+1)) : Template (n+1) :=
  .ex (.conj (.atom (.add L.succ.succ 1 0)) (higher w))

theorem highBits_correct {n U x : ℕ} (L : Fin n) (w : Template (n+1))
    (A : HAB.Matrix U) (e : Fin n→Fin U)
    (hw : ∀ t : Fin U, w.eval A (Fin.cases t e)=x.testBit t.val) (j : Fin U)
    (fit : (e L).val+j.val<U ∨ x<2^U) :
    (highBits L w).eval A (Fin.cases j e) = (x/2^(e L).val).testBit j.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [highBits,Tex_true,Tconj_true,higher_eval,hw,Nat.testBit_div_two_pow]
  change (∃ t : Fin U, decide ((e L).val+j.val=t.val)=true ∧ x.testBit t.val=true) ↔ _
  simp only [decide_eq_true_eq]
  rw [Nat.add_comm j.val]
  constructor
  · rintro ⟨t,he,h⟩; simpa only [he] using h
  · intro h
    have hj : (e L).val+j.val<U := by
      rcases fit with h|h
      · exact h
      · by_contra! far
        rw [Nat.testBit_lt_two_pow (h.trans_le (Nat.pow_le_pow_right (by decide) far))] at *
        contradiction
    exact ⟨⟨_,hj⟩,rfl,h⟩

/-- Recover a binary digit directly from CRT data when the basis modulus
has a definable binary word. The long word for the target is never supplied. -/
noncomputable def readout {n : ℕ} (L : Fin n) (active modulusBits : Template (n+1))
    (coefficient : Template (n+2)) : Template (n+1) :=
  highBits L (rowMul (crtWord (cutoff L) active coefficient (reciprocalCells L)) modulusBits)

theorem readout_correct {n U K x : ℕ} (L : Fin n) (active modulusBits : Template (n+1))
    (a : Template (n+2)) (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ) (inv : ℕ→ℕ)
    (primes : ∀ p ∈ s, Nat.Prime p) (small : ∀ p ∈ s, p ≤ 2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U)
    (hinv : ∀ p ∈ s, HABCRTRecovery.cofactor s p * inv p ≡ 1 [MOD p])
    (hx : x < HABCRTRecovery.modulus s)
    (precise : HABCRTRecovery.modulus s * HABCRTRecovery.budget s < 2^(e L).val)
    (sel : ∀ r : Fin U, active.eval A (Fin.cases r e) = true ↔ r.val ∈ s)
    (ha : ∀ r c : Fin U, r.val ∈ s → a.eval A (extend c r e) = (HABCRTRecovery.coeff inv x r.val).testBit c.val)
    (hm : ∀ j : Fin U, modulusBits.eval A (Fin.cases j e) = (HABCRTRecovery.modulus s).testBit j.val)
    (j : Fin U) (fit : (e L).val+j.val<U ∨ HABCRTRecovery.modulus s ≤ 2^(U-(e L).val)) :
    (readout L active modulusBits a).eval A (Fin.cases j e) = x.testBit j.val := by
  let w := HABCRTRecovery.word s (2^(e L).val) (HABCRTRecovery.budget s) (HABCRTRecovery.coeff inv x)
  let M := HABCRTRecovery.modulus s
  have hle : 2^K ≤ 2^((K+1)*K) := Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ (by omega))
  have dom (p : ℕ) (hp : p ∈ s) : p<U := ((small p hp).trans hle).trans_lt cap
  have hU : 2≤U := by have := Nat.one_lt_two_pow (by omega : K≠0); omega
  have known := crtWord_correct (cutoff L) active a (reciprocalCells L) A e s
    (HABCRTRecovery.coeff inv x) hU dom (cutoff_correct L A e) sel ha
    (fun p c h => reciprocalCells_correct L A e p c (primes _ h) hK (small _ h) cap)
  have product := rowMul_correct (x:=w) (y:=M) _ _ A e hU known hm
  have space : (e L).val+j.val<U ∨ w*M<2^U := by
    rcases fit with hf|hf
    · exact Or.inl hf
    · refine Or.inr ?_
      have hw : w<2^(e L).val := Nat.mod_lt _ (Nat.two_pow_pos _)
      have lm := (e L).isLt
      calc w*M ≤ w*2^(U-(e L).val) := Nat.mul_le_mul_left _ hf
           _ < 2^(e L).val*2^(U-(e L).val) := Nat.mul_lt_mul_of_pos_right hw (Nat.two_pow_pos _)
           _ = 2^U := by rw [←pow_add]; congr 1; omega
  exact (highBits_correct L _ A e product j space).trans (congrArg (fun v : ℕ => v.testBit j.val)
    (HABCRTRecovery.crt_readout primes hinv hx precise))

/-- A single control bit from the order comparison corrects the estimate's
parity in the final HAB shift. -/
def correctedParity {n : ℕ} (overshoot parity : Template n) : Template n :=
  different overshoot parity

theorem correctedParity_correct {n U x : ℕ} (overshoot parity : Template n) (A : HAB.Matrix U)
    (e : Fin n→Fin U) (bs : List ℕ) (large : ∀ a∈bs, x<a) (odd : ∀ a∈bs, a%2=1)
    (cmp : overshoot.eval A e=true ↔ x < HABCRTShift.estimate x bs * 2^bs.length)
    (par : parity.eval A e = (HABCRTShift.estimate x bs).testBit 0) :
    (correctedParity overshoot parity).eval A e = x.testBit bs.length := by
  rw [←HABCRTShift.bit_spec large odd]
  apply Bool.eq_iff_iff.mpr
  rw [correctedParity,different_eval,par]
  let q := HABCRTShift.estimate x bs
  change overshoot.eval A e ≠ q.testBit 0 ↔ (if q*2^bs.length≤x then q else q-1).testBit 0=true
  by_cases he : q*2^bs.length≤x
  · have ho : overshoot.eval A e=false := by
      cases eq : overshoot.eval A e with
      | false => rfl
      | true => exact (he.not_gt (cmp.mp eq)).elim
    rw [if_pos he,ho]; cases q.testBit 0 <;> decide
  · have ho : overshoot.eval A e=true := cmp.mpr (Nat.lt_of_not_ge he)
    have hq : q≠0 := by intro hz; simp [hz] at he
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hq
    rw [if_neg he,ho,hm,Nat.succ_sub_one]
    simp only [Nat.testBit_zero,ne_eq,Bool.true_eq,decide_eq_true_eq]
    omega

open HABPairInterpretation

/-- The parameterized dot product evaluated over pairs of base-domain indices.
Both the number of rows and the accessible bit width are U². The compiler can
be applied again for a larger fixed polynomial bound. -/
noncomputable def pairDot (input : Input) {n k : ℕ} (a b : Template (n+2))
    (hi lo : Fin (n+1)→Fin k) : Template k := compileTemplate @input (dot a b) hi lo

theorem pairDot_correct (input : Input) {n k U : ℕ} (a b : Template (n+2))
    (hi lo : Fin (n+1)→Fin k) (A : HAB.Matrix U) (B : HAB.Matrix (U*U)) (e : Fin k→Fin U)
    (hinput : ∀ {m : ℕ} (rh rl ch cl : Fin m) (env : Fin m→Fin U),
      (input rh rl ch cl).eval A env = B (code (env rh) (env rl)) (code (env ch) (env cl)))
    (hU : 2≤U*U) (f g : ℕ→ℕ)
    (ha : ∀ r c : Fin (U*U), a.eval B (extend c r (fun i => code (e (hi i.succ)) (e (lo i.succ)))) =
      (f r.val).testBit c.val)
    (hb : ∀ r c : Fin (U*U), b.eval B (extend c r (fun i => code (e (hi i.succ)) (e (lo i.succ)))) =
      (g r.val).testBit c.val) :
    (pairDot @input a b hi lo).eval A e =
      (∑ i ∈ Finset.range (U*U), f i*g i).testBit (code (e (hi 0)) (e (lo 0))).val := by
  rw [pairDot,compileTemplate_correct @input _ _ _ A B e hinput]
  let E := fun i : Fin n => code (e (hi i.succ)) (e (lo i.succ))
  let j := code (e (hi 0)) (e (lo 0))
  have ctx : (fun i => code (e (hi i)) (e (lo i))) = Fin.cases j E := by
    funext i; refine Fin.cases rfl (fun _ => rfl) i
  rw [ctx]
  exact dot_correct a b B E hU f g ha hb j

/-- Number of base slots for a free environment of a variables, with 2^d
base digits for each variable. A zero major digit is not required. -/
def tupleArity : ℕ → ℕ → ℕ
  | 0,a => a
  | d+1,a => tupleArity d (a+a)

theorem tupleArity_eq (d a : ℕ) : tupleArity d a = a*2^d := by
  induction d generalizing a with
  | zero => simp [tupleArity]
  | succ d ih => rw [tupleArity,ih,pow_succ]; ring

/-- Interpret every tuple as the corresponding index of the power-size universe. -/
def decode {U : ℕ} : (d : ℕ) → {a : ℕ} → (Fin (tupleArity d a)→Fin U) →
    Fin a→Fin (HABSpacePadding.size U d)
  | 0,_,env => env
  | d+1,a,env =>
    let E := decode d (a:=a+a) env
    fun i => code (E (i.castAdd a)) (E (Fin.natAdd a i))

theorem decode_surjective {U : ℕ} (d a : ℕ) :
    Function.Surjective (decode (U:=U) d (a:=a)) := by
  induction d generalizing a with
  | zero => exact fun e => ⟨e,rfl⟩
  | succ d ih =>
    intro e
    let hi := fun i : Fin a => (finProdFinEquiv.symm (e i)).1
    let lo := fun i : Fin a => (finProdFinEquiv.symm (e i)).2
    obtain ⟨env,henv⟩ := ih (a+a) (Fin.addCases hi lo)
    refine ⟨env,?_⟩
    funext i
    simp only [decode,henv,Fin.addCases_left,Fin.addCases_right,hi,lo,code,Prod.mk.eta,
      Equiv.apply_symm_apply]

/-- Iterate the square interpreter, retaining independent base tuple digits for
every free variable. Each fixed depth gives a single finite formula. -/
noncomputable def tuples (input : Input) :
    (d : ℕ) → {a : ℕ} → Template a → Template (tupleArity d a)
  | 0,_,p => p
  | d+1,a,p => tuples @input d (compileTemplate @input p (Fin.castAdd a) (Fin.natAdd a))

theorem tuples_correct (input : Input) {U : ℕ} (B : (d : ℕ)→HAB.Matrix (HABSpacePadding.size U d))
    (hinput : ∀ d {m : ℕ} (rh rl ch cl : Fin m) (env : Fin m→Fin (HABSpacePadding.size U d)),
      (input rh rl ch cl).eval (B d) env = B (d+1) (code (env rh) (env rl)) (code (env ch) (env cl)))
    (d : ℕ) {a : ℕ} (p : Template a) (e : Fin (tupleArity d a)→Fin U) :
    (tuples @input d p).eval (B 0) e = p.eval (B d) (decode d e) := by
  induction d generalizing a with
  | zero => rfl
  | succ d ih =>
    rw [tuples,ih,compileTemplate_correct @input _ _ _ (B d) (B (d+1)) _ (hinput d)]
    rfl

/-- The dot-product digit at any tuple address in a fixed polynomial domain.
There are U^(2^d) input rows and accessible bit positions. -/
theorem tupleDot_correct (input : Input) {U : ℕ} (B : (d : ℕ)→HAB.Matrix (HABSpacePadding.size U d))
    (hinput : ∀ d {m : ℕ} (rh rl ch cl : Fin m) (env : Fin m→Fin (HABSpacePadding.size U d)),
      (input rh rl ch cl).eval (B d) env = B (d+1) (code (env rh) (env rl)) (code (env ch) (env cl)))
    (d : ℕ) {n : ℕ} (a b : Template (n+2)) (e : Fin (tupleArity d (n+1))→Fin U)
    (hU : 2≤HABSpacePadding.size U d) (f g : ℕ→ℕ)
    (ha : ∀ r c : Fin (HABSpacePadding.size U d),
      a.eval (B d) (extend c r (fun i => decode d e i.succ)) = (f r.val).testBit c.val)
    (hb : ∀ r c : Fin (HABSpacePadding.size U d),
      b.eval (B d) (extend c r (fun i => decode d e i.succ)) = (g r.val).testBit c.val) :
    (tuples @input d (dot a b)).eval (B 0) e =
      (∑ i ∈ Finset.range (U^(2^d)), f i*g i).testBit (decode d e 0).val := by
  rw [tuples_correct @input B hinput,←HABSpacePadding.size_eq]
  let E := fun i : Fin n => decode d e i.succ
  let j := decode d e (0 : Fin (n+1))
  have ctx : decode d e = Fin.cases j E := by funext i; refine Fin.cases rfl (fun _ => rfl) i
  rw [ctx]
  exact dot_correct a b (B d) E hU f g ha hb j

/-- Compose the short residue graph, canonical cofactor inversion, bitwise CRT
comparison-word construction, and final binary shift. -/
noncomputable def residueReadout {n : ℕ} (L : Fin n) (basis modulusBits : Template (n+1))
    (residues : Template (n+2)) : Template (n+1) :=
  readout L basis modulusBits (graphBits (HABCRTCoefficients.coefficient basis residues))

theorem residueReadout_correct {n U K x : ℕ} (L : Fin n) (basis modulusBits : Template (n+1))
    (residues : Template (n+2)) (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ)
    (primes : ∀ p ∈ s, Nat.Prime p) (small : ∀ p ∈ s, p ≤ 2^K) (hK : 2≤K)
    (cap : 2^((K+1)*K)<U) (hx : x<HABCRTRecovery.modulus s)
    (precise : HABCRTRecovery.modulus s * HABCRTRecovery.budget s < 2^(e L).val)
    (sel : HABCRTCoefficients.Members basis A e s)
    (data : ∀ p v : Fin U, p.val∈s → (residues.eval A (extend v p e)=true ↔ v.val=x%p.val))
    (hm : ∀ j : Fin U, modulusBits.eval A (Fin.cases j e) = (HABCRTRecovery.modulus s).testBit j.val)
    (j : Fin U) (fit : (e L).val+j.val<U ∨ HABCRTRecovery.modulus s ≤ 2^(U-(e L).val)) :
    (residueReadout L basis modulusBits residues).eval A (Fin.cases j e) = x.testBit j.val := by
  have hle : 2^K ≤ 2^((K+1)*K) := Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ (by omega))
  have fits : HABCRTCoefficients.Fits (U:=U) s := fun p hp => ((small p hp).trans hle).trans_lt cap
  let inv := HABCRTRecovery.inverse s
  have cf (p c : Fin U) (hp : p.val ∈ s) :
      (graphBits (HABCRTCoefficients.coefficient basis residues)).eval A (extend c p e) =
      (HABCRTRecovery.coeff inv x p.val).testBit c.val := by
    apply graphBits_correct
    · exact (Nat.mod_lt _ (primes _ hp).pos).trans p.isLt
    · intro v
      exact HABCRTCoefficients.coefficient_spec basis residues A e s fits sel p v (primes _ hp)
        ⟨K,hK,small _ hp,cap⟩ x (fun t => data p t hp)
  exact readout_correct L basis modulusBits _ A e s inv primes small hK cap
    (fun _ hp => HABCRTRecovery.inverse_spec primes hp) hx precise sel cf hm j fit

/-- Direct query on an arbitrary binary input matrix in the range covered by
the selected CRT basis. The formula computes every input residue internally.
The binary word of the basis modulus and its membership predicate are inputs
to this construction. -/
noncomputable def matrixReadout {n : ℕ} (L : Fin n) (basis modulusBits : Template (n+1)) : Template (n+1) :=
  residueReadout L basis modulusBits (HABProductBlocks.binaryProduct 1 0)

theorem matrixReadout_correct {n U K : ℕ} (L : Fin n) (basis modulusBits : Template (n+1))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ)
    (primes : ∀ p ∈ s, Nat.Prime p) (small : ∀ p ∈ s, p ≤ 2^K) (hK : 2≤K)
    (cap : 2^((K+1)*K)<U) (hx : (∏ r : Fin U, HAB.rowWord (A r))<HABCRTRecovery.modulus s)
    (precise : HABCRTRecovery.modulus s * HABCRTRecovery.budget s < 2^(e L).val)
    (sel : HABCRTCoefficients.Members basis A e s)
    (hm : ∀ j : Fin U, modulusBits.eval A (Fin.cases j e) = (HABCRTRecovery.modulus s).testBit j.val)
    (j : Fin U) (fit : (e L).val+j.val<U ∨ HABCRTRecovery.modulus s ≤ 2^(U-(e L).val)) :
    (matrixReadout L basis modulusBits).eval A (Fin.cases j e) =
      (∏ r : Fin U, HAB.rowWord (A r)).testBit j.val :=
  residueReadout_correct L basis modulusBits _ A e s primes small hK cap hx precise sel
    (fun p v hp => HABProductBlocks.binaryProduct_spec 1 0 (extend v p e) A
      (primes _ hp) hK (small _ hp) cap) hm j fit

end DiophantineNP.HABCRTDot
