import DiophantineNP.HABProductBlocks
import DiophantineNP.HABSumParameters
import DiophantineNP.HABSourceTranslation
import DiophantineNP.HABPolylogRange
import DiophantineNP.WidthPrimeResidue
import DiophantineNP.SmallUniverses

/-! # Testing a proposed iterated product

The formula recognizes its full range of supported primes internally. It
compares the product with the binary word in a given row modulo every such
prime. An adequate first CRT block gives exact equality. In applications
where the product fits in an index, the proposed answer can also be quantified.
-/
namespace DiophantineNP.HABBoundedProduct
open Counting PrimeFormula WidthFormula FiniteArithmeticGap ShortResidue

open Predicate in
private def raw : Predicate :=
  let width := (eqN 1 0).neg.both (eqN 1 1).neg
  let cap := ex 6 (HABSumParameters.powAt 5 6)
  let times := ex 5 ((mul 4 1 5).both cap)
  let next := ex 4 ((add 1 3 4).both times)
  let capacity := ex 3 ((eqN 3 1).both next)
  ex 1 (width.both (ex 2 ((HABSumParameters.powAt 1 2).both ((le 0 2).both capacity))))

def Supported (U p : ℕ) : Prop := ∃ K, 2≤K ∧ p≤2^K ∧ 2^((K+1)*K)<U

private theorem raw_iff (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) :
    raw.holds U t e ↔ Supported U (e 0) := by
  simp [raw,Predicate.ex,Predicate.both,Predicate.neg,Predicate.eqN,Predicate.le,Predicate.lt,
    Predicate.mul,Predicate.add,HABSumParameters.powAt,Function.update,Supported]
  constructor
  · rintro ⟨k,_,⟨h0,h1⟩,_,hc,_,_,_,hcap⟩
    exact ⟨k,by omega,hc,hcap⟩
  · rintro ⟨k,hk,hp,cap⟩
    have he : k+1≤(k+1)*k := Nat.le_mul_of_pos_right _ (by omega)
    have hpow : 2^k≤2^((k+1)*k) := Nat.pow_le_pow_right (by decide) (by omega)
    have hi : (k+1)*k < 2^((k+1)*k) := Nat.lt_two_pow_self
    exact ⟨k,by omega,⟨by omega,by omega⟩,by omega,hp,by omega,by omega,by omega,cap⟩

private def allowed {k} (p : Fin k) : Template k :=
  .conj (fromFormula (prime p)) (raw.syntaxF (fun _ => p))

private theorem allowed_spec {k U} (p : Fin k) (A : HAB.Matrix U) (e : Fin k → Fin U) :
    (allowed p).eval A e = true ↔ (e p).val.Prime ∧ Supported U (e p).val := by
  let t (r c : ℕ) := if h : r<U ∧ c<U then A ⟨r,h.1⟩ ⟨c,h.2⟩ else false
  have eq : A=fun r c => t r.val c.val := by funext r c; simp [t,r.isLt,c.isLt]
  rw [eq,allowed,Tconj_true,fromFormula_eval,prime_true,raw.valid _ t,raw_iff]

/-- An input matrix may supply distinct formulas for the factors and the comparison word. -/
noncomputable def agrees {k} (value factors : Fin (k+2) → Fin (k+2) → Template (k+2)) : Template k :=
  .neg (.ex (.conj (allowed 0) (.neg (.ex (.conj (value 1 0) (factors 1 0))))))

theorem agrees_spec {k U} (A : HAB.Matrix U) (env : Fin k → Fin U) (x y : ℕ)
    (value factors : Fin (k+2) → Fin (k+2) → Template (k+2))
    (hx : ∀ p b : Fin U, p.val.Prime → Supported U p.val →
      ((value 1 0).eval A (Fin.cases b (Fin.cases p env))=true ↔ b.val=x%p.val))
    (hy : ∀ p b : Fin U, p.val.Prime → Supported U p.val →
      ((factors 1 0).eval A (Fin.cases b (Fin.cases p env))=true ↔ b.val=y%p.val)) :
    (agrees value factors).eval A env=true ↔
      ∀ p : ℕ, p.Prime → Supported U p → x%p=y%p := by
  classical
  simp only [agrees,Template.eval.eq_4,Bool.not_eq_true',←Bool.not_eq_true,Tex_true,Tconj_true,allowed_spec,
    Fin.cases_zero]
  push_neg
  constructor
  · intro h p hp hs
    obtain ⟨k,hk,hb,hcap⟩ := hs
    have he := Nat.le_mul_of_pos_left k (by omega : 0<k+1)
    have hu : p<U := (hb.trans (Nat.pow_le_pow_right (by decide) he)).trans_lt hcap
    let t : Fin U := ⟨p,hu⟩
    obtain ⟨b,bx,by'⟩ := h t ⟨hp,k,hk,hb,hcap⟩
    exact ((hx t b hp ⟨k,hk,hb,hcap⟩).mp bx).symm.trans ((hy t b hp ⟨k,hk,hb,hcap⟩).mp by')
  · intro h p hp
    let b : Fin U := ⟨x%p.val,(Nat.mod_lt _ hp.1.pos).trans p.isLt⟩
    exact ⟨b,(hx p b hp.1 hp.2).mpr rfl,(hy p b hp.1 hp.2).mpr (h p.val hp.1 hp.2)⟩

/-- Compare the product with one designated raw binary row in the same matrix. -/
noncomputable def checkRow {k} (r : Fin k) : Template k :=
  agrees (HABBinaryResidue.rowResidue r.succ.succ) HABProductBlocks.binaryProduct

theorem checkRow_spec {k U} (r : Fin k) (A : HAB.Matrix U) (e : Fin k → Fin U) :
    (checkRow r).eval A e=true ↔ ∀ p, p.Prime → Supported U p →
      HAB.rowWord (A (e r))%p=(∏ i : Fin U, HAB.rowWord (A i))%p := by
  unfold checkRow
  apply agrees_spec
  · rintro p b hp ⟨K,hK,hpK,hcap⟩
    exact HABBinaryResidue.rowResidue_short _ _ _ _ A hp hK hpK hcap
  · rintro p b hp ⟨K,hK,hpK,hcap⟩
    exact HABProductBlocks.binaryProduct_spec _ _ _ A hp hK hpK hcap

/-- If both values have at most a fixed power of log U bits, their residues
over the admissible primes distinguish them in every sufficiently large universe. -/
theorem exact_of_supported {U d k x y : ℕ}
    (large : HABPolylogRange.threshold (4*d+9)≤U) (size : k≤U.log2^d)
    (hx : x<2^k) (hy : y<2^k) :
    (∀ p, p.Prime → Supported U p → x%p=y%p) ↔ x=y := by
  refine ⟨fun h => HABPolylogRange.first_block_unique hx hy (fun j hj=>?_),
    fun h p _ _ => congrArg (fun a => a%p) h⟩
  have cap := HABPolylogRange.block_covered (k:=k) (s:=0) (t:=0) large size (Nat.zero_le _)
    (Nat.zero_le _) hj
  simp only [Nat.zero_mul,Nat.zero_add] at cap
  exact h _ (Nat.prime_nth_prime _) ⟨_,cap⟩

/-- Test equality to the product of a separately defined matrix of factors. -/
noncomputable def checkFactors {k} (r : Fin k)
    (cell : {a : ℕ} → Fin a → Fin a → Template a) : Template k :=
  agrees (HABBinaryResidue.rowResidue r.succ.succ)
    (fun p b => rewriteMatrix cell (HABProductBlocks.binaryProduct p b) id)

theorem checkFactors_exact {k U d bits} (r : Fin k) (A B : HAB.Matrix U) (e : Fin k → Fin U)
    (cell : {a : ℕ} → Fin a → Fin a → Template a)
    (entry : ∀ {a} (r c : Fin a) (s : Fin a → Fin U), (cell r c).eval A s = B (s r) (s c))
    (large : HABPolylogRange.threshold (4*d+9)≤U) (size : bits≤U.log2^d)
    (hv : HAB.rowWord (A (e r))<2^bits) (hp : (∏ i : Fin U, HAB.rowWord (B i))<2^bits) :
    (checkFactors r @cell).eval A e=true ↔ HAB.rowWord (A (e r))=∏ i : Fin U, HAB.rowWord (B i) := by
  rw [←exact_of_supported large size hv hp]
  unfold checkFactors
  apply agrees_spec
  · rintro p b pp ⟨K,hK,hpK,hcap⟩
    exact HABBinaryResidue.rowResidue_short _ _ _ _ A pp hK hpK hcap
  · rintro p b pp ⟨K,hK,hpK,hcap⟩
    rw [rewriteMatrix_eval _ A B entry]
    exact HABProductBlocks.binaryProduct_spec _ _ _ B pp hK hpK hcap

/-- Every admissible prime must give the same residue for the proposed finite
index and for the product of all rows of the input matrix. -/
noncomputable def indexGraph {k} (z : Fin k) : Template k :=
  agrees (fun p b => fromFormula (WidthPrimeResidue.remainder z.succ.succ p b))
    HABProductBlocks.binaryProduct

theorem indexGraph_exact {k U d bits} (z : Fin k) (A : HAB.Matrix U) (e : Fin k → Fin U)
    (large : HABPolylogRange.threshold (4*d+9)≤U) (size : bits≤U.log2^d)
    (hz : (e z).val<2^bits) (hp : (∏ i : Fin U, HAB.rowWord (A i))<2^bits) :
    (indexGraph z).eval A e=true ↔ (e z).val=∏ i : Fin U, HAB.rowWord (A i) := by
  rw [←exact_of_supported large size hz hp]
  unfold indexGraph
  apply agrees_spec
  · intro p b pp _
    rw [fromFormula_eval]
    exact WidthPrimeResidue.rem_true _ _ _ _ pp.pos
  · rintro p b pp ⟨K,hK,hpK,hcap⟩
    exact HABProductBlocks.binaryProduct_spec _ _ _ A pp hK hpK hcap

private noncomputable def largeBit : Template 1 := .ex (.conj (indexGraph 0) (.bit 0 1))
private def cutoff := max 4 (HABPolylogRange.threshold (4*2+9))

private theorem largeBit_spec {U} (hU : cutoff≤U) (A : HAB.Matrix U) (j : Fin U)
    (hp : (∏ i : Fin U, HAB.rowWord (A i))<U) :
    largeBit.eval A (fun _=>j) = (∏ i : Fin U, HAB.rowWord (A i)).testBit j.val := by
  have h4 : 4≤U := (le_max_left ..).trans hU
  have hl : 2≤U.log2 := (Nat.le_log2 (by omega : U≠0)).2 h4
  have size : U.log2+1≤U.log2^2 := by
    have h2 : 2≤U.log2 := hl
    nlinarith [Nat.mul_le_mul_left U.log2 h2]
  have width : U<2^(U.log2+1) := Nat.lt_log2_self
  have eq (z : Fin U) := indexGraph_exact (0 : Fin 2) A (pairEnv z j)
    ((le_max_right ..).trans hU) size (z.isLt.trans width) (hp.trans width)
  apply Bool.eq_iff_iff.mpr
  rw [largeBit,Tex_true]
  change (∃ z : Fin U, (.conj (indexGraph 0) (.bit 0 1) : Template 2).eval A (pairEnv z j)=true) ↔ _
  simp only [Tconj_true]
  change (∃ z : Fin U, (indexGraph 0).eval A (pairEnv z j)=true ∧ z.val.testBit j.val=true) ↔ _
  simp_rw [eq]
  constructor
  · rintro ⟨z,h,b⟩; exact h ▸ b
  · intro b; exact ⟨⟨_,hp⟩,rfl,b⟩

/-- A single source formula computes the product bit at all universe sizes
when the value of the entire product is smaller than the universe size. -/
theorem productBit_when_index_sized :
    ∃ φ : HAB.Form 1, ∀ {U} (A : HAB.Matrix U) (j : Fin U),
      (∏ i : Fin U, HAB.rowWord (A i))<U →
      (φ.Holds A (fun _ => j) ↔ (∏ i : Fin U, HAB.rowWord (A i)).testBit j.val=true) := by
  let Out (U : ℕ) (A : HAB.Matrix U) (j : Fin U) := (∏ i : Fin U, HAB.rowWord (A i)).testBit j.val
  suffices ∀ n (t : Template 1), (∀ {U}, n≤U → ∀ (A : HAB.Matrix U) (j : Fin U),
      (∏ i : Fin U, HAB.rowWord (A i))<U → t.eval A (fun _ => j)=Out U A j) →
      ∃ φ : HAB.Form 1, ∀ {U} (A : HAB.Matrix U) (j : Fin U),
        (∏ i : Fin U, HAB.rowWord (A i))<U → (φ.Holds A (fun _ => j) ↔ Out U A j=true) from
    this cutoff largeBit (fun h => largeBit_spec h)
  intro n
  induction n with
  | zero =>
    intro t ht
    exact ⟨HAB.toSource t,fun A j hp => by rw [HAB.toSource_correct,ht (Nat.zero_le _) A j hp]⟩
  | succ n ih =>
    intro t ht
    apply ih (branch (above n) t (fixedTable n (Out n)))
    intro U hu A j hp
    rw [FiniteArithmeticGap.branch_eval,above_eval]
    by_cases hn : n<U
    · simpa [hn] using ht hn A j hp
    · obtain rfl : U=n := by omega
      simp [fixedTable_eval]

end DiophantineNP.HABBoundedProduct
