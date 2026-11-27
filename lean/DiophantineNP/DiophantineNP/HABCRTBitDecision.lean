import DiophantineNP.HABCRTEstimate
import DiophantineNP.HABCRTSize

/-! # The final binary digit from CRT residue graphs

The estimate may be a long integer. Its congruences on the original prime
block suffice: multiply them by the locally computed residues of 2^s for
the order test, and extend those same congruences to 2 for the parity test.
-/
namespace DiophantineNP.HABCRTBitDecision
open Counting WidthFormula FiniteArithmeticGap HAB
open HABCRTCoefficients (Members)
open HABCRTLeading (Residues)
open HABCRTRecovery (modulus budget)

private def ren {a b : ℕ} (v : Template a) (f : Fin a → Fin b) : Template b :=
  rewriteMatrix (fun i j => .entry i j) v f

private theorem ren_eval {a b U : ℕ} (v : Template a) (f : Fin a → Fin b) (A : Matrix U) (e : Fin b→Fin U) :
    (ren v f).eval A e = v.eval A (e ∘ f) :=
  rewriteMatrix_eval _ A A (by intros; rfl) _ _ _

/-- Multiply a residue graph for Q by 2^s, prime by prime. The only
existential field value is Q mod p. -/
def shiftGraph {n : ℕ} (s : Fin n) (quotient : Template (n+2)) : Template (n+2) :=
  .ex (.conj (ren quotient (Fin.cases 0 (Fin.cases 2 (fun i => i.succ.succ.succ))))
    (HABCRTLeading.thresholdResidue false 0 s.succ.succ.succ 2 1))

theorem shiftGraph_correct {n U K Q : ℕ} (s : Fin n) (quotient : Template (n+2))
    (A : Matrix U) (e : Fin n→Fin U) (S : Finset ℕ)
    (primes : ∀ p∈S, Nat.Prime p) (small : ∀ p∈S, p ≤ 2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U) (data : Residues quotient A e S Q) :
    Residues (shiftGraph s quotient) A e S (Q*2^(e s).val) := by
  intro p b hp
  have names (v : Fin U) : Fin.cases v (extend b p e) ∘
      Fin.cases (0 : Fin (n+3)) (Fin.cases 2 (fun i : Fin n => i.succ.succ.succ)) = extend v p e := by
    funext i; refine Fin.cases rfl (fun j => ?_) i; refine Fin.cases rfl (fun _ => rfl) j
  have term (v : Fin U) : (HABCRTLeading.thresholdResidue false 0 s.succ.succ.succ 2 1).eval A
      (Fin.cases v (extend b p e))=true ↔ b.val=v.val*2^(e s).val%p.val := by
    let E : Fin (n+3)→Fin U := Fin.cases v (extend b p e)
    have H := HABCRTLeading.thresholdResidue_correct false (0 : Fin (n+3)) s.succ.succ.succ 2 1 A E
      (primes p.val hp) hK (small p.val hp) cap
    simpa only [Bool.toNat_false,Nat.add_zero] using H
  simp only [shiftGraph,Tex_true,Tconj_true,ren_eval,names,term,data p _ hp]
  have eq : (Q%p.val)*2^(e s).val%p.val=Q*2^(e s).val%p.val := Nat.mod_mul_mod ..
  exact ⟨fun ⟨_,hv,hb⟩ => (hv ▸ hb).trans eq,
    fun hb => ⟨⟨Q%p.val,(Nat.mod_lt _ (primes _ hp).pos).trans p.isLt⟩,rfl,hb.trans eq.symm⟩⟩

/-- Query an input graph at the prime two and the proposed residue one. -/
def atTwo {n : ℕ} (input : Template (n+2)) : Template n :=
  .ex (.conj (fromFormula (isNat 2 0)) (.ex (.conj (fromFormula (isNat 1 0)) input)))

theorem atTwo_correct {n U Q : ℕ} (input : Template (n+2)) (A : Matrix U) (e : Fin n→Fin U)
    (hU : 2<U) (data : ∀ p b : Fin U, p.val=2 →
      (input.eval A (extend b p e)=true ↔ b.val=Q%2)) :
    (atTwo input).eval A e = Q.testBit 0 := by
  apply Bool.eq_iff_iff.mpr
  simp only [atTwo,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,Fin.cases_zero]
  change (∃ p : Fin U, p.val=2 ∧ ∃ b : Fin U, b.val=1 ∧ input.eval A (extend b p e)=true) ↔ _
  simp only [Nat.testBit_zero,decide_eq_true_eq]
  exact ⟨fun ⟨p,hp,b,hb,v⟩ => ((data p b hp).mp v).symm.trans hb,
    fun h => ⟨⟨2,hU⟩,rfl,⟨1,by omega⟩,rfl,(data _ _ rfl).mpr h.symm⟩⟩

/-- Parity of the unique CRT value in [0,M), obtained by basis extension. -/
noncomputable def parity {n : ℕ} (L : Fin n) (basis : Template (n+1))
    (quotient : Template (n+2)) : Template n :=
  atTwo (HABCRTQuotient.remainder L basis quotient)

theorem parity_correct {n U K Q : ℕ} (L : Fin n) (basis : Template (n+1))
    (quotient : Template (n+2)) (A : Matrix U) (e : Fin n→Fin U) (S : Finset ℕ)
    (primes : ∀ p∈S, Nat.Prime p) (small : ∀ p∈insert 2 S, p ≤ 2^K) (hK : 2≤K)
    (cap : 2^((K+1)*K)<U) (hQ : Q < modulus S)
    (precise : modulus (insert 2 S)*budget (insert 2 S)<2^(e L).val)
    (sel : Members basis A e S) (data : Residues quotient A e S Q) :
    (parity L basis quotient).eval A e = Q.testBit 0 := by
  have hle : 2^K ≤ 2^((K+1)*K) := Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ (by omega))
  have hU := ((small 2 (Finset.mem_insert_self ..)).trans hle).trans_lt cap
  apply atTwo_correct _ _ _ hU
  intro p b hp
  have hh := HABCRTQuotient.remainder_correct L basis quotient A e S p b
    (by rw [hp]; exact Nat.prime_two) primes (by simpa only [hp] using small) hK cap
    (by simpa only [hp] using precise) sel data
  simpa only [hp,Nat.mod_eq_of_lt hQ] using hh

private theorem precision_base {S : Finset ℕ} {d : ℕ}
    (precise : modulus (insert 2 S)*budget (insert 2 S)<d) : modulus S*budget S<d := by
  by_cases h : 2 ∈ S
  · simpa [Finset.insert_eq_of_mem h] using precise
  · have hm : modulus (insert 2 S)=2*modulus S := Finset.prod_insert h
    have hb : budget (insert 2 S)=2+budget S := Finset.sum_insert h
    rw [hm,hb] at precise
    exact (Nat.mul_le_mul (Nat.le_mul_of_pos_left _ (by decide : 0<2))
      (Nat.le_add_left _ _)).trans_lt precise

/-- The final decision. The estimate and the target are supplied solely on
the original prime basis. The comparison and the test at two are constructed
by the formula itself. -/
noncomputable def formula {n : ℕ} (s L : Fin n) (basis : Template (n+1))
    (input quotient : Template (n+2)) : Template n :=
  HABCRTDot.correctedParity (HABCRTLeading.residueLt L basis input (shiftGraph s quotient))
    (parity L basis quotient)

theorem formula_correct {n U K x : ℕ} (s L : Fin n) (basis : Template (n+1))
    (input quotient : Template (n+2)) (A : Matrix U) (e : Fin n→Fin U) (S : Finset ℕ)
    (bs : List ℕ) (hs : (e s).val=bs.length)
    (large : ∀ a∈bs,x<a) (odd : ∀ a∈bs,a%2=1)
    (primes : ∀ p∈S, Nat.Prime p) (small : ∀ p∈insert 2 S, p ≤ 2^K) (hK : 2≤K)
    (cap : 2^((K+1)*K)<U) (hx : x<modulus S)
    (hq : HABCRTShift.estimate x bs*2^(e s).val<modulus S)
    (precise : modulus (insert 2 S)*budget (insert 2 S)<2^(e L).val)
    (sel : Members basis A e S) (data : Residues input A e S x)
    (qdata : Residues quotient A e S (HABCRTShift.estimate x bs)) :
    (formula s L basis input quotient).eval A e = x.testBit (e s).val := by
  let q := HABCRTShift.estimate x bs
  have sm (p : ℕ) (hp : p∈S) : p≤2^K := small p (Finset.mem_insert_of_mem hp)
  have hr := shiftGraph_correct s quotient A e S primes sm hK cap qdata
  have cmp := HABCRTLeading.residueLt_correct L basis input (shiftGraph s quotient) A e S primes sm hK cap
    hx hq (precision_base precise) sel data hr
  have hqm : q<modulus S := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans_lt hq
  have par := parity_correct L basis quotient A e S primes small hK cap hqm precise sel qdata
  rw [hs] at cmp ⊢
  exact HABCRTDot.correctedParity_correct _ _ A e bs large odd cmp par

open HABPrimeBlocks HABCRTShift
open HABCRTQuotient (auxSet baseBasis auxQuotient)

private theorem small_query {k s K q : ℕ} (hq : q∈primeSet k 0)
    (small : ∀ t≤s, ∀ p∈primeSet k t, p≤2^K) (p : ℕ) (hp : p∈insert q (auxSet k s)) :
    p≤2^K := by
  rcases Finset.mem_insert.mp hp with rfl|h
  · exact small 0 (Nat.zero_le _) _ hq
  · obtain ⟨r,hr,hrp⟩ := HABCRTQuotient.mem_auxSet.mp h
    exact small (r+1) hr p hrp

private theorem query_precision {S : Finset ℕ} {U K l : ℕ} (hK : 2≤K)
    (cap : 2^((K+1)*K)<U) (last : l=U-1) (small : ∀ p∈S,p≤2^K) :
    modulus S*budget S<2^l := last ▸ HABCRTSize.precision_max hK cap small

private theorem concreteDecision {n U K x : ℕ} (k s L : Fin n)
    (input quotient : Template (n+2)) (A : Matrix U) (e : Fin n→Fin U)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U) (last : (e L).val=U-1)
    (small : ∀ t≤(e s).val, ∀ p∈primeSet (e k).val t, p≤2^K)
    (room : x+2^(e s).val<block (e k).val 0)
    (data : Residues input A e (primeSet (e k).val 0) x)
    (qdata : Residues quotient A e (primeSet (e k).val 0) (estimate x (blocks (e k).val (e s).val))) :
    (formula s L (baseBasis k) input quotient).eval A e=x.testBit (e s).val := by
  let k' := (e k).val
  let B := primeSet k' 0
  let bs := blocks k' (e s).val
  have sm2 (p : ℕ) (h : p∈insert 2 B) : p≤2^K := by
    rcases Finset.mem_insert.mp h with rfl|hb
    · exact Nat.one_lt_two_pow (by omega)
    · exact small 0 (Nat.zero_le _) p hb
  have modB : modulus B=block k' 0 := primeSet_product ..
  have hx : x<block k' 0 := (Nat.le_add_right ..).trans_lt room
  have large (a : ℕ) (ha : a∈bs) : x<a := by
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp ha
    exact hx.trans_le (block_mono k' (Nat.zero_le _))
  have odd (a : ℕ) (ha : a∈bs) : a%2=1 := by
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp ha
    exact block_odd ..
  have len : bs.length=(e s).val := by simp [bs,blocks]
  have scaled : estimate x bs*2^(e s).val<modulus B := by
    rw [←len,modB]; exact HABCRTSize.comparison_fits large odd (by simpa only [len] using room)
  exact formula_correct s L (baseBasis k) input _ A e B bs len.symm large odd (fun _ h=>primeSet_primes h)
    sm2 hK cap (modB ▸ hx) scaled (query_precision hK cap last sm2) (HABCRTQuotient.baseBasis_members k A e) data qdata

/-- The base block, auxiliary divisor, and quotient are built by fixed formulas.
The two arguments provide residues of x and the numerator x times the half-block product. -/
noncomputable def blocksFromNumerator {n : ℕ} (k s L : Fin n)
    (input numerator : Template (n+2)) : Template n :=
  formula s L (baseBasis k) input (auxQuotient L k s numerator)

theorem blocksFromNumerator_correct {n U K x : ℕ} (k s L : Fin n)
    (input numerator : Template (n+2)) (A : Matrix U) (e : Fin n→Fin U)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U) (last : (e L).val=U-1)
    (small : ∀ t≤(e s).val, ∀ p∈primeSet (e k).val t, p≤2^K)
    (room : x+2^(e s).val<block (e k).val 0)
    (data : Residues input A e (primeSet (e k).val 0) x)
    (num : Residues numerator A e (primeSet (e k).val 0 ∪ auxSet (e k).val (e s).val)
      (x*halves (blocks (e k).val (e s).val))) :
    (blocksFromNumerator k s L input numerator).eval A e=x.testBit (e s).val := by
  apply concreteDecision k s L input _ A e hK cap last small room data
  intro q v hq
  have fine := small_query hq small
  apply HABCRTQuotient.auxQuotient_correct L k s numerator A e q v hq fine hK cap (query_precision hK cap last fine)
  intro p w hp
  exact num p w ((Finset.mem_insert.mp hp).elim (fun eq=>Finset.mem_union_left _ (eq ▸ hq))
    (Finset.mem_union_right _))

/-- A raw matrix query implementing the complete final shift on short prime
blocks. Every residue, half-block product, quotient, parity and comparison is
constructed inside the formula. The free indices are block length, output
position and reciprocal precision. -/
noncomputable def matrixBit {n : ℕ} (k s L : Fin n) : Template n :=
  let input := HABProductBlocks.binaryProduct (1 : Fin (n+2)) 0
  formula s L (baseBasis k) input (HABCRTEstimate.estimateGraph L k s input)

theorem matrixBit_correct {n U K : ℕ} (k s L : Fin n) (A : Matrix U) (e : Fin n→Fin U)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U) (last : (e L).val=U-1)
    (small : ∀ t≤(e s).val, ∀ p∈primeSet (e k).val t, p≤2^K)
    (room : (∏ r : Fin U, rowWord (A r))+2^(e s).val<block (e k).val 0) :
    (matrixBit k s L).eval A e=(∏ r : Fin U, rowWord (A r)).testBit (e s).val := by
  let x := ∏ r : Fin U, rowWord (A r)
  let input := HABProductBlocks.binaryProduct (1 : Fin (n+2)) 0
  have raw (p v : Fin U) (hp : p.val.Prime) (sm : p.val≤2^K) :
      input.eval A (extend v p e)=true ↔ v.val=x%p.val :=
    HABProductBlocks.binaryProduct_spec 1 0 (extend v p e) A hp hK sm cap
  apply concreteDecision k s L input _ A e hK cap last small room
  · intro p v hp
    exact raw _ _ (primeSet_primes hp) (small 0 (Nat.zero_le _) _ hp)
  · intro q v hq
    have fine := small_query hq small
    apply HABCRTEstimate.estimateGraph_correct L k s input A e q v hq fine hK cap (query_precision hK cap last fine)
    intro p w hp
    have pr : p.val.Prime := (Finset.mem_insert.mp hp).elim (fun eq=>eq ▸ primeSet_primes hq)
      HABCRTQuotient.auxSet_primes
    exact raw p w pr (fine p.val hp)

end DiophantineNP.HABCRTBitDecision
