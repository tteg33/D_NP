import DiophantineNP.HABWideQuotient
import DiophantineNP.HABWideOutput
import DiophantineNP.HABCRTBitDecision

/-! # The upper-scale CRT product-bit decision

HAB's short-list product interface is the only supplied logical operation.
Every field used for the shift has p³ smaller than the working universe.
The original matrix is the entire data input.
-/
namespace DiophantineNP.HABWideBitDecision
open Counting WidthFormula FiniteArithmeticGap HAB HABCRTShift HABPrimeBlocks
open HABCRTCoefficients (Members graphAt graphAt_spec)
open HABCRTLeading (Residues)
open HABCRTQuotient (auxSet baseBasis)
open HABCRTRecovery (modulus budget)
open HABPowerReduction (ShortProducts)

private noncomputable def shiftGraph (ops : ShortProducts) {n : ℕ}
    (s : Fin n) (quotient : Template (n+2)) : Template (n+2) :=
  .ex (.conj (graphAt quotient 0 2 (fun i => i.succ.succ.succ))
    (HABWideExtend.scaledResidue ops 0 s.succ.succ.succ 2 1))

private theorem shiftGraph_correct (ops : ShortProducts) {n U Q : ℕ} (s : Fin n) (quotient : Template (n+2))
    (A : Matrix U) (e : Fin n→Fin U) (S : Finset ℕ) (primes : ∀ p∈S, Nat.Prime p)
    (size : ∀ p∈S,p^3<U) (data : Residues quotient A e S Q) :
    Residues (shiftGraph ops s quotient) A e S (Q*2^(e s).val) := by
  intro p b hp
  have qa (v : Fin U) : (graphAt quotient 0 2 (fun i => i.succ.succ.succ)).eval A
      (Fin.cases v (extend b p e)) = quotient.eval A (extend v p e) := by
    rw [graphAt_spec]; rfl
  have term (v : Fin U) : (HABWideExtend.scaledResidue ops 0 s.succ.succ.succ 2 1).eval A
      (Fin.cases v (extend b p e))=true ↔ b.val=v.val*2^(e s).val%p.val := by
    let E : Fin (n+3)→Fin U := Fin.cases v (extend b p e)
    exact HABWideExtend.scaledResidue_correct ops 0 s.succ.succ.succ 2 1 A E (primes p.val hp) (size p.val hp)
  simp only [shiftGraph,Tex_true,Tconj_true,qa,term,data p _ hp]
  have eq : (Q%p.val)*2^(e s).val%p.val=Q*2^(e s).val%p.val := Nat.mod_mul_mod ..
  exact ⟨fun ⟨_,hv,hb⟩ => (hv ▸ hb).trans eq,
    fun hb => ⟨⟨Q%p.val,(Nat.mod_lt _ (primes _ hp).pos).trans p.isLt⟩,rfl,hb.trans eq.symm⟩⟩

/-- The constructed quotient parity is the CRT extension at the prime 2. -/
private noncomputable def parity (ops : ShortProducts) {n : ℕ} (L : Fin n) (basis : Template (n+1))
    (quotient : Template (n+2)) : Template n :=
  HABCRTBitDecision.atTwo (HABWideQuotient.remainder ops L basis quotient)

private theorem parity_correct (ops : ShortProducts) {n U Q : ℕ} (L : Fin n) (basis : Template (n+1))
    (quotient : Template (n+2)) (A : Matrix U) (e : Fin n→Fin U) (S : Finset ℕ)
    (primes : ∀ p∈S, Nat.Prime p) (size : ∀ p∈insert 2 S,p^3<U) (hQ : Q<modulus S)
    (precise : modulus (insert 2 S)*budget (insert 2 S)<2^(e L).val)
    (sel : Members basis A e S) (data : Residues quotient A e S Q) :
    (parity ops L basis quotient).eval A e = Q.testBit 0 := by
  have hU : 2<U := (by decide : 2≤2^3).trans_lt (size 2 (Finset.mem_insert_self ..))
  apply HABCRTBitDecision.atTwo_correct _ _ _ hU
  intro p b hp
  have hh := HABWideQuotient.remainder_correct ops L basis quotient A e S p b
    (by rw [hp]; exact Nat.prime_two) primes (by simpa only [hp] using size)
    (by simpa only [hp] using precise) sel data
  simpa only [hp,Nat.mod_eq_of_lt hQ] using hh

private noncomputable def decision (ops : ShortProducts) {n : ℕ} (k s L : Fin n)
    (input quotient : Template (n+2)) : Template n :=
  HABCRTDot.correctedParity
    (HABWideExtend.residueLt ops L (baseBasis k) input (shiftGraph ops s quotient))
    (parity ops L (baseBasis k) quotient)

private theorem decision_correct (ops : ShortProducts) {n U x : ℕ} (k s L : Fin n)
    (input quotient : Template (n+2)) (A : Matrix U) (e : Fin n→Fin U)
    (cap : 27<U) (last : (e L).val=U-1)
    (size : ∀ p∈primeSet (e k).val 0,p^3<U) (room : x+2^(e s).val<block (e k).val 0)
    (data : Residues input A e (primeSet (e k).val 0) x)
    (qdata : Residues quotient A e (primeSet (e k).val 0) (estimate x (blocks (e k).val (e s).val))) :
    (decision ops k s L input quotient).eval A e=x.testBit (e s).val := by
  let B := primeSet (e k).val 0
  let bs := blocks (e k).val (e s).val
  let Q := estimate x bs
  have precision (T : Finset ℕ) (h : ∀ p∈T,p^3<U) : modulus T*budget T<2^(e L).val :=
    last ▸ HABWideOutput.precision_of_cubes cap h
  have size2 (p : ℕ) (hp : p∈insert 2 B) : p^3<U := by
    rcases Finset.mem_insert.mp hp with rfl|hb
    · exact (by decide : 2^3≤27).trans_lt cap
    · exact size p hb
  have len : bs.length=(e s).val := by simp [bs,blocks]
  have modB : modulus B=block (e k).val 0 := primeSet_product ..
  have hx : x<block (e k).val 0 := (Nat.le_add_right ..).trans_lt room
  have large (a : ℕ) (ha : a∈bs) : x<a := by
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp ha
    exact hx.trans_le (block_mono _ (Nat.zero_le _))
  have odd (a : ℕ) (ha : a∈bs) : a%2=1 := by
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp ha
    exact block_odd ..
  have hq : Q*2^(e s).val<modulus B := by
    rw [←len,modB]; exact HABCRTSize.comparison_fits large odd (by simpa only [len] using room)
  have hr := shiftGraph_correct ops s quotient A e B (fun _ h=>primeSet_primes h) size qdata
  have sel := HABCRTQuotient.baseBasis_members k A e
  have cmp := HABWideExtend.residueLt_correct ops L (baseBasis k) input (shiftGraph ops s quotient) A e B
    (fun _ h=>primeSet_primes h) size (modB ▸ hx) hq (precision B size) sel data hr
  have hqm : Q<modulus B := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans_lt hq
  have par := parity_correct ops L (baseBasis k) quotient A e B (fun _ h=>primeSet_primes h)
    size2 hqm (precision _ size2) sel qdata
  rw [←len] at cmp ⊢
  exact HABCRTDot.correctedParity_correct _ _ A e bs large odd cmp par

/-- Bit s of the iterated product on the original input. The indices k and L
specify the size of each prime block and the working reciprocal precision. -/
noncomputable def matrixBit (ops : ShortProducts) {n : ℕ} (k s L : Fin n) : Template n :=
  let input := (HABLargePrimeProduct.source ops (1 : Fin (n+2)) 0).translate
  decision ops k s L input (HABWideQuotient.estimateGraph ops L k s input)

theorem matrixBit_correct (ops : ShortProducts) {n U : ℕ} (k s L : Fin n)
    (A : Matrix U) (e : Fin n→Fin U) (cap : 27<U) (last : (e L).val=U-1)
    (size : ∀ t≤(e s).val, ∀ p∈primeSet (e k).val t,p^3<U)
    (room : (∏ r : Fin U, rowWord (A r))+2^(e s).val<block (e k).val 0) :
    (matrixBit ops k s L).eval A e=(∏ r : Fin U, rowWord (A r)).testBit (e s).val := by
  let x := ∏ r : Fin U, rowWord (A r)
  let input := (HABLargePrimeProduct.source ops (1 : Fin (n+2)) 0).translate
  have raw (p v : Fin U) (hp : p.val.Prime) : input.eval A (extend v p e)=true ↔ v.val=x%p.val := by
    rw [show input=(HABLargePrimeProduct.source ops (1 : Fin (n+2)) 0).translate from rfl,
      HAB.Form.translate_correct,HABLargePrimeProduct.source_correct ops _ _ _ _ hp]
    exact eq_comm
  apply decision_correct ops k s L input _ A e cap last (size 0 (Nat.zero_le _)) room
  · intro p v hp; exact raw p v (primeSet_primes hp)
  · intro q v hq
    have hsize (p : ℕ) (hp : p∈insert q.val (auxSet (e k).val (e s).val)) : p^3<U := by
      rcases Finset.mem_insert.mp hp with rfl|hd
      · exact size 0 (Nat.zero_le _) _ hq
      · obtain ⟨r,hr,hrp⟩ := HABCRTQuotient.mem_auxSet.mp hd
        exact size (r+1) hr p hrp
    apply HABWideQuotient.estimateGraph_correct ops L k s input A e q v hq hsize
      (last ▸ HABWideOutput.precision_of_cubes cap hsize)
    intro p w hp
    exact raw p w ((Finset.mem_insert.mp hp).elim (fun eq=>eq ▸ primeSet_primes hq) HABCRTQuotient.auxSet_primes)

/-- Three-variable interface consumed by the polynomial padding construction. -/
theorem localSpec (ops : ShortProducts) : HABWideOutput.LocalSpec (matrixBit ops 0 1 2) := by
  intro V A k s L cap last size room
  exact matrixBit_correct ops (0 : Fin 3) 1 2 A ![k,s,L] cap last size room

end DiophantineNP.HABWideBitDecision
