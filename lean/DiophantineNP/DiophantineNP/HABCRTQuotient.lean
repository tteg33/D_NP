import DiophantineNP.HABCRTExtend
import DiophantineNP.HABPrimeBlocks
import DiophantineNP.ScaleFormula

/-! # Quotient residues for a divisor given by a short-prime basis

For a divisor B equal to a basis product, the old residues of X also describe
its remainder X % B. Extending that representation to a fresh prime supplies
the missing remainder digit in B * (X / B) + (X % B) = X.
-/
namespace DiophantineNP.HABCRTQuotient
open Counting WidthFormula PrimeFormula FiniteArithmeticGap HABCRTRecovery

private def ren {a k : ℕ} (p : Template a) (f : Fin a→Fin k) : Template k :=
  rewriteMatrix (fun i j => .entry i j) p f

private theorem ren_eval {a k U : ℕ} (p : Template a) (f : Fin a→Fin k)
    (A : HAB.Matrix U) (e : Fin k→Fin U) : (ren p f).eval A e=p.eval A (e ∘ f) :=
  rewriteMatrix_eval _ A A (by intros; rfl) _ _ _

private abbrev push {k U : ℕ} (z : Fin U) (e : Fin k→Fin U) : Fin (k+1)→Fin U := Fin.cases z e

private def probe {n : ℕ} (graph : Template (n+2)) (v : Fin (n+3)) (q : Fin n) : Template (n+3) :=
  ren graph (Fin.cases v (Fin.cases q.succ.succ.succ (fun i => i.succ.succ.succ)))

private theorem probe_eval {n U : ℕ} (graph : Template (n+2)) (v : Fin (n+3)) (q : Fin n)
    (A : HAB.Matrix U) (e : Fin n→Fin U) (x r b : Fin U) :
    (probe graph v q).eval A (push x (push r (push b e))) =
      graph.eval A (extend (push x (push r (push b e)) v) (e q) e) := by
  rw [probe,ren_eval]
  apply congrArg (graph.eval A)
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun _ => rfl) j

/-- The field formula has no matrix entries. Erasing those entries explicitly
allows the same graph to be used under an arbitrary matrix interpretation. -/
private def arithmetic {k : ℕ} (p : Template k) : Template k :=
  rewriteMatrix (fun i _ => .neg (.atom (.eqv i i))) p id

private theorem arithmetic_eval {k U : ℕ} (p : Template k) (A : HAB.Matrix U) (e : Fin k→Fin U) :
    (arithmetic p).eval A e = p.eval (fun _ _ => false) e :=
  rewriteMatrix_eval _ A _ (by intros; simp [Template.eval,Atom.eval]) _ _ _

/-- Compose the divisor, remainder, and dividend residue graphs. The last
argument is always the original input matrix, including inside the three graphs. -/
noncomputable def assemble {n : ℕ} (q t : Fin n) (M R X : Template (n+2)) : Template n :=
  .conj (fromFormula (ltF t q)) <| .ex <| .ex <| .ex <|
    .conj (probe M 2 q) <| .conj (probe R 1 q) <| .conj (probe X 0 q) <|
      arithmetic (quotientField 2 t.succ.succ.succ 1 q.succ.succ.succ 0)

theorem assemble_correct {n U X B : ℕ} (q t : Fin n) (M R I : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (hp : 0<(e q).val) (cop : (e q).val.Coprime B)
    (cap : (e q).val^2≤U)
    (modulusGraph : ∀ v : Fin U, M.eval A (extend v (e q) e)=true ↔ v.val=B%(e q).val)
    (restGraph : ∀ v : Fin U, R.eval A (extend v (e q) e)=true ↔ v.val=(X%B)%(e q).val)
    (inputGraph : ∀ v : Fin U, I.eval A (extend v (e q) e)=true ↔ v.val=X%(e q).val) :
    (assemble q t M R I).eval A e=true ↔ (e t).val=(X/B)%(e q).val := by
  simp only [assemble,Tconj_true,fromFormula_eval,ltF_true,Tex_true]
  change (_ ∧ ∃ b r x : Fin U,
    (probe M 2 q).eval A (push x (push r (push b e)))=true ∧
    (probe R 1 q).eval A (push x (push r (push b e)))=true ∧
    (probe I 0 q).eval A (push x (push r (push b e)))=true ∧
    (arithmetic _).eval A (push x (push r (push b e)))=true) ↔ _
  simp_rw [probe_eval,arithmetic_eval]
  change ((e t).val<(e q).val ∧ ∃ b r x : Fin U, M.eval A (extend b (e q) e)=true ∧
    R.eval A (extend r (e q) e)=true ∧ I.eval A (extend x (e q) e)=true ∧ _) ↔ _
  simp_rw [modulusGraph,restGraph,inputGraph]
  have field (b r x : Fin U) (hb : b.val=B%(e q).val) (hr : r.val=(X%B)%(e q).val)
      (hx : x.val=X%(e q).val) (ht : (e t).val<(e q).val) :=
    quotientField_of_square_le (X:=X) (B:=B) 2 t.succ.succ.succ 1 q.succ.succ.succ 0
      (push x (push r (push b e))) hp cop hb hr hx ht cap
  constructor
  · rintro ⟨ht,b,r,x,hb,hr,hx,h⟩
    exact (field b r x hb hr hx ht).mp h
  · intro h
    have ht : (e t).val<(e q).val := h ▸ Nat.mod_lt _ hp
    let digit (a : ℕ) : Fin U := ⟨a%(e q).val,(Nat.mod_lt _ hp).trans (e q).isLt⟩
    exact ⟨ht,digit B,digit (X%B),digit X,rfl,rfl,rfl,(field _ _ _ rfl rfl rfl ht).mpr h⟩

private theorem basis_coprime {s : Finset ℕ} {q : ℕ} (hq : q.Prime) (fresh : q∉s)
    (primes : ∀ p∈s, Nat.Prime p) : q.Coprime (modulus s) :=
  (Nat.coprime_prod_left_iff.mpr (fun p hp => (Nat.coprime_primes (primes p hp) hq).mpr
    (fun eq => fresh (eq ▸ hp)))).symm

/-- Remainder reduction preserves the input digit at every basis prime. -/
theorem remainder_on_basis (X : ℕ) {s : Finset ℕ} {p : ℕ} (hp : p∈s) :
    (X % modulus s) % p = X%p :=
  Nat.mod_mod_of_dvd X (Finset.dvd_prod_of_mem (fun i => i) hp)

private theorem square_capacity {U K q : ℕ} (hK : 2≤K) (hq : q≤2^K) (cap : 2^((K+1)*K)<U) :
    q^2≤U := calc
  q^2 ≤ (2^K)^2 := Nat.pow_le_pow_left hq _
  _ = 2^(K*2) := (pow_mul ..).symm
  _ ≤ 2^((K+1)*K) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  _ ≤ U := cap.le


private def extraBasis {n : ℕ} (basis : Template (n+1)) : Template ((n+2)+1) :=
  ren basis (Fin.cases 0 (fun i => i.succ.succ.succ))

private def extraInput {n : ℕ} (input : Template (n+2)) : Template ((n+2)+2) :=
  ren input (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ.succ)))

/-- Reconstruct the remainder modulo B at the query prime. The input graph is
used only on the divisor basis, where X and X % B have equal residues. -/
noncomputable def remainder {n : ℕ} (L : Fin n) (basis : Template (n+1)) (input : Template (n+2)) :
    Template (n+2) :=
  HABCRTExtend.formula L.succ.succ 1 0 (extraBasis basis) (extraInput input)

theorem remainder_correct {n U K X : ℕ} (L : Fin n) (basis : Template (n+1)) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ) (q b : Fin U) (hp : q.val.Prime)
    (primes : ∀ p∈s,Nat.Prime p) (small : ∀ p∈insert q.val s,p≤2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U)
    (precision : modulus (insert q.val s)*budget (insert q.val s)<2^(e L).val)
    (sel : HABCRTCoefficients.Members basis A e s)
    (data : ∀ p v : Fin U, p.val∈s → (input.eval A (extend v p e)=true ↔ v.val=X%p.val)) :
    (remainder L basis input).eval A (extend b q e)=true ↔ b.val=(X%modulus s)%q.val := by
  have smem : HABCRTCoefficients.Members (extraBasis basis) A (extend b q e) s := by
    intro p
    rw [extraBasis,ren_eval]
    have names : push p (extend b q e) ∘ Fin.cases (0 : Fin ((n+2)+1)) (fun i : Fin n => i.succ.succ.succ) =
        push p e := by funext z; refine Fin.cases rfl (fun _ => rfl) z
    rw [names]; exact sel p
  have sdata (p v : Fin U) (hm : p.val∈s) :
      (extraInput input).eval A (extend v p (extend b q e))=true ↔ v.val=(X%modulus s)%p.val := by
    rw [extraInput,ren_eval,remainder_on_basis X hm]
    have names : extend v p (extend b q e) ∘ Fin.cases (0 : Fin ((n+2)+2))
        (Fin.cases 1 (fun i : Fin n => i.succ.succ.succ.succ)) = extend v p e := by
      funext z; refine Fin.cases rfl (fun i => ?_) z; exact Fin.cases rfl (fun _ => rfl) i
    rw [names]; exact data p v hm
  exact HABCRTExtend.formula_correct L.succ.succ 1 0 (extraBasis basis) (extraInput input) A
    (extend b q e) s hp primes small hK cap (Nat.mod_lt X (Finset.prod_pos (fun p h => (primes p h).pos)))
    precision smem sdata

/-- Quotient of an unrestricted nonnegative integer by the product of the
selected basis primes. Its only input is the dividend's residue graph. -/
noncomputable def formula {n : ℕ} (L q t : Fin n) (basis : Template (n+1)) (input : Template (n+2)) :
    Template n :=
  assemble q t (HABCRTCoefficients.modulus basis) (remainder L basis input) input

/-- The field test works for every query prime coprime to the divisor and every
candidate. The assumptions concern the prime basis, precision and source residues.
The dividend, divisor, and quotient may all be larger than the entire universe. -/
theorem formula_correct {n U K X : ℕ} (L q t : Fin n) (basis : Template (n+1)) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ) (hp : (e q).val.Prime) (fresh : (e q).val∉s)
    (primes : ∀ p∈s,Nat.Prime p) (small : ∀ p∈insert (e q).val s,p≤2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U)
    (precision : modulus (insert (e q).val s)*budget (insert (e q).val s)<2^(e L).val)
    (sel : HABCRTCoefficients.Members basis A e s)
    (data : ∀ p v : Fin U, p.val∈insert (e q).val s →
      (input.eval A (extend v p e)=true ↔ v.val=X%p.val)) :
    (formula L q t basis input).eval A e=true ↔ (e t).val=(X/modulus s)%(e q).val := by
  have sq := small (e q).val (Finset.mem_insert_self ..)
  have ok : HABBoundedProduct.Supported U (e q).val := ⟨K,hK,sq,cap⟩
  have fits : HABCRTCoefficients.Fits (U:=U) s := fun p h =>
    ((small p (Finset.mem_insert_of_mem h)).trans (Nat.pow_le_pow_right (by decide)
      (Nat.le_mul_of_pos_left K (by omega : 0<K+1)))).trans_lt cap
  exact assemble_correct q t _ _ input A e hp.pos (basis_coprime hp fresh primes) (square_capacity hK sq cap)
    (fun v => HABCRTCoefficients.modulus_spec basis A e s fits sel (e q) v hp ok)
    (fun v => remainder_correct L basis input A e s (e q) v hp primes small hK cap precision sel
      (fun p z h => data p z (Finset.mem_insert_of_mem h)))
    (fun v => data (e q) v (Finset.mem_insert_self ..))

/-- A concrete dividend graph for the product of every row of the raw binary
matrix. The divisor basis and arbitrary query prime remain variable. -/
noncomputable def productQuotient {n : ℕ} (L q t : Fin n) (basis : Template (n+1)) : Template n :=
  formula L q t basis (HABProductBlocks.binaryProduct 1 0)

theorem productQuotient_correct {n U K : ℕ} (L q t : Fin n) (basis : Template (n+1))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ) (hp : (e q).val.Prime) (fresh : (e q).val∉s)
    (primes : ∀ p∈s,Nat.Prime p) (small : ∀ p∈insert (e q).val s,p≤2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U)
    (precision : modulus (insert (e q).val s)*budget (insert (e q).val s)<2^(e L).val)
    (sel : HABCRTCoefficients.Members basis A e s) :
    (productQuotient L q t basis).eval A e=true ↔
      (e t).val=((∏ r : Fin U, HAB.rowWord (A r))/modulus s)%(e q).val := by
  apply formula_correct L q t basis _ A e s hp fresh primes small hK cap precision sel
  intro p v hm
  have pp : p.val.Prime := (Finset.mem_insert.mp hm).elim (fun eq => eq ▸ hp) (primes p.val)
  exact HABProductBlocks.binaryProduct_spec 1 0 (extend v p e) A pp hK (small p.val hm) cap

/-- Instantiate the general divisor by a block of k consecutive odd primes
starting at block b. All divisor entries are selected internally by prime rank. -/
noncomputable def blockQuotient {n : ℕ} (L k b q t : Fin n) : Template n :=
  productQuotient L q t (HABPrimeBlocks.blockMember k.succ b.succ 0)

theorem blockQuotient_correct {n U K : ℕ} (L k b q t : Fin n) (A : HAB.Matrix U) (e : Fin n→Fin U)
    (hp : (e q).val.Prime) (fresh : (e q).val ∉ HABPrimeBlocks.primeSet (e k).val (e b).val)
    (small : ∀ p∈insert (e q).val (HABPrimeBlocks.primeSet (e k).val (e b).val),p≤2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U)
    (precision : let full := insert (e q).val (HABPrimeBlocks.primeSet (e k).val (e b).val);
                 modulus full*budget full < 2^(e L).val) :
    (blockQuotient L k b q t).eval A e=true ↔
      (e t).val=((∏ r : Fin U, HAB.rowWord (A r))/HABCRTShift.block (e k).val (e b).val)%(e q).val := by
  have div := productQuotient_correct L q t (HABPrimeBlocks.blockMember k.succ b.succ 0) A e
    (HABPrimeBlocks.primeSet (e k).val (e b).val) hp fresh (fun _ h => HABPrimeBlocks.primeSet_primes h)
    small hK cap precision (fun p => HABPrimeBlocks.blockMember_mem k.succ b.succ 0 A (push p e))
  exact div.trans (by rw [modulus,HABPrimeBlocks.primeSet_product])

/-- The quotient as a reusable residue graph. Slots zero and one are the
proposed value and target prime. All source parameters follow unchanged. -/
noncomputable def graph {n : ℕ} (L : Fin n) (basis : Template (n+1)) (input : Template (n+2)) :
    Template (n+2) := formula L.succ.succ 1 0 (extraBasis basis) (extraInput input)

theorem graph_correct {n U K X : ℕ} (L : Fin n) (basis : Template (n+1)) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ) (q t : Fin U) (hp : q.val.Prime) (fresh : q.val∉s)
    (primes : ∀ p∈s,Nat.Prime p) (small : ∀ p∈insert q.val s,p≤2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U)
    (precision : modulus (insert q.val s)*budget (insert q.val s)<2^(e L).val)
    (sel : HABCRTCoefficients.Members basis A e s)
    (data : ∀ p v : Fin U, p.val∈insert q.val s →
      (input.eval A (extend v p e)=true ↔ v.val=X%p.val)) :
    (graph L basis input).eval A (extend t q e)=true ↔ t.val=(X/modulus s)%q.val := by
  apply formula_correct L.succ.succ 1 0 _ _ A (extend t q e) s hp fresh primes small hK cap precision
  · intro p
    rw [extraBasis,ren_eval]
    have he : push p (extend t q e) ∘ Fin.cases (0 : Fin ((n+2)+1)) (fun i : Fin n => i.succ.succ.succ) =
        push p e := by funext z; refine Fin.cases rfl (fun _ => rfl) z
    rw [he]; exact sel p
  · intro p v h
    rw [extraInput,ren_eval]
    have he : extend v p (extend t q e) ∘ Fin.cases (0 : Fin ((n+2)+2))
        (Fin.cases 1 (fun i : Fin n => i.succ.succ.succ.succ)) = extend v p e := by
      funext z; refine Fin.cases rfl (fun i => ?_) z; exact Fin.cases rfl (fun _ => rfl) i
    rw [he]; exact data p v h

open HABPrimeBlocks HABCRTShift

/-- The union of the prime blocks with numbers 1 through s. -/
noncomputable def auxSet (k s : ℕ) : Finset ℕ :=
  (Finset.range s).biUnion (fun r => primeSet k (r+1))

theorem mem_auxSet {k s p : ℕ} : p∈auxSet k s ↔ ∃ r<s, p∈primeSet k (r+1) := by
  simp [auxSet]

theorem auxSet_primes {k s p : ℕ} (hp : p∈auxSet k s) : p.Prime := by
  obtain ⟨_,_,h⟩ := mem_auxSet.mp hp
  exact primeSet_primes h

theorem auxSet_disjoint (k s : ℕ) : Disjoint (primeSet k 0) (auxSet k s) := by
  apply Finset.disjoint_left.mpr
  intro p orig hp
  obtain ⟨r,_,h⟩ := mem_auxSet.mp hp
  exact (Finset.disjoint_left.mp (primeSet_disjoint (t:=0) (v:=r+1) k (by omega))) orig h

theorem auxSet_product (k s : ℕ) : modulus (auxSet k s) = (blocks k s).prod := by
  have pair : Set.PairwiseDisjoint (↑(Finset.range s) : Set ℕ) (fun r => primeSet k (r+1)) := by
    intro a _ b _ ne
    exact primeSet_disjoint k (by omega)
  rw [modulus,auxSet,Finset.prod_biUnion pair]
  simp_rw [primeSet_product]
  clear pair
  induction s with
  | zero => simp [blocks]
  | succ s ih =>
    rw [Finset.prod_range_succ]
    change _ = ((List.range (s+1)).map (fun r => block k (r+1))).prod
    rw [List.range_succ,List.map_append,List.prod_append]
    simp [blocks] at ih ⊢
    exact Or.inl ih

/-- Membership of a candidate prime in block zero. -/
noncomputable def baseBasis {n : ℕ} (k : Fin n) : Template (n+1) :=
  .ex (.conj (fromFormula (isNat 0 0)) (blockMember k.succ.succ 0 1))

theorem baseBasis_members {n U : ℕ} (k : Fin n) (A : HAB.Matrix U) (e : Fin n→Fin U) :
    HABCRTCoefficients.Members (baseBasis k) A e (primeSet (e k).val 0) := by
  intro p
  simp only [baseBasis,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,blockMember_mem,Fin.cases_zero,Fin.cases_succ]
  change (∃ z : Fin U, z.val=0 ∧ p.val∈primeSet (e k).val z.val) ↔ _
  exact ⟨fun ⟨z,h,hp⟩ => h ▸ hp,fun h => ⟨⟨0,p.pos⟩,rfl,h⟩⟩

/-- The auxiliary family in prime, row, outer-parameter order. Row r<s
selects block r+1. Every row at or above s selects the empty basis. -/
noncomputable def auxFamily {n : ℕ} (k s : Fin n) : Template (n+2) :=
  .conj (fromFormula (ltF 1 s.succ.succ))
    (.ex (.conj (fromFormula (Packing.successorFormula 2 0)) (blockMember k.succ.succ.succ 0 1)))

theorem auxFamily_correct {n U : ℕ} (k s : Fin n) (A : HAB.Matrix U) (e : Fin n→Fin U) (p r : Fin U) :
    (auxFamily k s).eval A (extend p r e)=true ↔ r.val<(e s).val ∧ p.val∈primeSet (e k).val (r.val+1) := by
  simp only [auxFamily,Tconj_true,fromFormula_eval,ltF_true,Tex_true,Packing.successorFormula_true,blockMember_mem,
    Fin.cases_succ,Fin.cases_zero]
  change (r.val<(e s).val ∧ ∃ t : Fin U, r.val+1=t.val ∧ p.val∈primeSet (e k).val t.val) ↔ _
  exact ⟨fun ⟨hr,t,ht,h⟩ => ⟨hr,ht ▸ h⟩,
    fun ⟨hr,h⟩ => ⟨hr,⟨r.val+1,by have := (e s).isLt; omega⟩,rfl,h⟩⟩

/-- A membership graph for the divisor consisting of all auxiliary blocks. -/
noncomputable def auxBasis {n : ℕ} (k s : Fin n) : Template (n+1) :=
  .ex (ren (auxFamily k s) (Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ))))

theorem auxBasis_members {n U : ℕ} (k s : Fin n) (A : HAB.Matrix U) (e : Fin n→Fin U) :
    HABCRTCoefficients.Members (auxBasis k s) A e (auxSet (e k).val (e s).val) := by
  intro p
  rw [auxBasis,Tex_true,mem_auxSet]
  have eq (r : Fin U) : (push r (push p e)) ∘ Fin.cases 1 (Fin.cases 0 (fun i : Fin n => i.succ.succ)) =
      extend p r e := by
    funext z; refine Fin.cases rfl (fun i => ?_) z; exact Fin.cases rfl (fun _ => rfl) i
  simp_rw [ren_eval,eq,auxFamily_correct]
  exact ⟨fun ⟨r,hr,h⟩ => ⟨r.val,hr,h⟩,fun ⟨r,hr,h⟩ => ⟨⟨r,hr.trans (e s).isLt⟩,hr,h⟩⟩

/-- The family interface used when multiplying the half-block factors. -/
theorem auxFamily_members {n U : ℕ} (k s : Fin n) (A : HAB.Matrix U) (e : Fin n→Fin U)
    (r : Fin U) (hr : r.val<(e s).val) :
    HABCRTCoefficients.Members (auxFamily k s) A (push r e) (primeSet (e k).val (r.val+1)) := by
  intro p
  simpa only [hr,true_and] using auxFamily_correct k s A e p r

theorem odd_of_mem_primeSet {k b p : ℕ} (h : p∈primeSet k b) : Odd p := by
  obtain ⟨j,_,rfl⟩ := mem_primeSet.mp h
  exact (Nat.prime_nth_prime _).odd_of_ne_two (by
    change primeAt (b*k+j) ≠ 2
    have lo := Nat.add_two_le_nth_prime (b*k+j+1)
    change _≤primeAt (b*k+j) at lo;omega)

theorem auxSet_odd {k s p : ℕ} (h : p∈auxSet k s) : Odd p := by
  obtain ⟨_,_,hp⟩ := mem_auxSet.mp h
  exact odd_of_mem_primeSet hp

theorem aux_modulus_odd (k i : ℕ) : Odd (modulus (primeSet k (i+1))) := by
  rw [modulus,primeSet_product]; exact Nat.odd_iff.mpr (block_odd ..)

theorem aux_halves (k s : ℕ) :
    halves ((List.range s).map (fun i => modulus (primeSet k (i+1)))) = halves (blocks k s) := by
  simp only [modulus,primeSet_product,blocks]

/-- The quotient by all the auxiliary blocks, in value-prime-parameter order. -/
noncomputable def auxQuotient {n : ℕ} (L k s : Fin n) (input : Template (n+2)) : Template (n+2) :=
  graph L (auxBasis k s) input

theorem auxQuotient_correct {n U K X : ℕ} (L k s : Fin n) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (q v : Fin U) (hq : q.val∈primeSet (e k).val 0)
    (small : ∀ p∈insert q.val (auxSet (e k).val (e s).val),p≤2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U)
    (precision : let S := insert q.val (auxSet (e k).val (e s).val);
                 modulus S*budget S<2^(e L).val)
    (data : ∀ p t : Fin U, p.val∈insert q.val (auxSet (e k).val (e s).val) →
      (input.eval A (extend t p e)=true ↔ t.val=X%p.val)) :
    (auxQuotient L k s input).eval A (extend v q e)=true ↔
      v.val=(X/(blocks (e k).val (e s).val).prod)%q.val := by
  rw [auxQuotient,graph_correct L (auxBasis k s) input A e _ q v (primeSet_primes hq)
    (Finset.disjoint_left.mp (auxSet_disjoint ..) hq) (fun _ h => auxSet_primes h) small hK cap
    precision (auxBasis_members k s A e) data,auxSet_product]

end DiophantineNP.HABCRTQuotient
