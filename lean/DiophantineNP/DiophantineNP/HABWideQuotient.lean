import DiophantineNP.HABWideExtend
import DiophantineNP.HABCRTQuotient
import DiophantineNP.HABCRTNumerator

/-! # Upper-scale quotient and geometric shift in CRT coordinates

The division and half-block constructions use the short-product interface to
support every prime whose cube fits in the interpretation domain.
-/
namespace DiophantineNP.HABWideQuotient
open Counting WidthFormula PrimeFormula FiniteArithmeticGap HABCRTRecovery
open HABCRTQuotient (assemble assemble_correct remainder_on_basis auxBasis auxBasis_members
  auxSet auxSet_primes auxSet_odd auxSet_disjoint mem_auxSet auxFamily auxFamily_members
  odd_of_mem_primeSet auxSet_product aux_modulus_odd)
open HABPrimeBlocks HABCRTShift
open HABPowerReduction (ShortProducts)

private def ren {a k : ℕ} (p : Template a) (f : Fin a→Fin k) : Template k :=
  rewriteMatrix (fun i j => .entry i j) p f

private theorem ren_eval {a k U : ℕ} (p : Template a) (f : Fin a→Fin k)
    (A : HAB.Matrix U) (e : Fin k→Fin U) : (ren p f).eval A e=p.eval A (e ∘ f) :=
  rewriteMatrix_eval _ A A (by intros; rfl) _ _ _

private abbrev push {k U : ℕ} (z : Fin U) (e : Fin k→Fin U) : Fin (k+1)→Fin U := Fin.cases z e

private theorem basis_coprime {s : Finset ℕ} {q : ℕ} (hq : q.Prime) (fresh : q∉s)
    (primes : ∀ p∈s, Nat.Prime p) : q.Coprime (modulus s) :=
  (Nat.coprime_prod_left_iff.mpr (fun p hp => (Nat.coprime_primes (primes p hp) hq).mpr
    (fun eq => fresh (eq ▸ hp)))).symm

private def extraBasis {n : ℕ} (basis : Template (n+1)) : Template ((n+2)+1) :=
  ren basis (Fin.cases 0 (fun i => i.succ.succ.succ))

private def extraInput {n : ℕ} (input : Template (n+2)) : Template ((n+2)+2) :=
  ren input (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ.succ)))

/-- Reconstruct the remainder modulo B at the query prime. The input graph is
used only on the divisor basis, where X and X % B have equal residues. -/
noncomputable def remainder (ops : ShortProducts) {n : ℕ} (L : Fin n) (basis : Template (n+1)) (input : Template (n+2)) :
    Template (n+2) :=
  HABWideExtend.formula ops L.succ.succ 1 0 (extraBasis basis) (extraInput input)

theorem remainder_correct (ops : ShortProducts) {n U X : ℕ} (L : Fin n) (basis : Template (n+1)) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ) (q b : Fin U) (hp : q.val.Prime)
    (primes : ∀ p∈s,Nat.Prime p) (size : ∀ p∈insert q.val s,p^3<U)
    (precision : modulus (insert q.val s)*budget (insert q.val s)<2^(e L).val)
    (sel : HABCRTCoefficients.Members basis A e s)
    (data : ∀ p v : Fin U, p.val∈s → (input.eval A (extend v p e)=true ↔ v.val=X%p.val)) :
    (remainder ops L basis input).eval A (extend b q e)=true ↔ b.val=(X%modulus s)%q.val := by
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
  exact HABWideExtend.formula_correct ops L.succ.succ 1 0 (extraBasis basis) (extraInput input) A
    (extend b q e) s hp primes size (Nat.mod_lt X (Finset.prod_pos (fun p h => (primes p h).pos)))
    precision smem sdata

/-- Quotient of an unrestricted nonnegative integer by the product of the
selected basis primes. Its only input is the dividend's residue graph. -/
noncomputable def formula (ops : ShortProducts) {n : ℕ} (L q t : Fin n) (basis : Template (n+1)) (input : Template (n+2)) :
    Template n :=
  assemble q t (HABWideCoefficients.modulus ops basis) (remainder ops L basis input) input

/-- The field test works for every query prime coprime to the divisor and every
candidate. The assumptions concern the prime basis, precision and source residues.
The dividend, divisor, and quotient may all be larger than the entire universe. -/
theorem formula_correct (ops : ShortProducts) {n U X : ℕ} (L q t : Fin n) (basis : Template (n+1)) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ) (hp : (e q).val.Prime) (fresh : (e q).val∉s)
    (primes : ∀ p∈s,Nat.Prime p) (size : ∀ p∈insert (e q).val s,p^3<U)
    (precision : modulus (insert (e q).val s)*budget (insert (e q).val s)<2^(e L).val)
    (sel : HABCRTCoefficients.Members basis A e s)
    (data : ∀ p v : Fin U, p.val∈insert (e q).val s →
      (input.eval A (extend v p e)=true ↔ v.val=X%p.val)) :
    (formula ops L q t basis input).eval A e=true ↔ (e t).val=(X/modulus s)%(e q).val := by
  have ok := size (e q).val (Finset.mem_insert_self ..)
  have fits : HABCRTCoefficients.Fits (U:=U) s := fun p h =>
    (Nat.le_self_pow (by decide : 3≠0) p).trans_lt (size p (Finset.mem_insert_of_mem h))
  have sq : (e q).val^2≤U :=
    (Nat.pow_le_pow_right hp.pos (by decide : 2≤3)).trans ok.le
  exact assemble_correct q t _ _ input A e hp.pos (basis_coprime hp fresh primes) sq
    (fun v => HABWideCoefficients.modulus_spec ops basis A e s fits sel (e q) v hp ok)
    (fun v => remainder_correct ops L basis input A e s (e q) v hp primes size precision sel
      (fun p z h => data p z (Finset.mem_insert_of_mem h)))
    (fun v => data (e q) v (Finset.mem_insert_self ..))

/-- The quotient as a reusable residue graph. Slots zero and one are the
proposed value and target prime. All source parameters follow unchanged. -/
noncomputable def graph (ops : ShortProducts) {n : ℕ} (L : Fin n) (basis : Template (n+1)) (input : Template (n+2)) :
    Template (n+2) := formula ops L.succ.succ 1 0 (extraBasis basis) (extraInput input)

theorem graph_correct (ops : ShortProducts) {n U X : ℕ} (L : Fin n) (basis : Template (n+1)) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ) (q t : Fin U) (hp : q.val.Prime) (fresh : q.val∉s)
    (primes : ∀ p∈s,Nat.Prime p) (size : ∀ p∈insert q.val s,p^3<U)
    (precision : modulus (insert q.val s)*budget (insert q.val s)<2^(e L).val)
    (sel : HABCRTCoefficients.Members basis A e s)
    (data : ∀ p v : Fin U, p.val∈insert q.val s →
      (input.eval A (extend v p e)=true ↔ v.val=X%p.val)) :
    (graph ops L basis input).eval A (extend t q e)=true ↔ t.val=(X/modulus s)%q.val := by
  apply formula_correct ops L.succ.succ 1 0 _ _ A (extend t q e) s hp fresh primes size precision
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

/-- The quotient by all the auxiliary blocks, in value-prime-parameter order. -/
noncomputable def auxQuotient (ops : ShortProducts) {n : ℕ} (L k s : Fin n) (input : Template (n+2)) : Template (n+2) :=
  graph ops L (auxBasis k s) input

theorem auxQuotient_correct (ops : ShortProducts) {n U X : ℕ} (L k s : Fin n) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (q v : Fin U) (hq : q.val∈primeSet (e k).val 0)
    (size : ∀ p∈insert q.val (auxSet (e k).val (e s).val),p^3<U)
    (precision : let S := insert q.val (auxSet (e k).val (e s).val);
                 modulus S*budget S<2^(e L).val)
    (data : ∀ p t : Fin U, p.val∈insert q.val (auxSet (e k).val (e s).val) →
      (input.eval A (extend t p e)=true ↔ t.val=X%p.val)) :
    (auxQuotient ops L k s input).eval A (extend v q e)=true ↔
      v.val=(X/(blocks (e k).val (e s).val).prod)%q.val := by
  rw [auxQuotient,graph_correct ops L (auxBasis k s) input A e _ q v (primeSet_primes hq)
    (Finset.disjoint_left.mp (auxSet_disjoint ..) hq) (fun _ h => auxSet_primes h) size
    precision (auxBasis_members k s A e) data,auxSet_product]

/-- A reusable residue graph of the preliminary binary shift. The query slots
are the candidate field value, its prime, then the ambient parameters. -/
noncomputable def estimateGraph (ops : ShortProducts) {n : ℕ} (L k s : Fin n) (input : Template (n+2)) : Template (n+2) :=
  auxQuotient ops L k s (HABWideCoefficients.numerator ops s (auxFamily k s) input)

theorem estimateGraph_correct (ops : ShortProducts) {n U X : ℕ} (L k s : Fin n) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (q v : Fin U) (hq : q.val∈primeSet (e k).val 0)
    (size : ∀ p∈insert q.val (auxSet (e k).val (e s).val),p^3<U)
    (precision : let S := insert q.val (auxSet (e k).val (e s).val);
                 modulus S*budget S<2^(e L).val)
    (data : ∀ p t : Fin U, p.val∈insert q.val (auxSet (e k).val (e s).val) →
      (input.eval A (extend t p e)=true ↔ t.val=X%p.val)) :
    (estimateGraph ops L k s input).eval A (extend v q e)=true ↔
      v.val=estimate X (blocks (e k).val (e s).val)%q.val := by
  have fits (i : Fin U) (hi : i.val<(e s).val) : HABCRTCoefficients.Fits (U:=U) (primeSet (e k).val (i.val+1)) := by
    intro p hp
    exact (Nat.le_self_pow (by decide : 3≠0) p).trans_lt
      (size p (Finset.mem_insert_of_mem (mem_auxSet.mpr ⟨i.val,hi,hp⟩)))
  apply auxQuotient_correct ops L k s _ A e q v hq size precision
  intro p t hm
  have pp : p.val.Prime ∧ Odd p.val := by
    rcases Finset.mem_insert.mp hm with eq|hp
    · rw [eq]; exact ⟨primeSet_primes hq,odd_of_mem_primeSet hq⟩
    · exact ⟨auxSet_primes hp,auxSet_odd hp⟩
  have hn := HABWideCoefficients.numerator_spec ops s (auxFamily k s) input A e (fun i => primeSet (e k).val (i+1))
    X p t pp.1 pp.2 (size p.val hm) fits (fun i hi => auxFamily_members k s A e i hi)
    (fun i _ => aux_modulus_odd _ i.val) (fun v => data p v hm)
  rwa [HABCRTNumerator.prime_halfProduct] at hn

end DiophantineNP.HABWideQuotient
