import DiophantineNP.HABCRTQuotient
import DiophantineNP.HABCRTNumerator

/-! # Residues of the preliminary binary-shift quotient

All the multiplications by half-block factors and the subsequent exact integer
division run inside the fixed template. The input provides residues only of the
original X, before rescaling.
-/
namespace DiophantineNP.HABCRTEstimate
open Counting WidthFormula FiniteArithmeticGap HABCRTRecovery HABPrimeBlocks HABCRTQuotient HABCRTShift

/-- A reusable residue graph of the preliminary binary shift. The query slots
are the candidate field value, its prime, then the ambient parameters. -/
noncomputable def estimateGraph {n : ℕ} (L k s : Fin n) (input : Template (n+2)) : Template (n+2) :=
  auxQuotient L k s (HABCRTNumerator.numerator s (auxFamily k s) input)

theorem estimateGraph_correct {n U K X : ℕ} (L k s : Fin n) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (q v : Fin U) (hq : q.val∈primeSet (e k).val 0)
    (small : ∀ p∈insert q.val (auxSet (e k).val (e s).val),p≤2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U)
    (precision : let S := insert q.val (auxSet (e k).val (e s).val);
                 modulus S*budget S<2^(e L).val)
    (data : ∀ p t : Fin U, p.val∈insert q.val (auxSet (e k).val (e s).val) →
      (input.eval A (extend t p e)=true ↔ t.val=X%p.val)) :
    (estimateGraph L k s input).eval A (extend v q e)=true ↔
      v.val=estimate X (blocks (e k).val (e s).val)%q.val := by
  have hle : 2^K ≤ 2^((K+1)*K) := Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left K (by omega))
  have fits (i : Fin U) (hi : i.val<(e s).val) : HABCRTCoefficients.Fits (U:=U) (primeSet (e k).val (i.val+1)) := by
    intro p hp
    exact ((small p (Finset.mem_insert_of_mem (mem_auxSet.mpr ⟨i.val,hi,hp⟩))).trans hle).trans_lt cap
  apply auxQuotient_correct L k s _ A e q v hq small hK cap precision
  intro p t hm
  have pp : p.val.Prime ∧ Odd p.val := by
    rcases Finset.mem_insert.mp hm with eq|hp
    · rw [eq]; exact ⟨primeSet_primes hq,odd_of_mem_primeSet hq⟩
    · exact ⟨auxSet_primes hp,auxSet_odd hp⟩
  have hn := HABCRTNumerator.numerator_spec s (auxFamily k s) input A e (fun i => primeSet (e k).val (i+1))
    X p t pp.1 pp.2 ⟨K,hK,small p.val hm,cap⟩ fits (fun i hi => auxFamily_members k s A e i hi)
    (fun i _ => aux_modulus_odd _ i.val) (fun v => data p v hm)
  rwa [HABCRTNumerator.prime_halfProduct] at hn

end DiophantineNP.HABCRTEstimate
