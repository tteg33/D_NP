import DiophantineNP.HABCRTExtend
import DiophantineNP.HABLargePrimeRow
import DiophantineNP.HABWideCoefficients

/-! Comparison and one-prime extension of a CRT representation using the
upper-scale modular-power construction. Only the ordinary cubic workspace
for arithmetic on individual primes is required. -/
namespace DiophantineNP.HABWideExtend
open Counting WidthFormula FiniteArithmeticGap HAB HABPowerReduction
open HABCRTRecovery (modulus budget inverse coeff)
open HABCRTCoefficients (Members Fits)
open HABCRTLeading (Residues)

private noncomputable def power (ops : ShortProducts) {n : ℕ} (j p b : Fin n) : Template n :=
  HABLargePrimeRow.weight (primePOW ops) j p b

private theorem power_correct (ops : ShortProducts) {n U : ℕ} (j p b : Fin n) (A : Matrix U)
    (e : Fin n→Fin U) (hp : (e p).val.Prime) :
    (power ops j p b).eval A e=true ↔ (e b).val=2^(e j).val%(e p).val :=
  HABLargePrimeRow.weight_spec (primePOW ops) j p b A e (primePOW_correct ops A) hp

/-- The reciprocal row for any represented prime, including two. -/
noncomputable def reciprocalCells (ops : ShortProducts) {n : ℕ} (L : Fin n) : Template (n+2) :=
  HABCRTDot.reciprocalCellsWith (@power ops) L

theorem reciprocalCells_correct (ops : ShortProducts) {n U : ℕ} (L : Fin n) (A : Matrix U)
    (e : Fin n→Fin U) (p c : Fin U) (hp : p.val.Prime) :
    (reciprocalCells ops L).eval A (extend c p e)=(2^(e L).val/p.val).testBit c.val := by
  apply HABCRTDot.reciprocalCellsWith_correct (@power ops) L A e p c hp
  intro m j p' b E he
  rw [←he]; exact power_correct ops _ _ _ _ _ (he ▸ hp)

private theorem cubeFits {p U : ℕ} (h : p^3<U) : p<U := by
  cases p with
  | zero => simpa using h
  | succ q => exact (Nat.le_self_pow (by decide : 3≠0) (q+1)).trans_lt h

/-- Graph for the residue of an index multiplied by an arbitrary binary shift. -/
noncomputable def scaledResidue (ops : ShortProducts) {n : ℕ} (q s p b : Fin n) : Template n :=
  .ex (.conj (fromFormula (WidthPrimeResidue.remainder q.succ p.succ 0))
    (.ex (.conj (power ops s.succ.succ p.succ.succ 0)
      (.ex (.conj (.atom (.mul 2 1 0)) (fromFormula (WidthPrimeResidue.remainder 0 p.succ.succ.succ b.succ.succ.succ)))))))

theorem scaledResidue_correct (ops : ShortProducts) {n U : ℕ} (q s p b : Fin n)
    (A : Matrix U) (e : Fin n→Fin U) (prime : (e p).val.Prime) (size : (e p).val^3<U) :
    (scaledResidue ops q s p b).eval A e=true ↔ (e b).val=(e q).val*2^(e s).val%(e p).val := by
  let P := (e p).val
  have hpow (r v : Fin U) : (power ops s.succ.succ p.succ.succ 0).eval A (extend v r e)=true ↔
      v.val=2^(e s).val%P := power_correct ops _ _ _ A _ prime
  have hrem (r : Fin U) : (WidthPrimeResidue.remainder q.succ p.succ 0).eval (Fin.cases r e)=true ↔
      r.val=(e q).val%P := by
    let E : Fin (n+1)→Fin U := Fin.cases r e
    exact WidthPrimeResidue.rem_true q.succ p.succ 0 E prime.pos
  have hlast (r v m : Fin U) : (WidthPrimeResidue.remainder 0 p.succ.succ.succ b.succ.succ.succ).eval
      (Fin.cases m (extend v r e))=true ↔ (e b).val=m.val%P := by
    let E : Fin (n+3)→Fin U := Fin.cases m (extend v r e)
    exact WidthPrimeResidue.rem_true 0 p.succ.succ.succ b.succ.succ.succ E prime.pos
  simp only [scaledResidue,Tex_true,Tconj_true,fromFormula_eval,hrem]
  change (∃ r : Fin U, r.val=(e q).val%P ∧ ∃ v : Fin U, (power ops _ _ _).eval A (extend v r e)=true ∧
    ∃ m : Fin U, decide (r.val*v.val=m.val)=true ∧ _) ↔ _
  simp only [hpow,decide_eq_true_eq,hlast]
  have mixed := Nat.mul_mod (e q).val (2^(e s).val) P
  constructor
  · rintro ⟨r,hr,v,hv,m,hm,h⟩
    rw [←hm,hr,hv,←mixed] at h; exact h
  · intro h
    have hr := Nat.mod_lt (e q).val prime.pos
    have hv := Nat.mod_lt (2^(e s).val) prime.pos
    have pfit := (e p).isLt
    have pp : P*P≤P^3 := by rw [←pow_two]; exact Nat.pow_le_pow_right prime.pos (by decide)
    have hm := ((Nat.mul_le_mul hr.le hv.le).trans pp).trans_lt size
    exact ⟨⟨_,hr.trans pfit⟩,rfl,⟨_,hv.trans pfit⟩,rfl,⟨_,hm⟩,rfl,h.trans mixed⟩

/-- Compare canonical representatives supplied as arbitrary residue graphs. -/
noncomputable def residueLt (ops : ShortProducts) {n : ℕ} (L : Fin n) (basis : Template (n+1))
    (a b : Template (n+2)) : Template n :=
  .conj (.ex basis) (HABCRTDot.crtLt (HABCRTDot.cutoff L) basis
    (HABCRTDot.graphBits (HABWideCoefficients.coefficient ops basis a))
    (HABCRTDot.graphBits (HABWideCoefficients.coefficient ops basis b)) (reciprocalCells ops L))

theorem residueLt_correct (ops : ShortProducts) {n U x y : ℕ} (L : Fin n) (basis : Template (n+1))
    (a b : Template (n+2)) (A : Matrix U) (e : Fin n→Fin U) (s : Finset ℕ)
    (primes : ∀ p∈s, p.Prime) (size : ∀ p∈s, p^3<U) (hx : x<modulus s) (hy : y<modulus s)
    (precise : modulus s*budget s<2^(e L).val) (sel : Members basis A e s)
    (ha : Residues a A e s x) (hb : Residues b A e s y) :
    (residueLt ops L basis a b).eval A e=true ↔ x<y := by
  have fits : Fits (U:=U) s := fun _ h => cubeFits (size _ h)
  simp only [residueLt,Tconj_true,Tex_true,sel]
  by_cases nonempty : s.Nonempty
  · obtain ⟨r,hr⟩ := nonempty
    have hU := (primes _ hr).two_le.trans (fits r hr).le
    rw [and_iff_right (show ∃ p : Fin U, p.val∈s from ⟨⟨r,fits r hr⟩,hr⟩)]
    have bits (z : ℕ) (g : Template (n+2)) (hg : Residues g A e s z) (p c : Fin U) (hp : p.val∈s) :
        (HABCRTDot.graphBits (HABWideCoefficients.coefficient ops basis g)).eval A (extend c p e) =
        (coeff (inverse s) z p.val).testBit c.val := by
      apply HABCRTDot.graphBits_correct
      · exact (Nat.mod_lt _ (primes _ hp).pos).trans p.isLt
      · intro v
        exact HABWideCoefficients.coefficient_spec ops basis g A e s fits sel p v (primes _ hp) (size _ hp) z
          (fun b => hg p b hp)
    exact HABCRTDot.crtLt_correct _ _ _ _ _ A e s (inverse s) hU fits (e L).isLt.le primes
      (fun _ hp => HABCRTRecovery.inverse_spec primes hp) hx hy precise (HABCRTDot.cutoff_correct L A e)
      sel (bits x a ha) (bits y b hb) (fun p c hp => reciprocalCells_correct ops L A e p c (primes _ hp))
  · obtain rfl : s=∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    simp [modulus] at hx hy
    simp [hx,hy]

/-- Check the proposed additional residue using a CRT comparison on the expanded basis. -/
noncomputable def formula (ops : ShortProducts) {n} (L q t : Fin n) (basis : Template (n+1))
    (input : Template (n+2)) : Template n :=
  HABCRTExtend.formulaWith (residueLt ops L) (HABWideCoefficients.modulus ops basis) q t basis input

theorem formula_correct (ops : ShortProducts) {n U x} (L q t : Fin n) (basis : Template (n+1))
    (input : Template (n+2)) (A : Matrix U) (e : Fin n→Fin U) (s : Finset ℕ) (hp : (e q).val.Prime)
    (pr : ∀ p∈s, p.Prime) (size : ∀ p∈insert (e q).val s, p^3<U) (hx : x<modulus s)
    (precision : modulus (insert (e q).val s)*budget (insert (e q).val s)<2^(e L).val)
    (sel : Members basis A e s) (data : Residues input A e s x) :
    (formula ops L q t basis input).eval A e=true ↔ (e t).val=x%(e q).val := by
  have fits : Fits (U:=U) s := fun _ h => cubeFits (size _ (Finset.mem_insert_of_mem h))
  have prS : ∀ p∈insert (e q).val s, p.Prime := by simpa using And.intro hp pr
  exact HABCRTExtend.formulaWith_correct _ _ q t basis input A e s hp pr hx sel data
    (fun b => HABWideCoefficients.modulus_spec ops basis A e s fits sel (e q) b hp
      (size _ (Finset.mem_insert_self _ _)))
    (fun a b z y hz hy ha hb => residueLt_correct ops L _ a b A e _ prS size hz hy precision
      (HABCRTExtend.enlarged_correct q basis A e s sel) ha hb)

end DiophantineNP.HABWideExtend
