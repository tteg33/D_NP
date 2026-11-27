import DiophantineNP.HABCRTDot
import DiophantineNP.HABCRTLeading

/-! # Extending a finite CRT basis by one prime

For each proposed residue at the new prime there is a unique representative
in the enlarged CRT interval. The old modulus separates the right candidate
from every other one. This file constructs the input relations used in that
comparison. -/
namespace DiophantineNP.HABCRTExtend
open Counting WidthFormula FiniteArithmeticGap HABCRTRecovery

private theorem crtCandidate {s : Finset ℕ} {q t x : ℕ} (pr : ∀ p ∈ s, Nat.Prime p)
    (hq : q.Prime) (fresh : q ∉ s) (hx : x<modulus s) (ht : t<q) :
    ∃ z, z<modulus (insert q s) ∧ modulus s < modulus (insert q s) ∧
      (∀ p ∈ insert q s, z%p=if p=q then t else x%p) ∧
      (∀ p ∈ insert q s, modulus s % p=if p=q then modulus s % p else 0) ∧
      (z<modulus s ↔ t=x%q) := by
  let m := modulus s
  have cop : m.Coprime q := Nat.coprime_prod_left_iff.mpr (by
    intro p hp
    exact (Nat.coprime_primes (pr p hp) hq).mpr (by rintro rfl; exact fresh hp))
  have hm : 0<m := Finset.prod_pos (fun p hp => (pr p hp).pos)
  have big : modulus (insert q s)=m*q := by rw [modulus,Finset.prod_insert fresh,Nat.mul_comm]; rfl
  let z := Nat.chineseRemainder cop x t
  have hz : z.val < modulus (insert q s) := big ▸ Nat.chineseRemainder_lt_mul cop x t hm.ne' hq.ne_zero
  have mb : m < modulus (insert q s) := by rw [big]; simpa using Nat.mul_lt_mul_of_pos_left hq.one_lt hm
  refine ⟨z.val,hz,mb,?_,?_,?_⟩
  · intro p hp; split
    next h => subst p; exact Eq.trans (show z.val%q=t%q from z.property.2) (Nat.mod_eq_of_lt ht)
    next h =>
      have hp' := (Finset.mem_insert.mp hp).resolve_left h
      exact z.property.1.of_dvd (Finset.dvd_prod_of_mem (fun a=>a) hp')
  · intro p hp; split
    next => rfl
    next h => exact Nat.mod_eq_zero_of_dvd (Finset.dvd_prod_of_mem (fun a=>a) ((Finset.mem_insert.mp hp).resolve_left h))
  · constructor
    · intro h
      have he := z.property.1.eq_of_lt_of_lt h hx
      exact (Nat.mod_eq_of_lt ht).symm.trans ((z.property.2.symm : t%q=z.val%q).trans (congrArg (·%q) he))
    · intro h
      have xq : x ≡ t [MOD q] := by change x%q=t%q; rw [Nat.mod_eq_of_lt ht,h]
      have eq : x=z.val := (Nat.chineseRemainder_modEq_unique cop (Nat.ModEq.refl x) xq).eq_of_lt_of_lt
        (by rw [←big]; exact hx.trans mb) (by rw [←big]; exact hz)
      simpa [←eq] using hx

def enlarged {n} (q : Fin n) (basis : Template (n+1)) : Template (n+1) :=
  .disj (.atom (.eqv 0 q.succ)) basis

theorem enlarged_correct {n U} (q : Fin n) (basis : Template (n+1)) (A : HAB.Matrix U)
    (e : Fin n → Fin U) (s : Finset ℕ)
    (sel : ∀ p : Fin U, basis.eval A (Fin.cases p e)=true ↔ p.val∈s) (p : Fin U) :
    (enlarged q basis).eval A (Fin.cases p e)=true ↔ p.val∈insert (e q).val s := by
  rw [enlarged,Tdisj_true,sel,Finset.mem_insert]
  simp [Template.eval,Atom.eval,Fin.ext_iff]

private def selectGraph {n} (q : Fin n) (fresh old : Template (n+2)) : Template (n+2) :=
  let atNew : Template (n+2) := .atom (.eqv 1 q.succ.succ)
  .disj (.conj atNew fresh) (.conj (.neg atNew) old)

private theorem selectGraph_correct {n U} (q : Fin n) (fresh old : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n → Fin U) (v p : Fin U) :
    (selectGraph q fresh old).eval A (extend v p e) =
      (if p=e q then fresh.eval A (extend v p e) else old.eval A (extend v p e)) := by
  let a := fresh.eval A (extend v p e)
  let b := old.eval A (extend v p e)
  change ((decide (p=e q) && a) || (!(decide (p=e q)) && b)) = if p=e q then a else b
  by_cases h : p=e q <;> simp [h]

private def proposed {n} (q t : Fin n) (input : Template (n+2)) : Template (n+2) :=
  selectGraph q (.atom (.eqv 0 t.succ.succ)) input

private def boundary {n} (q : Fin n) (modGraph : Template (n+2)) : Template (n+2) :=
  selectGraph q modGraph (fromFormula (isNat 0 0))

private theorem proposed_correct {n U x} (q t : Fin n) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (p v : Fin U)
    (hin : p≠e q → (input.eval A (extend v p e)=true ↔ v.val=x%p.val)) :
    (proposed q t input).eval A (extend v p e)=true ↔ v.val=if p.val=(e q).val then (e t).val else x%p.val := by
  rw [proposed,selectGraph_correct]
  by_cases h : p=e q
  · subst p; simp [Template.eval,Atom.eval,extend,Fin.ext_iff]
  · simp [h,show p.val≠(e q).val from fun he=>h (Fin.ext he),hin h]

private theorem boundary_correct {n U m} (q : Fin n) (modGraph : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (p v : Fin U)
    (hm : p=e q → (modGraph.eval A (extend v p e)=true ↔ v.val=m%p.val)) :
    (boundary q modGraph).eval A (extend v p e)=true ↔ v.val=if p.val=(e q).val then m%p.val else 0 := by
  rw [boundary,selectGraph_correct]
  by_cases h : p=e q
  · subst p; simpa using hm rfl
  · simp only [if_neg h,if_neg (show p.val≠(e q).val from fun he=>h (Fin.ext he)),fromFormula_eval,isNat_spec]; rfl

/-- The source syntax for basis extension uses two supplied formulas: comparison
on the enlarged basis, and the old basis product modulo the proposed prime. -/
def formulaWith {n} (cmp : Template (n+1) → Template (n+2) → Template (n+2) → Template n)
    (modGraph : Template (n+2)) (q t : Fin n) (basis : Template (n+1)) (input : Template (n+2)) :
    Template n :=
  let atQ := rewriteMatrix (fun r c => .entry r c) basis (Fin.cases q id)
  let supplied := rewriteMatrix (fun r c => .entry r c) input (Fin.cases t (Fin.cases q id))
  let test := cmp (enlarged q basis) (proposed q t input)
    (boundary q modGraph)
  .disj (.conj atQ supplied) (.conj (.neg atQ) (.conj (fromFormula (PrimeFormula.ltF t q)) test))

theorem formulaWith_correct {n U x} (cmp : Template (n+1) → Template (n+2) → Template (n+2) → Template n)
    (modGraph : Template (n+2)) (q t : Fin n) (basis : Template (n+1)) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n → Fin U) (s : Finset ℕ) (hp : (e q).val.Prime)
    (pr : ∀ p ∈ s, Nat.Prime p) (hx : x<modulus s) (sel : HABCRTCoefficients.Members basis A e s)
    (data : HABCRTLeading.Residues input A e s x)
    (residues : ∀ b : Fin U, modGraph.eval A (extend b (e q) e)=true ↔ b.val=modulus s%(e q).val)
    (compare : ∀ (a b : Template (n+2)) (z y : ℕ),
      z<modulus (insert (e q).val s) → y<modulus (insert (e q).val s) →
      HABCRTLeading.Residues a A e (insert (e q).val s) z →
      HABCRTLeading.Residues b A e (insert (e q).val s) y →
      ((cmp (enlarged q basis) a b).eval A e=true ↔ z<y)) :
    (formulaWith cmp modGraph q t basis input).eval A e=true ↔ (e t).val=x%(e q).val := by
  have atQ : (rewriteMatrix (fun r c => .entry r c) basis (Fin.cases q id)).eval A e = basis.eval A (Fin.cases (e q) e) := by
    rw [rewriteMatrix_eval _ A A (by intros; rfl)]
    congr 1; funext i; refine Fin.cases rfl (fun _ => rfl) i
  have rhs : (rewriteMatrix (fun r c => .entry r c) input (Fin.cases t (Fin.cases q id))).eval A e =
      input.eval A (extend (e t) (e q) e) := by
    rw [rewriteMatrix_eval _ A A (by intros; rfl)]
    congr 1; funext i; refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun _ => rfl) j
  simp only [formulaWith,Tdisj_true,Tconj_true,Template.eval.eq_4,Bool.not_eq_true',←Bool.not_eq_true,
    atQ,rhs,sel (e q),fromFormula_eval,PrimeFormula.ltF_true]
  by_cases fresh : (e q).val ∈ s
  · simp [fresh,data _ _ fresh]
  simp only [fresh,false_and,not_false_eq_true,true_and,false_or]
  by_cases ht : (e t).val < (e q).val
  · simp only [ht,true_and]
    obtain ⟨z,hz,hm,zmod,mmod,crit⟩ := crtCandidate pr hp fresh hx ht
    rw [←crit]
    apply compare _ _ z (modulus s) hz hm
    · intro p b h
      rw [zmod _ h]
      apply proposed_correct
      intro ne
      exact data _ _ ((Finset.mem_insert.mp h).resolve_left (fun he=>ne (Fin.ext he)))
    · intro p b h
      rw [mmod _ h]
      apply boundary_correct
      intro eq
      subst p
      exact residues b
  · have h := Nat.mod_lt x hp.pos
    simp only [ht,false_and,false_iff]; omega

/-- Extend the input representation to a proposed residue at q. The fixed
formula uses the original graph directly when q is already in the basis. -/
noncomputable def formula {n} (L q t : Fin n) (basis : Template (n+1)) (input : Template (n+2)) :
    Template n := formulaWith (HABCRTLeading.residueLt L) (HABCRTCoefficients.modulus basis) q t basis input

/-- HAB Lemma 4.4 on a short-prime basis in the actual formula vocabulary.
The input is the residue graph on the old basis. Every target residue test,
including construction of the old modulus on the new prime, is internal. -/
theorem formula_correct {n U K x} (L q t : Fin n) (basis : Template (n+1)) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n → Fin U) (s : Finset ℕ) (hp : (e q).val.Prime)
    (pr : ∀ p ∈ s, Nat.Prime p) (small : ∀ p ∈ insert (e q).val s, p≤2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U) (hx : x<modulus s)
    (precision : modulus (insert (e q).val s)*budget (insert (e q).val s)<2^(e L).val)
    (sel : HABCRTCoefficients.Members basis A e s)
    (data : ∀ p b : Fin U, p.val∈s → (input.eval A (extend b p e)=true ↔ b.val=x%p.val)) :
    (formula L q t basis input).eval A e=true ↔ (e t).val=x%(e q).val := by
  let S := insert (e q).val s
  have prS : ∀ p ∈ S, Nat.Prime p := by simpa [S] using And.intro hp pr
  have adm (p : Fin U) (h : p.val∈S) : HABBoundedProduct.Supported U p.val := ⟨K,hK,small _ h,cap⟩
  have fits : HABCRTCoefficients.Fits (U:=U) s := by
    intro p h
    have hle : K≤(K+1)*K := Nat.le_mul_of_pos_left _ (by omega)
    exact ((small p (Finset.mem_insert_of_mem h)).trans (Nat.pow_le_pow_right (by decide) hle)).trans_lt cap
  have selS : HABCRTCoefficients.Members (enlarged q basis) A e S :=
    enlarged_correct q basis A e s sel
  exact formulaWith_correct _ _ q t basis input A e s hp pr hx sel data
    (fun b => HABCRTCoefficients.modulus_spec basis A e s fits sel (e q) b hp
      (adm _ (Finset.mem_insert_self _ _)))
    (fun a b z y hz hy ha hb => HABCRTLeading.residueLt_correct L _ a b A e S prS small hK cap hz hy
      precision selS ha hb)

end DiophantineNP.HABCRTExtend
