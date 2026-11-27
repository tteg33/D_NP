import DiophantineNP.HABCounting
import DiophantineNP.HABCRTShift

/-! Uniform indexing of the disjoint blocks of odd primes in HAB's CRT
construction. The rank counts every prime below the candidate, even when
the candidate occupies the upper half of the universe. -/
namespace DiophantineNP.HABPrimeBlocks
open Counting WidthFormula FiniteArithmeticGap HAB ShortResidue HABCounting HABCRTShift

private def below : Predicate where
  syntaxF σ := .conj (fromFormula (PrimeFormula.prime (σ 0))) (fromFormula (PrimeFormula.ltF (σ 0) (σ 1)))
  holds _ _ e := (e 0).Prime ∧ e 0<e 1
  valid σ _ e := by simp [Tconj_true,PrimeFormula.prime_true,PrimeFormula.ltF_true]

private theorem count_below {U : ℕ} (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (hp : e 1<U) :
    cardP U t e 0 below = Nat.count Nat.Prime (e 1) := by
  classical
  rw [cardP,Nat.count_eq_card_filter_range]
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_range,below,Function.update_self,
    Function.update_of_ne (by decide : (1:ℕ)≠0)]
  constructor
  · exact fun ⟨_,h,l⟩ => ⟨l,h⟩
  · exact fun ⟨l,h⟩ => ⟨l.trans hp,h,l⟩

private def table {U : ℕ} (A : Matrix U) (r c : ℕ) : Bool :=
  if hr : r<U then if hc : c<U then A ⟨r,hr⟩ ⟨c,hc⟩ else false else false

/-- The rank of a candidate index equals the number of primes strictly below it. -/
noncomputable def primeCount {n : ℕ} (p s : Fin n) : Template n :=
  (countEqP 0 2 below).syntaxF (fun i => if i=2 then s else p)

theorem primeCount_correct {n U : ℕ} (p s : Fin n) (A : Matrix U) (e : Fin n→Fin U) :
    (primeCount p s).eval A e=true ↔ (e s).val=Nat.count Nat.Prime (e p).val := by
  have hA : A = fun r c : Fin U => table A r.val c.val := by funext r c; simp [table,r.isLt,c.isLt]
  conv_lhs => rw [hA]
  rw [primeCount,Predicate.valid]
  change (e s).val=cardP _ _ _ 0 below ↔ _
  rw [count_below _ _ (e p).isLt]
  rfl

/-- The odd prime at zero-based index i. The first such prime is 3. -/
noncomputable def oddPrimeAt {n : ℕ} (p i : Fin n) : Template n :=
  .conj (fromFormula (PrimeFormula.prime p)) (.ex (.conj (primeCount p.succ 0)
      (.ex (.conj (fromFormula (isNat 1 0)) (.atom (.add i.succ.succ 0 1))))))

theorem oddPrimeAt_correct {n U : ℕ} (p i : Fin n) (A : Matrix U) (e : Fin n→Fin U) :
    (oddPrimeAt p i).eval A e=true ↔ (e p).val=primeAt (e i).val := by
  simp only [oddPrimeAt,Tconj_true,fromFormula_eval,PrimeFormula.prime_true,Tex_true,
    primeCount_correct,Fin.cases_zero,Fin.cases_succ,isNat_spec,Template.eval.eq_1,Atom.eval,decide_eq_true_eq]
  change (_ ∧ ∃ r : Fin U, r.val=Nat.count Nat.Prime (e p).val ∧ ∃ one : Fin U,
      one.val=1 ∧ (e i).val+one.val=r.val) ↔ _
  constructor
  · rintro ⟨hp,r,hr,one,h1,he⟩
    have rank : (e i).val+1=Nat.count Nat.Prime (e p).val := by omega
    rw [primeAt,rank,Nat.nth_count hp]
  · intro he
    have hp := (Nat.prime_nth_prime ((e i).val+1))
    have count := Nat.count_nth_of_infinite Nat.infinite_setOf_prime ((e i).val+1)
    change (e p).val=Nat.nth Nat.Prime ((e i).val+1) at he
    rw [←he] at hp count
    have hr := (Nat.count_le Nat.Prime (n:=(e p).val)).trans_lt (e p).isLt
    have h1 := hp.two_le.trans_lt (e p).isLt
    exact ⟨hp,⟨_,hr⟩,rfl,⟨1,by omega⟩,rfl,count.symm⟩

/-- Position j in block t of width k. The witness registers never need
to contain the right endpoint (t+1)*k, which can lie outside the universe. -/
noncomputable def blockEntry {n : ℕ} (k t j p : Fin n) : Template n :=
  .conj (fromFormula (PrimeFormula.ltF j k)) (.ex (.conj (.atom (.mul t.succ k.succ 0))
    (.ex (.conj (.atom (.add 1 j.succ.succ 0)) (oddPrimeAt p.succ.succ 0)))))

theorem blockEntry_correct {n U : ℕ} (k t j p : Fin n) (A : Matrix U) (e : Fin n→Fin U) :
    (blockEntry k t j p).eval A e=true ↔
      (e j).val<(e k).val ∧ (e p).val=primeAt ((e t).val*(e k).val+(e j).val) := by
  simp only [blockEntry,Tconj_true,Tex_true,fromFormula_eval,PrimeFormula.ltF_true,
    oddPrimeAt_correct,Template.eval.eq_1,Atom.eval,decide_eq_true_eq,Fin.cases_zero,Fin.cases_succ]
  change (_ ∧ ∃ base : Fin U, (e t).val*(e k).val=base.val ∧ ∃ idx : Fin U,
    base.val+(e j).val=idx.val ∧ (e p).val=primeAt idx.val) ↔ _
  constructor
  · rintro ⟨hj,b,hb,i,hi,hp⟩
    exact ⟨hj,by rw [hb,hi,hp]⟩
  · rintro ⟨hj,hp⟩
    have bound := Nat.add_two_le_nth_prime ((e t).val*(e k).val+(e j).val+1)
    change _≤primeAt ((e t).val*(e k).val+(e j).val) at bound
    rw [←hp] at bound
    have within := (e p).isLt
    exact ⟨hj,⟨(e t).val*(e k).val,by omega⟩,rfl,
      ⟨(e t).val*(e k).val+(e j).val,by omega⟩,rfl,hp⟩

/-- Membership in an entire CRT block, with variable width and block number. -/
noncomputable def blockMember {n : ℕ} (k t p : Fin n) : Template n :=
  .ex (blockEntry k.succ t.succ 0 p.succ)

theorem blockMember_correct {n U : ℕ} (k t p : Fin n) (A : Matrix U) (e : Fin n→Fin U) :
    (blockMember k t p).eval A e=true ↔
      ∃ j<(e k).val, (e p).val=primeAt ((e t).val*(e k).val+j) := by
  simp only [blockMember,Tex_true,blockEntry_correct,Fin.cases_succ,Fin.cases_zero]
  exact ⟨fun ⟨j,hj,he⟩ => ⟨j.val,hj,he⟩,fun ⟨j,hj,he⟩ => ⟨⟨j,hj.trans (e k).isLt⟩,hj,he⟩⟩

/-- As an interval test on the ordinary prime rank, the two endpoints are
shifted by one to skip the prime 2. Neither endpoint is a formula register. -/
theorem blockMember_by_rank {n U : ℕ} (k t p : Fin n) (A : Matrix U) (e : Fin n→Fin U) :
    (blockMember k t p).eval A e=true ↔ (e p).val.Prime ∧
    (e t).val*(e k).val + 1 ≤ Nat.count Nat.Prime (e p).val ∧
    Nat.count Nat.Prime (e p).val < ((e t).val+1)*(e k).val+1 := by
  rw [blockMember_correct,Nat.add_mul,one_mul]
  constructor
  · rintro ⟨j,hj,he⟩
    rw [he,primeAt,Nat.count_nth_of_infinite Nat.infinite_setOf_prime]
    exact ⟨Nat.prime_nth_prime _,by omega,by omega⟩
  · rintro ⟨hp,hl,hr⟩
    let j := Nat.count Nat.Prime (e p).val - ((e t).val*(e k).val+1)
    have eq : (e t).val*(e k).val+j+1=Nat.count Nat.Prime (e p).val := by dsimp [j]; omega
    exact ⟨j,by dsimp [j]; omega,by rw [primeAt,eq,Nat.nth_count hp]⟩

/-- The finite set used as the CRT basis for one block. -/
noncomputable def primeSet (k t : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun j => primeAt (t*k+j))

theorem mem_primeSet {k t p : ℕ} : p∈primeSet k t ↔ ∃ j<k, p=primeAt (t*k+j) := by
  simp [primeSet,eq_comm]

theorem blockMember_mem {n U : ℕ} (k t p : Fin n) (A : Matrix U) (e : Fin n→Fin U) :
    (blockMember k t p).eval A e=true ↔ (e p).val ∈ primeSet (e k).val (e t).val := by
  rw [blockMember_correct,mem_primeSet]

private theorem index_inj (k t : ℕ) : Function.Injective (fun j => primeAt (t*k+j)) := by
  intro a b hab
  have h := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hab
  omega

theorem primeSet_card (k t : ℕ) : (primeSet k t).card=k := by
  rw [primeSet,Finset.card_image_of_injective _ (index_inj k t),Finset.card_range]

theorem primeSet_primes {k t p : ℕ} (h : p∈primeSet k t) : p.Prime := by
  obtain ⟨j,_,rfl⟩ := mem_primeSet.mp h
  exact Nat.prime_nth_prime _

theorem primeSet_product (k t : ℕ) : (∏ p ∈ primeSet k t,p)=block k t := by
  rw [primeSet,Finset.prod_image (fun _ _ _ _ he => index_inj k t he)]
  rfl

theorem primeSet_disjoint {t v : ℕ} (k : ℕ) (h : t≠v) :
    Disjoint (primeSet k t) (primeSet k v) := by
  apply Finset.disjoint_left.mpr
  intro p ht hv
  exact (primeSet_primes ht).not_dvd_one <|
    ((Nat.dvd_gcd ((primeSet_product k t) ▸ Finset.dvd_prod_of_mem (fun p => p) ht)
      ((primeSet_product k v) ▸ Finset.dvd_prod_of_mem (fun p => p) hv)).trans
      ((blocks_coprime (k:=k) h).gcd_eq_one ▸ dvd_refl _))

end DiophantineNP.HABPrimeBlocks
