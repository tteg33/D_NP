import DiophantineNP.HABCRTDot
import DiophantineNP.HABPrimeBlocks
import DiophantineNP.HABCRTCoefficients

/-! Reading a representable leading quotient of a CRT word by comparing
against the two adjacent multiples c*2^j and (c+1)*2^j. -/
namespace DiophantineNP.HABCRTLeading
open Counting WidthFormula FiniteArithmeticGap HAB HABBinaryResidue ShortResidue

private def bumpR (up : Bool) : Predicate where
  syntaxF σ := if up then .ex (.conj (fromFormula (isNat 1 0))
    (.atom (.add (σ 4).succ 0 (σ 5).succ))) else .atom (.eqv (σ 4) (σ 5))
  holds _ _ e := e 5=e 4+up.toNat
  valid σ t e := by
    cases up
    · simp [Template.eval,Atom.eval,Fin.ext_iff,eq_comm]
    · simp only [Bool.toNat_true,if_true,Tex_true,Tconj_true,fromFormula_eval,
        isNat_spec,Fin.cases_zero,Template.eval.eq_1,Atom.eval,decide_eq_true_eq,Fin.cases_succ]
      constructor
      · rintro ⟨i,h1,h⟩; omega
      · intro h
        have hb := (e (σ 5)).isLt
        exact ⟨⟨1,by omega⟩,rfl,h.symm⟩

private def shifted (up : Bool) : Predicate :=
  Predicate.ex 4 <| Predicate.ex 5 <| Predicate.ex 6 <| Predicate.ex 7 <|
    (modulo 2 0 4).both <| (bumpR up).both <|
    (powerAtPosition 1 6).both <| (Predicate.mul 5 6 7).both (modulo 7 0 3)

private theorem shifted_spec (up : Bool) {U K : ℕ} (t : ℕ→ℕ→Bool) (e : ℕ→ℕ)
    (hp : (e 0).Prime) (hpU : e 0<U) (hj : e 1<U) (hK : 2≤K) (hpk : e 0≤2^K)
    (hc : 2^((K+1)*K)<U) :
    (shifted up).holds U t e ↔ e 3=(e 2+up.toNat)*2^(e 1)%(e 0) := by
  let H (a b v w : ℕ) := Function.update (Function.update (Function.update (Function.update e 4 a) 5 b) 6 v) 7 w
  have powers (a b v w : ℕ) (hv : v<U) :
      (powerAtPosition 1 6).holds U t (H a b v w) ↔ v=2^(e 1)%e 0 := by
    apply powerAtPosition_spec t (H a b v w) 1 6 (by decide) (by decide) rfl hp hpU hj hv hK hpk hc
  change (∃ a<U, ∃ b<U, ∃ v<U, ∃ w<U,
    (0<e 0 ∧ a=e 2%e 0) ∧ b=a+up.toNat ∧ (powerAtPosition 1 6).holds U t (H a b v w) ∧
    b*v=w ∧ 0<e 0 ∧ e 3=w%e 0) ↔ _
  have eq : ((e 2%e 0 + up.toNat)*(2^(e 1)%e 0)) % e 0 = (e 2+up.toNat)*2^(e 1)%e 0 := by
    have first := (Nat.mod_modEq (e 2) (e 0)).add (Nat.ModEq.refl up.toNat)
    exact first.mul (Nat.mod_modEq _ _)
  constructor
  · rintro ⟨a,_,b,_,v,hv,w,_,⟨_,rfl⟩,rfl,hp',rfl,_,he⟩
    rw [(powers _ _ _ _ hv).mp hp'] at he
    exact he.trans eq
  · intro out
    let a := e 2%e 0
    let v := 2^(e 1)%e 0
    have ha : a<e 0 := Nat.mod_lt _ hp.pos
    have hv : v<e 0 := Nat.mod_lt _ hp.pos
    have ub : up.toNat≤1 := by cases up <;> decide
    have hb : a+up.toNat≤e 0 := by omega
    have cap := (square_fits hK hpk hc).trans_le (Nat.sub_le U (U/2))
    have hw := (Nat.mul_le_mul hb hv.le).trans_lt cap
    exact ⟨a,ha.trans hpU,_,hb.trans_lt hpU,v,hv.trans hpU,_,hw,⟨hp.pos,rfl⟩,rfl,
      (powers _ _ _ _ (hv.trans hpU)).mpr rfl,rfl,hp.pos,out.trans eq.symm⟩

/-- The residue of the lower or upper threshold. The upper threshold also
works at c=U−1, since its successor is taken after reducing modulo p. -/
def thresholdResidue {n : ℕ} (up : Bool) (c j p r : Fin n) : Template n :=
  (shifted up).syntaxF (fun i => if i=0 then p else if i=1 then j else if i=2 then c else r)

theorem thresholdResidue_correct {n U K : ℕ} (up : Bool) (c j p r : Fin n)
    (A : Matrix U) (e : Fin n→Fin U) (hp : (e p).val.Prime) (hK : 2≤K)
    (hpk : (e p).val≤2^K) (hc : 2^((K+1)*K)<U) :
    (thresholdResidue up c j p r).eval A e=true ↔
    (e r).val=((e c).val+up.toNat)*2^(e j).val%(e p).val := by
  let T (a b : ℕ) := if h : a<U ∧ b<U then A ⟨a,h.1⟩ ⟨b,h.2⟩ else false
  have ht : A=fun r c => T r.val c.val := by funext r c; simp [T,r.isLt,c.isLt]
  rw [ht,thresholdResidue,Predicate.valid _ _ T,shifted_spec up T _ hp (e p).isLt (e j).isLt hK hpk hc]
  rfl


open HABCRTCoefficients (Members Fits)
open HABCRTRecovery (modulus budget coeff inverse)

abbrev Residues {n U : ℕ} (a : Template (n+2)) (A : Matrix U) (e : Fin n→Fin U)
    (s : Finset ℕ) (x : ℕ) := ∀ p b : Fin U, p.val∈s →
      (a.eval A (extend b p e)=true ↔ b.val=x%p.val)

/-- Compare arbitrary CRT residue graphs. Every coefficient, inverse, reciprocal
and bias used by the comparison is computed in the fixed formula. -/
noncomputable def residueLt {n : ℕ} (L : Fin n) (basis : Template (n+1))
    (a b : Template (n+2)) : Template n :=
  HABCRTDot.primeLt L basis (HABCRTDot.graphBits (HABCRTCoefficients.coefficient basis a))
    (HABCRTDot.graphBits (HABCRTCoefficients.coefficient basis b))

theorem residueLt_correct {n U K x y : ℕ} (L : Fin n) (basis : Template (n+1))
    (a b : Template (n+2)) (A : Matrix U) (e : Fin n→Fin U) (s : Finset ℕ)
    (primes : ∀ p∈s, p.Prime) (small : ∀ p∈s, p≤2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U) (hx : x<modulus s) (hy : y<modulus s)
    (precise : modulus s*budget s<2^(e L).val) (sel : Members basis A e s)
    (ha : Residues a A e s x) (hb : Residues b A e s y) :
    (residueLt L basis a b).eval A e=true ↔ x<y := by
  have hi : 2^K ≤ 2^((K+1)*K) := Nat.pow_le_pow_right (by decide)
    (Nat.le_mul_of_pos_left _ (by omega))
  have fits : Fits (U:=U) s := fun p hp => ((small p hp).trans hi).trans_lt cap
  have bits (z : ℕ) (g : Template (n+2)) (hg : Residues g A e s z)
      (p c : Fin U) (hp : p.val∈s) :
      (HABCRTDot.graphBits (HABCRTCoefficients.coefficient basis g)).eval A (extend c p e) =
      (coeff (inverse s) z p.val).testBit c.val := by
    apply HABCRTDot.graphBits_correct
    · exact (Nat.mod_lt _ (primes p.val hp).pos).trans p.isLt
    · intro v
      exact HABCRTCoefficients.coefficient_spec basis g A e s fits sel p v (primes _ hp)
        ⟨K,hK,small _ hp,cap⟩ z (fun b => hg p b hp)
  apply HABCRTDot.primeLt_correct L basis _ _ A e s (inverse s) primes small hK cap
    (fun _ hp => HABCRTRecovery.inverse_spec primes hp) hx hy precise sel
    (bits x a ha) (bits y b hb)

private def threshold {n : ℕ} (up : Bool) (c j : Fin n) : Template (n+2) :=
  thresholdResidue up c.succ.succ j.succ.succ 1 0

private theorem threshold_spec {n U K : ℕ} (up : Bool) (c j : Fin n) (A : Matrix U)
    (e : Fin n→Fin U) (s : Finset ℕ) (primes : ∀ p∈s, p.Prime)
    (small : ∀ p∈s, p≤2^K) (hK : 2≤K) (cap : 2^((K+1)*K)<U) :
    Residues (threshold up c j) A e s (((e c).val+up.toNat)*2^(e j).val) := by
  intro p b hp
  exact thresholdResidue_correct _ _ _ _ _ _ _ (primes _ hp) hK (small _ hp) cap

/-- Test two adjacent thresholds to certify c = floor(x / 2^j). -/
noncomputable def leadingAt {n : ℕ} (c j L : Fin n) (basis : Template (n+1))
    (input : Template (n+2)) : Template n :=
  .conj (.neg (residueLt L basis input (threshold false c j)))
    (residueLt L basis input (threshold true c j))

theorem leadingAt_correct {n U K x : ℕ} (c j L : Fin n) (basis : Template (n+1))
    (input : Template (n+2)) (A : Matrix U) (e : Fin n→Fin U) (s : Finset ℕ)
    (primes : ∀ p∈s, p.Prime) (small : ∀ p∈s, p≤2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U) (hx : x<modulus s)
    (upper : ((e c).val+1)*2^(e j).val<modulus s)
    (precise : modulus s*budget s<2^(e L).val) (sel : Members basis A e s)
    (hin : Residues input A e s x) :
    (leadingAt c j L basis input).eval A e=true ↔ (e c).val=x/2^(e j).val := by
  have lo : (e c).val*2^(e j).val<modulus s := (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans_lt upper
  have hfalse := residueLt_correct L basis input (threshold false c j) A e s primes small hK cap hx
    (by simpa using lo) precise sel hin (threshold_spec false c j A e s primes small hK cap)
  have htrue := residueLt_correct L basis input (threshold true c j) A e s primes small hK cap hx
    (by simpa using upper) precise sel hin (threshold_spec true c j A e s primes small hK cap)
  simp only [leadingAt,Tconj_true,Template.eval.eq_4,Bool.not_eq_true',←Bool.not_eq_true,hfalse,htrue,
    Bool.toNat_false,Bool.toNat_true,Nat.add_zero,not_lt]
  rw [←Nat.le_div_iff_mul_le (Nat.two_pow_pos _),←Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
  omega

private def ren {n m : ℕ} (v : Template n) (σ : Fin n→Fin m) : Template m :=
  rewriteMatrix (fun i j => .entry i j) v σ

private theorem ren_spec {n m U : ℕ} (v : Template n) (σ : Fin n→Fin m) (A : Matrix U) (e : Fin m→Fin U) :
    (ren v σ).eval A e=v.eval A (e ∘ σ) := rewriteMatrix_eval _ A A (by intros; rfl) _ _ _

private def lift1 {n : ℕ} (v : Template (n+1)) : Template (n+2) :=
  ren v (Fin.cases 0 (fun i => i.succ.succ))

private def lift2 {n : ℕ} (v : Template (n+2)) : Template (n+3) :=
  ren v (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ)))

private theorem lifts {n U x : ℕ} (basis : Template (n+1)) (input : Template (n+2))
    (A : Matrix U) (e : Fin n→Fin U) (s : Finset ℕ) (c : Fin U)
    (hb : Members basis A e s) (hx : Residues input A e s x) :
    Members (lift1 basis) A (Fin.cases c e) s ∧ Residues (lift2 input) A (Fin.cases c e) s x := by
  constructor
  · intro p
    rw [lift1,ren_spec]
    have eq : Fin.cases p (Fin.cases c e) ∘ Fin.cases 0 (fun i : Fin n => i.succ.succ) =
      Fin.cases p e := by funext i; refine Fin.cases rfl (fun _ => rfl) i
    rw [eq]; exact hb p
  · intro p b hp
    rw [lift2,ren_spec]
    have eq : extend b p (Fin.cases c e) ∘ Fin.cases 0 (Fin.cases 1 (fun i : Fin n => i.succ.succ.succ)) =
      extend b p e := by
      funext i; refine Fin.cases rfl (fun j => ?_) i
      refine Fin.cases rfl (fun _ => rfl) j
    rw [eq]; exact hx p b hp

/-- Read bit j whenever the discarded low j bits leave a quotient that fits
in one finite index. This permits up to log₂ U leading bits of a CRT word. -/
noncomputable def leadingBit {n : ℕ} (j L : Fin n) (basis : Template (n+1))
    (input : Template (n+2)) : Template n :=
  .ex (.conj (leadingAt 0 j.succ L.succ (lift1 basis) (lift2 input))
    (.ex (.conj (fromFormula (isNat 0 0)) (.bit 1 0))))

theorem leadingBit_correct {n U K x : ℕ} (j L : Fin n) (basis : Template (n+1))
    (input : Template (n+2)) (A : Matrix U) (e : Fin n→Fin U) (s : Finset ℕ)
    (primes : ∀ p∈s, p.Prime) (small : ∀ p∈s, p≤2^K)
    (hK : 2≤K) (cap : 2^((K+1)*K)<U) (hx : x<modulus s)
    (top : x/2^(e j).val<U) (upper : U*2^(e j).val<modulus s)
    (precise : modulus s*budget s<2^(e L).val) (sel : Members basis A e s)
    (hin : Residues input A e s x) :
    (leadingBit j L basis input).eval A e=true ↔ x.testBit (e j).val=true := by
  have check (c : Fin U) : (leadingAt 0 j.succ L.succ (lift1 basis) (lift2 input)).eval A
      (Fin.cases c e)=true ↔ c.val=x/2^(e j).val := by
    let f : Fin (n+1) → Fin U := Fin.cases c e
    exact leadingAt_correct (x:=x) 0 j.succ L.succ (lift1 basis) (lift2 input) A f s primes small hK
      cap hx ((Nat.mul_le_mul_right _ (show c.val+1≤U from c.isLt)).trans_lt upper) precise
      (lifts basis input A e s c sel hin).1 (lifts basis input A e s c sel hin).2
  simp only [leadingBit,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,Fin.cases_zero,check]
  change (∃ c : Fin U, c.val=x/2^(e j).val ∧ ∃ z : Fin U, z.val=0 ∧ c.val.testBit z.val=true) ↔ _
  have bit : (x/2^(e j).val).testBit 0=x.testBit (e j).val := by
    rw [←Nat.shiftRight_eq_div_pow,Nat.testBit_shiftRight,Nat.add_zero]
  exact ⟨fun ⟨c,hc,z,hz,hh⟩ => by simpa [hz,hc,bit] using hh,
    fun h => ⟨⟨_,top⟩,rfl,⟨0,(e j).pos⟩,rfl,bit.trans h⟩⟩

end DiophantineNP.HABCRTLeading
