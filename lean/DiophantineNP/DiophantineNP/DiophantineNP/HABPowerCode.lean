import DiophantineNP.HABGroupPower
import DiophantineNP.HABBinaryResidue
import DiophantineNP.HABSumParameters

/-! # Arithmetic checks for a short group-power certificate

One represented integer h supplies all the CRT digits as h modulo each
basis prime. A bounded unary sum checks their weighted congruence. -/
namespace DiophantineNP.HABPowerCode
open Counting WidthFormula PrimeFormula FiniteArithmeticGap ShortResidue Finset HABGroupPower
open ShortResidue.Predicate
local infixr:35 " ⋀ " => ShortResidue.Predicate.both

def term (n D h d : ℕ) := if d ∈ D.primeFactors then h%d*(n/d) else 0

def Admin (p r D h c K : ℕ) : Prop :=
  let n := p-1
  K=primeBound n ∧ D≤n*K ∧ n<D ∧ h<D ∧ Squarefree D ∧
  (∀ d∈D.primeFactors, n.Coprime d ∧ d<K) ∧ c≤K*K ∧
  (c+∑ d∈range K, term n D h d) ≡ r [MOD n]

private def member : ShortResidue.Predicate where
  syntaxF σ := .conj ((eqN 30 0).neg.syntaxF σ) (fromFormula (basisMember (σ 6) (σ 30)))
  holds _ _ e := e 6 ∈ (e 30).primeFactors
  valid σ t env := by
    rw [Tconj_true,Predicate.valid,fromFormula_eval]
    change (¬(env (σ 30)).val=0 ∧ _=true) ↔ _
    by_cases hz : (env (σ 30)).val=0
    · simp [hz]
    · rw [basisMember_spec _ _ _ (Nat.pos_of_ne_zero hz)]; simp [hz]

private def basis : ShortResidue.Predicate where
  syntaxF σ := fromFormula (basisFormula (σ 1) (σ 30) (σ 0))
  holds _ _ e := e 1<e 30 ∧ Squarefree (e 30) ∧
    ∀ d∈(e 30).primeFactors, (e 1).Coprime d ∧ d<e 0
  valid _ _ _ := by rw [fromFormula_eval,basisFormula_spec]

private def divQ (x d q : ℕ) : ShortResidue.Predicate where
  syntaxF σ := fromFormula (.ex (HABBinaryResidue.qr (σ x).succ (σ d).succ (σ q).succ 0))
  holds _ _ e := 0<e d ∧ e q=e x/e d
  valid σ _ env := by
    simp only [fromFormula_eval,exists_true,HABBinaryResidue.qr_true,Fin.cases_zero,Fin.cases_succ]
    constructor
    · rintro ⟨_,hd,hq,_⟩; exact ⟨hd,hq⟩
    · rintro ⟨hd,hq⟩
      exact ⟨⟨_,(Nat.mod_lt _ hd).trans (env (σ d)).isLt⟩,hd,hq,rfl⟩

private def cell : ShortResidue.Predicate :=
  member ⋀ Predicate.ex 10 (HABBinaryResidue.modulo 31 6 10 ⋀ Predicate.ex 11 (divQ 1 6 11 ⋀
    Predicate.ex 12 (mul 10 11 12 ⋀ lt 7 12)))

private theorem term_le (n D h d : ℕ) : term n D h d ≤ n := by
  unfold term
  split_ifs with hd
  · exact (Nat.mul_le_mul_right _ (Nat.mod_lt _ (Nat.mem_primeFactors.mp hd).1.pos).le).trans
      (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self ..)
  · omega

private theorem cell_spec (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (hn : e 1<U) (hd : e 6<U) :
    cell.holds U t e ↔ e 7<term (e 1) (e 30) (e 31) (e 6) := by
  simp only [cell,Predicate.both,member,Predicate.ex,HABBinaryResidue.modulo,divQ,mul,lt]
  simp only [Function.update, Nat.reduceEqDiff, ↓reduceDIte]
  by_cases hm : e 6 ∈ (e 30).primeFactors
  · have hp := (Nat.mem_primeFactors.mp hm).1.pos
    have hb := term_le (e 1) (e 30) (e 31) (e 6)
    simp only [term,if_pos hm] at hb ⊢
    simp only [hm,true_and,hp]
    constructor
    · rintro ⟨w,_,rfl,q,_,rfl,v,_,rfl,h⟩; exact h
    · intro h
      exact ⟨_,(Nat.mod_lt _ hp).trans hd,rfl,_,(Nat.div_le_self ..).trans_lt hn,rfl,
        _,hb.trans_lt hn,rfl,h⟩
  · simp [hm,term]

private def boundCode : ShortResidue.Predicate :=
  Predicate.ex 10 <| Predicate.ex 11 <| Predicate.ex 12 <| Predicate.ex 13 <| Predicate.ex 14 <|
    Predicate.ex 15 <| Predicate.ex 16 <|
    HABSumParameters.powAt 10 11 ⋀ le 11 1 ⋀ add 11 11 12 ⋀ lt 1 12 ⋀
    eqN 13 2 ⋀ add 10 13 14 ⋀ mul 14 14 15 ⋀ eqN 16 128 ⋀ mul 16 15 0

private theorem boundCode_spec (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (hn : 0<e 1)
    (hcap : 2*e 1<U) (hK : e 0<U) :
    boundCode.holds U t e ↔ e 0=primeBound (e 1) := by
  simp only [boundCode,Predicate.ex,Predicate.both,HABSumParameters.powAt,le,Predicate.neg,lt,add,eqN,mul]
  norm_num [Function.update]
  have eq (l : ℕ) : 128*((l+2)*(l+2))=32*(2*(l+1)+2)^2 := by ring
  constructor
  · rintro ⟨l,_,v,_,vv,_,z,_,w,_,w',_,m,_,rfl,lo,rfl,hi,rfl,rfl,rfl,rfl,h⟩
    have hl : l=(e 1).log2 := Nat.le_antisymm ((Nat.le_log2 hn.ne').mpr lo)
      (Nat.le_of_lt_succ ((Nat.log2_lt hn.ne').mpr (by simpa [pow_succ,Nat.mul_two] using hi)))
    rw [←h,eq,hl]; rfl
  · intro h
    let l := (e 1).log2
    have low : 2^l≤e 1 := Nat.log2_self_le hn.ne'
    have high : e 1<2^l+2^l := by simpa [l,pow_succ,Nat.mul_two] using (Nat.lt_log2_self (n:=e 1))
    have hk : e 0=128*((l+2)*(l+2)) := by rw [eq]; exact h
    have hc : (l+2)*(l+2) ≤ e 0 := by rw [hk]; omega
    have hsq : l+2≤(l+2)*(l+2) := Nat.le_mul_of_pos_right _ (by omega)
    have lU : l<U := (Nat.log2_le_self _).trans_lt (by omega)
    have hconst : 128 ≤ e 0 := by rw [hk]; nlinarith [show 0<l+2 by omega]
    exact ⟨l,lU,_,by omega,_,by omega,2,by omega,_,by omega,_,by omega,128,by omega,rfl,
      low,rfl,high,rfl,rfl,rfl,rfl,hk.symm⟩

private theorem sumEq (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (hU : 1<U) (hK : e 0<U)
    (hn : e 1<U) (hcap : e 0*e 1<U-U/2) (hs : e 4≤U/2) :
    (summed cell).holds U t e ↔ e 4=∑ d∈range (e 0),term (e 1) (e 30) (e 31) d := by
  let f := term (e 1) (e 30) (e 31)
  rw [summed_spec cell U t e f hK hn hU (fun _ _ => term_le ..) hcap hs (by
    intro z _ r hr v _
    let g := cellEnv e z r v
    have hn' : g 1<U := by simpa [g,cellEnv,Function.update] using hn
    have hr' : g 6<U := by simpa [g,cellEnv,Function.update] using hr.trans hK
    simpa [g,cellEnv,Function.update,f] using cell_spec U t g hn' hr')]
  have eq (k : ℕ) : Readout.prefixSum f k = ∑ d∈range k,f d := by
    induction k with
    | zero => simp [Readout.prefixSum]
    | succ k ih => rw [Readout.prefixSum,ih,sum_range_succ]
  rw [eq]

private def congruent : ShortResidue.Predicate :=
  Predicate.ex 41 <| add 33 4 41 ⋀ Predicate.ex 42
    (HABBinaryResidue.modulo 41 1 42 ⋀ HABBinaryResidue.modulo 32 1 42)

private theorem congruent_spec (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ)
    (hn : 0<e 1) (hnU : e 1<U) (hadd : e 33+e 4<U) :
    congruent.holds U t e ↔ (e 33+e 4) ≡ e 32 [MOD e 1] := by
  simp only [congruent,Predicate.ex,Predicate.both,add,HABBinaryResidue.modulo]
  simp only [Function.update,Nat.reduceEqDiff,↓reduceDIte,hn,true_and]
  constructor
  · rintro ⟨v,_,rfl,w,_,hw,hr⟩; exact hw.symm.trans hr
  · intro h
    exact ⟨_,hadd,rfl,_,(Nat.mod_lt _ hn).trans hnU,rfl,h⟩

private noncomputable def checksum :=
  Predicate.ex 4 (le 4 35 ⋀ summed cell ⋀ congruent)

private theorem checksum_spec (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (hnp : 0<e 1)
    (hU : 1<U) (hK : e 0<U) (hn : e 1<U) (hprod : e 35=e 1*e 0)
    (hcap : 2*(e 35+e 33+1) < U) :
    checksum.holds U t e ↔ (e 33+∑ d∈range (e 0),term (e 1) (e 30) (e 31) d) ≡ e 32 [MOD e 1] := by
  let S := ∑ d∈range (e 0),term (e 1) (e 30) (e 31) d
  have sb : S≤e 35 := by
    rw [hprod,Nat.mul_comm]
    exact (sum_le_sum (fun _ _ => term_le ..)).trans_eq (by simp)
  have step (s : ℕ) (hs : s≤e 35) :
      ((summed cell).holds U t (Function.update e 4 s) ∧ congruent.holds U t (Function.update e 4 s)) ↔
      s=S ∧ (e 33+s) ≡ e 32 [MOD e 1] := by
    let g := Function.update e 4 s
    have base : e 0*e 1<U-U/2 := by rw [Nat.mul_comm,←hprod]; omega
    have sum := sumEq U t g hU (by simpa [g,Function.update] using hK)
      (by simpa [g,Function.update] using hn) (by simpa [g,Function.update] using base)
      (by simp [g];omega)
    have con := congruent_spec U t g (by simpa [g,Function.update] using hnp)
      (by simpa [g,Function.update] using hn) (by simp [g];omega)
    simpa [g,Function.update,S] using and_congr sum con
  change (∃ s<U, (le 4 35).holds U t (Function.update e 4 s) ∧ _) ↔ _
  have guard (s : ℕ) : (le 4 35).holds U t (Function.update e 4 s) ↔ s≤e 35 := by
    simp [le,lt,Predicate.neg,Function.update]
  simp only [guard,Predicate.both]
  constructor
  · rintro ⟨s,_,hs,ready⟩
    obtain ⟨rfl,h⟩ := (step s hs).mp ready
    exact h
  · exact fun h => ⟨S,by omega,sb,(step S sb).mpr ⟨rfl,h⟩⟩

private def cand (n D h c K : ℕ) : Prop :=
  D≤n*K ∧ n<D ∧ h<D ∧ Squarefree D ∧ (∀ d∈D.primeFactors, n.Coprime d ∧ d<K) ∧ c≤K*K

private def candidates : ShortResidue.Predicate :=
  le 30 35 ⋀ lt 31 30 ⋀ basis ⋀ Predicate.ex 36 (mul 0 0 36 ⋀ le 33 36)

private theorem candidates_spec (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ)
    (hp : e 35=e 1*e 0) (hK : e 0*e 0<U) :
    candidates.holds U t e ↔ cand (e 1) (e 30) (e 31) (e 33) (e 0) := by
  simp only [candidates,Predicate.both,basis,Predicate.ex,le,Predicate.neg,lt,mul,cand]
  simp only [Function.update,Nat.reduceEqDiff,↓reduceDIte,hp,not_lt]
  constructor
  · rintro ⟨hd,hh,⟨hl,hs,hg⟩,m,_,rfl,hc⟩; exact ⟨hd,hl,hh,hs,hg,hc⟩
  · rintro ⟨hd,hl,hh,hs,hg,hc⟩; exact ⟨hd,hh,⟨hl,hs,hg⟩,_,hK,rfl,hc⟩

private noncomputable def checks :=
  Predicate.ex 35 (mul 1 0 35 ⋀ candidates ⋀ checksum)

private theorem checks_spec (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (hnp : 0<e 1)
    (hU : 1<U) (hK : e 0<U) (hn : e 1<U) (hbig : 2*(e 1*e 0+e 0*e 0+1)<U) :
    checks.holds U t e ↔ cand (e 1) (e 30) (e 31) (e 33) (e 0) ∧
      (e 33+∑ d∈range (e 0),term (e 1) (e 30) (e 31) d) ≡ e 32 [MOD e 1] := by
  let g := Function.update e 35 (e 1*e 0)
  have hc := candidates_spec U t g (by simp [g]) (by simp [g];omega)
  have co (hc' : g 33≤g 0*g 0) := checksum_spec U t g
    (by simpa [g,Function.update] using hnp) hU (by simpa [g,Function.update] using hK)
    (by simpa [g,Function.update] using hn) (by simp [g])
    (by simp [g] at hc' ⊢;omega)
  change (∃ v<U, (mul 1 0 35).holds U t (Function.update e 35 v) ∧ _) ↔ _
  have guard (v : ℕ) : (mul 1 0 35).holds U t (Function.update e 35 v) ↔ e 1*e 0=v := by
    simp [mul,Function.update]
  simp only [guard,Predicate.both]
  constructor
  · rintro ⟨v,_,rfl,hc',hz⟩
    have hcan := hc.mp hc'
    exact ⟨by simpa [g,Function.update] using hcan,
      by simpa [g,Function.update] using (co hcan.2.2.2.2.2).mp hz⟩
  · rintro ⟨hcan,hz⟩
    exact ⟨_,by omega,rfl,hc.mpr (by simpa [g,Function.update] using hcan),
      (co (by simpa [g,Function.update] using hcan.2.2.2.2.2)).mpr (by simpa [g,Function.update] using hz)⟩

private def predecessor : ShortResidue.Predicate := Predicate.ex 44 (eqN 44 1 ⋀ add 1 44 34)

private noncomputable def program := Predicate.ex 1 (predecessor ⋀ boundCode ⋀ checks)

private theorem budget {p U : ℕ} (hp : 2≤p) (hU : (p+2)^30≤U) :
    2*((p-1)*primeBound (p-1)+primeBound (p-1)*primeBound (p-1)+1)<U ∧ 2*p<U := by
  let x := p+2
  have hx : 4≤x := by dsimp [x]; omega
  have hK : primeBound (p-1) ≤ x^6 := by
    have hn := Nat.log2_le_self (p-1)
    have h : (p-1).log2+2 ≤ x := by dsimp [x]; omega
    have h128 : 128≤x^4 := by have := Nat.pow_le_pow_left hx 4; norm_num at this; omega
    calc primeBound (p-1) = 128*((p-1).log2+2)^2 := by unfold primeBound;ring
         _ ≤ x^4*x^2 := Nat.mul_le_mul h128 (Nat.pow_le_pow_left h 2)
         _ = x^6 := by ring
  have xn : p-1≤x^6 := (show p-1≤x from by dsimp [x];omega).trans
    (by simpa using Nat.pow_le_pow_right (n:=x) (by omega) (show 1≤6 by decide))
  have sq : x^6*x^6=x^12 := by ring
  have b1 := Nat.mul_le_mul xn hK
  have b2 := Nat.mul_le_mul hK hK
  rw [sq] at b1 b2
  have heavy : 16*x^12≤U := calc
    16*x^12 ≤ x^2*x^12 := Nat.mul_le_mul_right _ (by nlinarith)
    _ = x^14 := by ring
    _ ≤ x^30 := Nat.pow_le_pow_right (by omega) (by decide)
    _ ≤ U := hU
  have big : x≤x^12 := by simpa using Nat.pow_le_pow_right (n:=x) (by omega) (show 1≤12 by decide)
  have px : p≤x := by dsimp [x];omega
  omega

private def slots : ℕ→Fin 6 := fun z =>
  if z=34 then 0 else if z=32 then 1 else if z=30 then 2 else
  if z=31 then 3 else if z=33 then 4 else 5

/-- Slots 0 through 5 contain the prime, exponent, basis product, packed
coefficient digits, correction and basis-prime bound. -/
noncomputable def formula : Template 6 := program.syntaxF slots

theorem formula_correct {U : ℕ} (A : Fin U→Fin U→Bool) (e : Fin 6→Fin U)
    (hp : (e 0).val.Prime) (fits : ((e 0).val+2)^30≤U) :
    formula.eval A e=true ↔ Admin (e 0).val (e 1).val (e 2).val (e 3).val (e 4).val (e 5).val := by
  let t (r c : ℕ) := if h : r<U ∧ c<U then A ⟨r,h.1⟩ ⟨c,h.2⟩ else false
  have he : A=(fun r c : Fin U => t r.val c.val) := by funext r c; simp [t,r.isLt,c.isLt]
  let n := (e 0).val-1
  let g := Function.update (fun i => (e (slots i)).val) 1 n
  have hn : 0<n := by dsimp [n]; have := hp.two_le;omega
  obtain ⟨hbudget,hdbl⟩ := budget hp.two_le fits
  have hb := boundCode_spec U t g (by simpa [g] using hn)
    (by simp [g,n];omega) (by simp [g,slots])
  have hc (hK : (e 5).val=primeBound n) := checks_spec U t g
    (by simpa [g] using hn) (by have := hp.two_le;omega)
    (by simp [g,slots]) (by simp [g,n];omega)
    (by simpa [g,slots,Function.update,hK,n] using hbudget)
  rw [formula,he,Predicate.valid]
  change (∃ j<U, predecessor.holds U t (Function.update (fun i => (e (slots i)).val) 1 j) ∧ _) ↔ _
  have pred (j : ℕ) : predecessor.holds U t (Function.update (fun i => (e (slots i)).val) 1 j) ↔ j=n := by
    simp only [predecessor,Predicate.ex,Predicate.both,eqN,add]
    simp [Function.update,slots,n]; have := hp.two_le;omega
  simp only [pred,Predicate.both]
  constructor
  · rintro ⟨j,_,rfl,hb',hc'⟩
    have hk : (e 5).val=primeBound n := by simpa [g,slots,Function.update] using hb.mp hb'
    obtain ⟨can,con⟩ := (hc hk).mp hc'
    change (e 5).val=primeBound n ∧ _
    exact ⟨hk,can.1,can.2.1,can.2.2.1,can.2.2.2.1,can.2.2.2.2.1,can.2.2.2.2.2,con⟩
  · rintro ⟨hk,hd,hl,hh,hs,hp',hcb,hcon⟩
    exact ⟨n,by dsimp [n];omega,rfl,hb.mpr hk,
      (hc hk).mpr ⟨⟨hd,hl,hh,hs,hp',hcb⟩,hcon⟩⟩

end DiophantineNP.HABPowerCode
