import DiophantineNP.HABCounting
import DiophantineNP.HABTranslation

/-! # Reading a binary word in a short prime residue field

The set bit positions are grouped by their residue weights. Exact counting
allows an entire input row to be processed in the original universe. Only
the table indexed by the possible short residues needs to fit a bounded
majority sum. -/
namespace DiophantineNP.HABBinaryResidue
open Counting WidthFormula PrimeFormula FiniteArithmeticGap ShortResidue Finset
open ShortResidue.Predicate
local infixr:35 " ⋀ " => ShortResidue.Predicate.both

private theorem prefix_eq (f : ℕ → ℕ) (n : ℕ) :
    Readout.prefixSum f n = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp [Readout.prefixSum]
  | succ n ih => simp [Readout.prefixSum, ih, sum_range_succ]

/-- The zero position is counted separately so the remaining population
fits in one element even when every input row has the same residue. -/
def population (U : ℕ) (f : ℕ → ℕ) (a : ℕ) : ℕ :=
  ((range U).filter (fun j => j ≠ 0 ∧ f j = a)).card

private theorem pop_lt {U : ℕ} (hU : 0 < U) (f : ℕ → ℕ) (a : ℕ) :
    population U f a < U := by
  unfold population
  conv_rhs => rw [← card_range U]
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨filter_subset _ _, ?_⟩
  intro h
  have h0 : 0 ∈ (range U).filter (fun j => j ≠ 0 ∧ f j = a) := by rw [h]; exact mem_range.mpr hU
  simp at h0

private theorem sum_pop {U p : ℕ} (hU : 0<U) (f : ℕ→ℕ) (hf : ∀ i<U, f i<p) :
    (∑ a ∈ range p, a * population U f a) + f 0 = ∑ j ∈ range U, f j := by
  classical
  have swap : (∑ a ∈ range p, a * population U f a) =
      ∑ j ∈ range U, if j=0 then 0 else f j := by
    calc
      _ = ∑ a ∈ range p, ∑ j ∈ range U, if j≠0 ∧ f j=a then a else 0 := by
        apply sum_congr rfl
        intro a ha
        rw [← Finset.sum_filter]
        simp [population, Nat.mul_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply sum_congr rfl
        intro j hj
        by_cases h : j=0
        · simp [h]
        · simp [h,hf j (mem_range.mp hj)]
  rw [swap]
  have hz : f 0 = ∑ j ∈ range U, if j=0 then f j else 0 := by simp [hU]
  conv_lhs => rhs; rw [hz]
  rw [← Finset.sum_add_distrib]
  exact sum_congr rfl (fun j _ => by by_cases h : j=0 <;> simp [h])

def contribution (U p : ℕ) (f : ℕ→ℕ) (a : ℕ) := a * (population U f a % p) % p

private theorem weight_eq {U p : ℕ} (hU : 0<U) (f : ℕ→ℕ) (hf : ∀ i<U, f i<p) :
    (Readout.prefixSum (contribution U p f) p + f 0)%p = Readout.prefixSum f U%p := by
  rw [prefix_eq,prefix_eq,← sum_pop hU f hf]
  apply Nat.ModEq.add _ (Nat.ModEq.refl _)
  suffices ∀ n, (∑ a ∈ range n, contribution U p f a) ≡
      (∑ a ∈ range n, a * population U f a) [MOD p] from this p
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum_range_succ]
    apply ih.add
    simp [Nat.ModEq,contribution,Nat.mul_mod]

/-- Ordinary bounded division with remainder. -/
def qr {k : ℕ} (x d q r : Fin k) : Formula k :=
  .ex (andF (mulF d.succ q.succ 0)
    (andF (addF 0 r.succ x.succ) (ltF r.succ d.succ)))

theorem qr_true {U k : ℕ} (x d q r : Fin k) (env : Fin k → Fin U) :
    (qr x d q r).eval env = true ↔
      0<(env d).val ∧ (env q).val=(env x).val/(env d).val ∧ (env r).val=(env x).val%(env d).val := by
  simp only [qr, exists_true,andF_spec,mulF_spec,addF_spec,ltF_true,Fin.cases_succ,Fin.cases_zero]
  constructor
  · rintro ⟨m,hm,he,hr⟩
    have hd : 0<(env d).val := by omega
    have hx : (env x).val=(env r).val+(env d).val*(env q).val := by omega
    rw [hx,Nat.add_mul_div_left _ _ hd,Nat.div_eq_of_lt hr,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
    simp [hd]
  · rintro ⟨hd,hq,hr⟩
    have hh := Nat.div_add_mod (env x).val (env d).val
    rw [← hq, ← hr] at hh
    exact ⟨⟨_,by have := (env x).isLt; omega⟩,rfl,hh,hr ▸ Nat.mod_lt _ hd⟩

def modulo (x d r : ℕ) : ShortResidue.Predicate where
  syntaxF σ := fromFormula (.ex (qr (σ x).succ (σ d).succ 0 (σ r).succ))
  holds _ _ e := 0<e d ∧ e r=e x%e d
  valid σ _ env := by
    simp only [fromFormula_eval,exists_true,qr_true,Fin.cases_succ,Fin.cases_zero]
    constructor
    · rintro ⟨q,h,_,hr⟩; exact ⟨h,hr⟩
    · rintro ⟨h,hr⟩
      exact ⟨⟨_,(Nat.div_le_self _ _).trans_lt (env (σ x)).isLt⟩,h,rfl,hr⟩


private def bucketCell (counts : ShortResidue.Predicate) : ShortResidue.Predicate :=
  Predicate.ex 21 <| counts ⋀ (Predicate.ex 22 <| modulo 21 0 22 ⋀
    (Predicate.ex 23 <| mul 6 22 23 ⋀ (Predicate.ex 24 <| modulo 23 0 24 ⋀ lt 7 24)))

private theorem bucketCell_spec (counts : ShortResidue.Predicate) (U p : ℕ) (t : ℕ→ℕ→Bool)
    (e : ℕ→ℕ) (f : ℕ→ℕ) (ep : e 0=p) (hp : 0<p) (hsize : p*p<U) (ha : e 6<p)
    (hc : ∀ c<U, counts.holds U t (Function.update e 21 c) ↔ c=population U f (e 6)) :
    (bucketCell counts).holds U t e ↔ e 7 < contribution U p f (e 6) := by
  have hU : 0<U := by omega
  have hpU : p<U := (Nat.le_mul_of_pos_left _ hp).trans_lt hsize
  let C := population U f (e 6)
  let R := C%p
  have hR : R<p := Nat.mod_lt _ hp
  have hT : e 6*R<U := (Nat.mul_le_mul ha.le hR.le).trans_lt hsize
  simp only [bucketCell,Predicate.ex,Predicate.both,modulo,mul,lt]
  simp only [Function.update, Nat.reduceEqDiff, ↓reduceDIte,ep,hp,true_and]
  constructor
  · rintro ⟨c,hc',hcu,r,_,rfl,v,_,rfl,z,_,rfl,h⟩
    have hh := (hc c hc').mp hcu
    simpa [contribution,hh] using h
  · intro hh
    exact ⟨C,pop_lt hU f _,(hc C (pop_lt hU f _)).mpr rfl,
      R,hR.trans hpU,rfl,e 6*R,hT,rfl,_,(Nat.mod_lt _ hp).trans hpU,rfl,hh⟩

private def guardSum : ShortResidue.Predicate := Predicate.ex 28 <| mul 0 0 28 ⋀ le 4 28

private theorem guardSum_spec (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (h : e 0*e 0<U) :
    guardSum.holds U t e ↔ e 4≤e 0*e 0 := by
  simp only [guardSum,Predicate.ex,Predicate.both,mul,le,Predicate.neg,lt,not_lt]
  simp [Function.update, h]

private def addFirst (first : ShortResidue.Predicate) : ShortResidue.Predicate :=
  Predicate.ex 26 <| first ⋀ (Predicate.ex 27 <| add 4 26 27 ⋀ modulo 27 0 2)

private theorem addFirst_spec (first : ShortResidue.Predicate) (U p : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ)
    (x : ℕ) (ep : e 0=p) (hp : 0<p) (hfit : e 4+x<U)
    (hf : ∀ v<U, first.holds U t (Function.update e 26 v) ↔ v=x) :
    (addFirst first).holds U t e ↔ e 2=(e 4+x)%p := by
  simp only [addFirst,Predicate.ex,Predicate.both,add,modulo]
  simp only [Function.update, Nat.reduceEqDiff, ↓reduceDIte,ep,hp,true_and]
  constructor
  · rintro ⟨v,hv,hh,z,_,rfl,h⟩
    simpa [(hf v hv).mp hh] using h
  · intro h
    have hx : x<U := by omega
    exact ⟨x,hx,(hf x hx).mpr rfl,_,hfit,rfl,h⟩

noncomputable def assembled (counts first : ShortResidue.Predicate) :=
  Predicate.ex 4 <| guardSum ⋀ ShortResidue.summed (bucketCell counts) ⋀ addFirst first

/-- Sum the residue classes by frequency. Counting the nonzero positions separately
allows a population equal to the whole universe without an extra numerical digit. -/
theorem assembled_spec (counts first : ShortResidue.Predicate) (U p : ℕ)
    (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (f : ℕ→ℕ) (ep : e 0=p) (ep' : e 1=p)
    (hp : 0<p) (hU : 1<U) (hsize : p*p<U-U/2) (hf : ∀ j<U,f j<p)
    (hc : ∀ s<U, ∀ z<U, ∀ a<p, ∀ u<p, ∀ c<U, counts.holds U t
      (Function.update (cellEnv (Function.update e 4 s) z a u) 21 c) ↔ c=population U f a)
    (h0 : ∀ s<U, ∀ v<U, first.holds U t (Function.update (Function.update e 4 s) 26 v) ↔ v=f 0) :
    (assembled counts first).holds U t e ↔ e 2=Readout.prefixSum f U%p := by
  let W := contribution U p f
  let S := Readout.prefixSum W p
  have hp2 : p*p<U := hsize.trans_le (Nat.sub_le ..)
  have hpU : p<U := (Nat.le_mul_of_pos_left _ hp).trans_lt hp2
  have hw (a : ℕ) : W a < p := Nat.mod_lt _ hp
  have hS : S≤p*p := by
    rw [show S=Readout.prefixSum W p from rfl,prefix_eq]
    calc
      _ ≤ ∑ _a ∈ range p, p := sum_le_sum fun a _ => (hw a).le
      _ = _ := by simp
  have hsU := hS.trans_lt hp2
  have hguard (s : ℕ) := guardSum_spec U t (Function.update e 4 s)
    (by simpa [Function.update,ep] using hp2)
  have hsum (s : ℕ) (hs : s<U) (hg : s≤p*p) : (ShortResidue.summed (bucketCell counts)).holds U t
      (Function.update e 4 s) ↔ s=S := by
    let v := Function.update e 4 s
    have v0 : v 0=p := by simp [v,ep]
    have v1 : v 1=p := by simp [v,ep']
    change _ ↔ v 4=Readout.prefixSum W p
    rw [← v0]
    apply ShortResidue.summed_spec (bucketCell counts) U t v W
      (v0 ▸ hpU) (v1 ▸ hpU) hU (by rw [v1]; exact fun a _ => (hw a).le)
      (by simpa [v0,v1] using hsize) (by simp [v]; omega)
    intro z hz a ha u hu
    rw [v0] at ha; rw [v1] at hu
    exact bucketCell_spec counts U p t (cellEnv v z a u) f (by simp [cellEnv,Function.update,v0])
      hp hp2 (by simpa [cellEnv,Function.update] using ha) (by simpa [cellEnv,Function.update,v] using hc s hs z hz a ha u hu)
  have hfirst (s : ℕ) (hs : s<U) (hg : s≤p*p) := addFirst_spec first U p t (Function.update e 4 s)
    (f 0) (by simp [Function.update,ep]) hp
    (by simp only [Function.update_self]; have := hf 0 (by omega); have := Nat.le_mul_of_pos_left p hp; omega)
    (h0 s hs)
  change (∃ s<U, _ ∧ _ ∧ _) ↔ _
  constructor
  · rintro ⟨s,hs,hg,ht,hh⟩
    have hgs : s≤p*p := by simpa [Function.update,ep] using (hguard s).mp hg
    have he := (hsum s hs hgs).mp ht
    have h := (hfirst s hs hgs).mp hh
    simpa [Function.update,he,S,W,weight_eq (by omega) f hf] using h
  · intro h
    refine ⟨S,hsU,(hguard S).mpr (by simpa [Function.update,ep] using hS),
      (hsum S hsU hS).mpr rfl,(hfirst S hsU hS).mpr ?_⟩
    simpa [Function.update,S,W,weight_eq (by omega) f hf] using h


/-- The exponent may be any position in the entire universe: for an odd prime
we first reduce it modulo the order of the multiplicative residue group. -/
def powerAtPosition (j a : ℕ) : ShortResidue.Predicate :=
  (eqN 0 2 ⋀ ((eqN j 0 ⋀ eqN a 1).either ((eqN j 0).neg ⋀ eqN a 0))).either
  ((eqN 0 2).neg ⋀ (Predicate.ex 31 <| Predicate.ex 32 <| Predicate.ex 33 <| Predicate.ex 34 <|
    eqN 31 1 ⋀ eqN 32 2 ⋀ add 33 31 0 ⋀ modulo j 33 34 ⋀ shortPow 32 34 0 a))

theorem powerAtPosition_spec {U K p : ℕ} (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (j a : ℕ)
    (hj : j<31) (ha : a<31) (ep : e 0=p) (hp : p.Prime) (hpU : p<U)
    (_hpos : e j<U) (hval : e a<U) (hK : 2≤K) (hpk : p≤2^K)
    (hc : 2^((K+1)*K)<U) :
    (powerAtPosition j a).holds U t e ↔ e a=2^(e j)%p := by
  change ((e 0=2 ∧ ((e j=0 ∧ e a=1) ∨ (¬ e j=0 ∧ e a=0))) ∨
    (¬ e 0=2 ∧ ∃ o<U, ∃ b<U, ∃ m<U, ∃ r<U, _)) ↔ _
  by_cases htwo : p=2
  · rw [ep]
    by_cases hz : e j=0
    · simp [htwo,hz]
    · obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hz
      simp [htwo,hn,pow_succ]
  · rw [ep]
    simp only [htwo,false_and,false_or,not_false_eq_true,true_and]
    have hbig : 2<p := lt_of_le_of_ne hp.two_le (Ne.symm htwo)
    have hm : 0<p-1 := by omega
    have hj31 : j≠31 := by omega
    have hj32 : j≠32 := by omega
    have hj33 : j≠33 := by omega
    have hj34 : j≠34 := by omega
    have ha31 : a≠31 := by omega
    have ha32 : a≠32 := by omega
    have ha33 : a≠33 := by omega
    have ha34 : a≠34 := by omega
    let E (o b m r : ℕ) := Function.update (Function.update (Function.update (Function.update e 31 o) 32 b) 33 m) 34 r
    have eqP (o b m r : ℕ) : E o b m r 0=p := by simp [E,ep]
    have eqJ (o b m r : ℕ) : E o b m r j=e j := by simp [E,hj31,hj32,hj33,hj34]
    have eqA (o b m r : ℕ) : E o b m r a=e a := by simp [E,ha31,ha32,ha33,ha34]
    let r := e j%(p-1)
    have hr : r<p-1 := Nat.mod_lt _ hm
    have hrp : r<p := by omega
    have powOK : (shortPow 32 34 0 a).holds U t (E 1 2 (p-1) r) ↔ e a=2^(e j)%p := by
      have H := shortPow_iff 32 34 0 a U K t (E 1 2 (p-1) r) (by simpa [eqP] using hp)
        (by simpa [E,ep] using hbig) (by simpa [E,ep] using hrp) (by simpa [eqA] using hval)
        (by simpa [eqP] using hpU) hK (by simpa [eqP] using hpk) hc
      rw [H,eqA,eqP]
      change e a=2^r%p ↔ _
      rw [show 2^r%p=2^(e j)%p from reduce_exponent hp (by decide) hbig _]
    change (∃ o<U, ∃ b<U, ∃ m<U, ∃ v<U, o=1 ∧ b=2 ∧ m+o=e 0 ∧
      (0<m ∧ v=(E o b m v j)%m) ∧ (shortPow 32 34 0 a).holds U t (E o b m v)) ↔ _
    simp only [eqJ,ep]
    constructor
    · rintro ⟨o,_,b,_,m,_,v,_,rfl,rfl,h,⟨_,rfl⟩,hpow⟩
      obtain rfl : m=p-1 := by omega
      exact powOK.mp hpow
    · intro h
      exact ⟨1,by omega,2,by omega,p-1,by omega,r,hrp.trans hpU,rfl,rfl,by omega,⟨hm,rfl⟩,powOK.mpr h⟩

private def weightedBit (j a : ℕ) : ShortResidue.Predicate :=
  ((entry 30 j).neg ⋀ eqN a 0).either (entry 30 j ⋀ powerAtPosition j a)

private def digit (t : ℕ→ℕ→Bool) (row p j : ℕ) :=
  (t row j).toNat * 2^j % p

private theorem weightedBit_spec {U K p : ℕ} (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (j a : ℕ)
    (hj : j<31) (ha : a<31) (ep : e 0=p) (hp : p.Prime) (hpU : p<U)
    (hpos : e j<U) (hval : e a<U) (hK : 2≤K) (hpk : p≤2^K) (hc : 2^((K+1)*K)<U) :
    (weightedBit j a).holds U t e ↔ e a=digit t (e 30) p (e j) := by
  change ((¬t (e 30) (e j)=true) ∧ e a=0 ∨ (t (e 30) (e j)=true) ∧ _) ↔ _
  rw [powerAtPosition_spec t e j a hj ha ep hp hpU hpos hval hK hpk hc]
  cases h : t (e 30) (e j) <;> simp [digit,h]


private noncomputable def populations (cell : ℕ→ℕ→ShortResidue.Predicate) :=
  HABCounting.countEqP 25 21 ((eqN 25 0).neg ⋀ cell 25 6)

private def firstCell (cell : ℕ→ℕ→ShortResidue.Predicate) :=
  Predicate.ex 25 (eqN 25 0 ⋀ cell 25 26)

/-- Sum a relation-defined table of residue values over all positions. The
outer parameters are a modulus (names 0 and 1) and proposed result (name 2).
Name 30 is available as a parameter for the input table. -/
noncomputable def sumCells (cell : ℕ→ℕ→ShortResidue.Predicate) :=
  assembled (populations cell) (firstCell cell)

/-- The result has no row-count restriction: each of the U positions is read.
The only accumulator-width assumption is on the modulus, not the input word. -/
theorem sumCells_spec (cell : ℕ→ℕ→ShortResidue.Predicate)
    {U p : ℕ} (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (f : ℕ→ℕ) (ep : e 0=p) (ep' : e 1=p)
    (hp : 0<p) (hU : 1<U) (hsize : p*p<U-U/2) (hf : ∀ j<U,f j<p)
    (hcell : ∀ (v : ℕ→ℕ) (a : ℕ), a<31 → v 0=p → v 30=e 30 →
      v 25<U → v a<U → ((cell 25 a).holds U t v ↔ v a=f (v 25))) :
    (sumCells cell).holds U t e ↔ e 2=Readout.prefixSum f U%p := by
  classical
  apply assembled_spec _ _ _ _ _ _ _ ep ep' hp hU hsize hf
  · intro s hs z hz a ha u hu c hc
    let v := Function.update (cellEnv (Function.update e 4 s) z a u) 21 c
    have v6 : v 6=a := by simp [v,cellEnv,Function.update]
    have v0 : v 0=p := by simp [v,cellEnv,Function.update,ep]
    have v30 : v 30=e 30 := by simp [v,cellEnv,Function.update]
    change (v 21 = HABCounting.cardP U t v 25 ((eqN 25 0).neg ⋀ cell 25 6)) ↔ _
    have v21 : v 21=c := by simp [v]
    rw [v21]
    apply Iff.of_eq
    apply congrArg (fun m => c=m)
    unfold HABCounting.cardP population
    apply congrArg Finset.card
    apply filter_congr
    intro j hj
    have hv := hcell (Function.update v 25 j) 6 (by decide) (by simpa [Function.update] using v0)
      (by simpa [Function.update] using v30) (by simpa using mem_range.mp hj)
      (by simp [Function.update,v6]; have := Nat.le_mul_of_pos_left p hp; omega)
    change ((¬(Function.update v 25 j) 25=0) ∧ (cell 25 6).holds U t (Function.update v 25 j)) ↔ _
    rw [hv]
    change (j≠0 ∧ a=f j) ↔ j≠0 ∧ f j=a
    exact and_congr_right fun _ => eq_comm
  · intro s hs c hc
    let v := Function.update (Function.update e 4 s) 26 c
    change (∃ j<U, j=0 ∧ (cell 25 26).holds U t (Function.update v 25 j)) ↔ _
    have HH := hcell (Function.update v 25 0) 26 (by decide) (by simp [v,Function.update,ep])
      (by simp [v,Function.update]) (by simp; omega) (by simpa [v,Function.update] using hc)
    change (cell 25 26).holds U t (Function.update v 25 0) ↔ c=f 0 at HH
    constructor
    · rintro ⟨j,_,rfl,he⟩; exact HH.mp he
    · intro he; exact ⟨0,by omega,rfl,HH.mpr he⟩

/-- An iterated sum modulo p from a raw input relation assigning one residue
to each row. Both arguments are ordinary elements of the finite universe. -/
noncomputable def sumResidue {k : ℕ} (p b : Fin k) : Template k :=
  (sumCells entry).syntaxF (fun i => if i=2 then b else p)

theorem sumResidue_spec {U k : ℕ} (p b : Fin k) (e : Fin k→Fin U) (f : ℕ→ℕ)
    (hp : 0<(e p).val) (hU : 1<U) (hsize : (e p).val*(e p).val<U-U/2)
    (hf : ∀ j<U, f j<(e p).val) :
    (sumResidue p b).eval (fun j v => decide (v.val=f j.val)) e=true ↔
      (e b).val=Readout.prefixSum f U%(e p).val := by
  unfold sumResidue
  rw [Predicate.valid _ _ (fun j v => decide (v=f j))]
  exact sumCells_spec entry _ _ f rfl rfl hp hU hsize hf (fun _ _ _ _ _ _ _ => by simp [entry])

noncomputable def rowResidue {k : ℕ} (row p b : Fin k) : Template k :=
  (sumCells weightedBit).syntaxF (fun i => if i=2 then b else if i=30 then row else p)

private theorem weighted_word (t : ℕ→ℕ→Bool) (r p U : ℕ) :
    Readout.prefixSum (digit t r p) U % p = Readout.word (t r) U % p := by
  induction U with
  | zero => simp [Readout.word,Readout.prefixSum]
  | succ U ih =>
    change (Readout.prefixSum (digit t r p) U+digit t r p U)%p= (Readout.word (t r) U + _)%p
    rw [Nat.add_mod,Nat.add_mod (Readout.word _ _),ih]
    simp [digit]

/-- For any input matrix, this one fixed formula recognizes the residue of an
entire row of U bits at every prime in the proved short-power range. -/
theorem rowResidue_spec {U K k : ℕ} (row p b : Fin k) (e : Fin k→Fin U) (A : HAB.Matrix U)
    (hp : (e p).val.Prime) (hsize : (e p).val*(e p).val<U-U/2)
    (hK : 2≤K) (hpk : (e p).val≤2^K) (hcap : 2^((K+1)*K)<U) :
    (rowResidue row p b).eval A e=true ↔
      (e b).val=HAB.rowWord (A (e row))%(e p).val := by
  let T (r j : ℕ) := if h : r<U ∧ j<U then A ⟨r,h.1⟩ ⟨j,h.2⟩ else false
  have tab : A=fun r j => T r.val j.val := by funext r j; simp [T,r.isLt,j.isLt]
  let d := (e p).val
  let r := (e row).val
  let v := fun i : ℕ => (e (if i=2 then b else if i=30 then row else p)).val
  have h := sumCells_spec weightedBit T v (digit T r d) rfl rfl hp.pos
    (hp.one_lt.trans (e p).isLt) hsize (fun i _ => Nat.mod_lt _ hp.pos)
    (fun env a ha he hr hj hv => by
      simpa only [hr] using weightedBit_spec T env 25 a (by decide) ha he hp (e p).isLt hj hv hK hpk hcap)
  unfold rowResidue
  rw [tab,Predicate.valid _ _ T]
  change _ ↔ (e b).val=HAB.rowWord (fun i => T r i.val)%d
  rw [h]
  change (e b).val=Readout.prefixSum (digit T r d) U%d ↔ _
  rw [weighted_word]
  have hword : HAB.rowWord (fun i : Fin U => T r i.val) = Readout.word (T r) U := by
    have he : (fun i : Fin U => T r i.val) = fun i : Fin U => (Readout.word (T r) U).testBit i.val := by
      funext i; exact (Readout.word_testBit _ i.isLt).symm
    rw [he,HAB.rowWord_natural (Readout.word_lt _ _)]
  rw [hword]
/-- The short-power capacity already pays for the residue histogram. -/
theorem square_fits {p U K : ℕ} (hK : 2≤K) (hpk : p≤2^K) (hcap : 2^((K+1)*K)<U) :
    p*p<U-U/2 := by
  have hexp : K+K+1≤(K+1)*K := by
    have h := Nat.mul_le_mul_right K hK
    nlinarith
  have twice : 2*(p*p)<U := calc
    2*(p*p) ≤ 2*(2^K*2^K) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hpk hpk)
    _ = 2^(K+K+1) := by rw [pow_succ,pow_add]; omega
    _ ≤ 2^((K+1)*K) := Nat.pow_le_pow_right (by decide) hexp
    _ < U := hcap
  omega

theorem rowResidue_short {U K k : ℕ} (row p b : Fin k) (e : Fin k→Fin U) (A : HAB.Matrix U)
    (hp : (e p).val.Prime) (hK : 2≤K) (hpk : (e p).val≤2^K) (hcap : 2^((K+1)*K)<U) :
    (rowResidue row p b).eval A e=true ↔
      (e b).val=HAB.rowWord (A (e row))%(e p).val :=
  rowResidue_spec row p b e A hp (square_fits hK hpk hcap) hK hpk hcap

end DiophantineNP.HABBinaryResidue
