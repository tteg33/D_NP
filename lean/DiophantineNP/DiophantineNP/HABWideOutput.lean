import DiophantineNP.HABCRTSize
import DiophantineNP.HABProductEquivalence
import DiophantineNP.HABSpacePadding

/-! # From a uniformly bounded CRT bit query to all product bits

The input matrix is enlarged by padding its rows with the multiplicative
identity. The product is preserved through every square interpretation. -/
namespace DiophantineNP.HABWideOutput
open Finset HAB HABCRTRecovery HABCRTShift HABPrimeBlocks HABPairInterpretation
open WidthFormula Counting FiniteArithmeticGap

/-- A cubic numerical allocation for each basis prime also pays for the
precision of the entire CRT basis, even when the basis is extended. -/
theorem precision_of_cubes {V : ℕ} {S : Finset ℕ} (cap : 27<V)
    (small : ∀ p ∈ S,p^3<V) : modulus S*budget S < 2^(V-1) := by
  let T := insert 3 S
  have ne : T.Nonempty := ⟨3,mem_insert_self ..⟩
  let B := T.max' ne
  have B3 : 3≤B := le_max' T 3 (mem_insert_self ..)
  have bound (p) (hp : p∈S) : p≤B := le_max' T p (mem_insert_of_mem hp)
  have cube : B^3<V := by
    have h : B∈insert 3 S := max'_mem T ne
    rcases mem_insert.mp h with eq|mem
    · simpa only [eq] using cap
    · exact small B mem
  have card : S.card ≤ B+1 := (card_le_card (show S⊆range (B+1) from
    fun p hp => mem_range.mpr (Nat.lt_succ_of_le (bound p hp)))).trans (card_range _).le
  have base := precision (s := S) (b := B) (fun p hp => (bound p hp).trans Nat.lt_two_pow_self.le)
  apply base.trans_le (Nat.pow_le_pow_right (by decide) ?_)
  have mono := Nat.mul_le_mul_left B card
  have cubic : B*(B+1)+B+(B+1)+1 ≤ B^3 := by
    have sq : 3*B^2≤B*B^2 := Nat.mul_le_mul_right _ B3
    have num : 3*B≤B*B := Nat.mul_le_mul_right B B3
    nlinarith
  omega

/-- The local bit routine may assume this concrete finite precision,
cubic bounds for the block primes, and room for the corrective comparison. -/
def LocalSpec (F : Template 3) : Prop := ∀ {V : ℕ} (A : Matrix V) (k s L : Fin V),
  27<V → L.val=V-1 →
  (∀ t≤s.val, ∀ p∈primeSet k.val t, p^3<V) →
  (∏ i : Fin V,rowWord (A i))+2^s.val<block k.val 0 →
  F.eval A ![k,s,L]=(∏ i : Fin V,rowWord (A i)).testBit s.val


private abbrev total {U : ℕ} (A : Matrix U) := ∏ i : Fin U,rowWord (A i)

private def widen {U : ℕ} (A : Matrix U) : Matrix (U*U) :=
  fun r c => (HABProductPadding.factor A r.val).testBit c.val

private theorem widen_total {U : ℕ} (hU : 2≤U) (A : Matrix U) : total (widen A)=total A := by
  have row (r : Fin (U*U)) : rowWord (widen A r)=HABProductPadding.factor A r.val :=
    rowWord_natural (HABProductPadding.factor_fits hU A _)
  have natural (n : ℕ) (f : ℕ → ℕ) : (∏ r : Fin n, f r.val)=productPrefix f n := by
    induction n with
    | zero => simp [productPrefix]
    | succ n ih => rw [Fin.prod_univ_castSucc,product_succ,←ih]; rfl
  change (∏ r : Fin (U*U),rowWord (widen A r))=_
  simp_rw [row]
  rw [natural,HABProductPadding.product_factor hU]

private noncomputable def once {k : ℕ} (q : Template k) : Template k :=
  .ex (.conj (fromFormula (isNat 0 0)) (compileTemplate @HABProductPadding.cell q (fun _ => 0) Fin.succ))

private theorem once_correct {U k : ℕ} (q : Template k) (A : Matrix U) (e : Fin k → Fin U)
    (pos : 0<U) :
    (once q).eval A e=q.eval (widen A) (fun j => HABSpacePadding.index (e j) 1) := by
  apply Bool.eq_iff_iff.mpr
  rw [once,Tex_true]
  simp only [Tconj_true,fromFormula_eval,isNat_spec,Fin.cases_zero]
  have check (z : Fin U) (hz : z.val=0) :
      (compileTemplate @HABProductPadding.cell q (fun _ => (0:Fin (k+1))) Fin.succ).eval A (Fin.cases z e)
        =q.eval (widen A) (fun j => HABSpacePadding.index (e j) 1) := by
    rw [compileTemplate_correct @HABProductPadding.cell _ _ _ A (widen A) _ (fun rh rl ch cl env =>
      HABProductPadding.cell_spec rh rl ch cl A env)]
    apply congrArg (q.eval (widen A))
    funext i
    change code z (e i)=code ⟨0,_⟩ (e i)
    exact congrArg (fun t => code t (e i)) (Fin.ext hz)
  exact ⟨fun ⟨z,hz,ok⟩ => (check z hz).symm.trans ok,fun ok => ⟨⟨0,pos⟩,rfl,(check _ rfl).trans ok⟩⟩

private noncomputable def pad {k : ℕ} : ℕ → Template k → Template k
  | 0,q => q
  | d+1,q => pad d (once q)

private def padded {U : ℕ} (A : Matrix U) : (d : ℕ) → Matrix (HABSpacePadding.size U d)
  | 0 => A
  | d+1 => widen (padded A d)

private theorem size_ge {U : ℕ} (hU : 2≤U) (d : ℕ) : 2≤HABSpacePadding.size U d := by
  rw [HABSpacePadding.size_eq]
  exact hU.trans (by simpa only [pow_one] using
    Nat.pow_le_pow_right (show 1≤U by omega) (Nat.one_le_two_pow (n:=d)))

private theorem pad_correct {k U : ℕ} (d : ℕ) (q : Template k) (A : Matrix U) (e : Fin k → Fin U)
    (hU : 2≤U) : (pad d q).eval A e=(q.eval (padded A d) fun j => HABSpacePadding.index (e j) d) := by
  induction d generalizing q with
  | zero => rfl
  | succ d ih =>
    rw [pad,ih,once_correct _ _ _ (by have := size_ge hU d; omega)]
    rfl

private theorem padded_total {U : ℕ} (A : Matrix U) (hU : 2≤U) (d : ℕ) :
    total (padded A d)=total A := by
  induction d with
  | zero => rfl
  | succ d ih => exact (widen_total (size_ge hU d) (padded A d)).trans ih

/-- Even the cube of the largest relevant prime fits the chosen universe.
The underlying bound on the nth prime is elementary. -/
theorem cube_bound {U s : ℕ} (hU : 2≤U) (hs : s<U*U) {t p : ℕ} (ht : t≤s)
    (mem : p ∈ primeSet (U*U+1) t) : p^3 < U^256 := by
  obtain ⟨j,hj,e⟩ := mem_primeSet.mp mem
  have prime := prime_bound ht hj
  rw [←e] at prime
  have W := Nat.mul_self_le_mul_self hU
  have almost : (s+1)*(U*U+1)+2 ≤ 4*U^4 := by
    have le := Nat.mul_le_mul_right (U*U+1) hs
    have sq : U^2≤U^4 := Nat.pow_le_pow_right (by omega) (by decide)
    nlinarith
  have four : 4≤U^2 := by simpa only [pow_two] using W
  have poly : (s+1)*(U*U+1)+2≤U^6 := calc
    _ ≤ 4*U^4 := almost
    _ ≤ U^2*U^4 := Nat.mul_le_mul_right _ four
    _ = _ := by ring
  have c32 : 32≤U^5 := by simpa using Nat.pow_le_pow_left hU 5
  have small : p<U^17 := calc
    _ < _ := prime
    _ ≤ U^5*(U^6)^2 := Nat.mul_le_mul c32 (Nat.pow_le_pow_left poly _)
    _ = U^17 := by ring
  calc
    p^3 < (U^17)^3 := Nat.pow_lt_pow_left small (by decide)
    _ = U^51 := (pow_mul ..).symm
    _ ≤ U^256 := Nat.pow_le_pow_right (by omega) (by decide)

private theorem position_lt {U : ℕ} (hi lo : Fin U) : hi.val*U+lo.val<U*U := calc
  _ < hi.val*U+U := Nat.add_lt_add_left lo.isLt _
  _ = (hi.val+1)*U := (Nat.succ_mul ..).symm
  _ ≤ U*U := Nat.mul_le_mul_right _ hi.isLt

private theorem product_room {U : ℕ} (A : Matrix U) {s : ℕ} (hs : s<U*U) :
    total A+2^s<block (U*U+1) 0 := by
  have hprod : total A≤2^(U*U) := calc
    total A ≤ ∏ _i : Fin U,2^U := Finset.prod_le_prod' (fun i _ => (rowWord_bound (A i)).le)
    _ = _ := by simp [pow_mul]
  calc
    _ < 2^(U*U)+2^(U*U) := Nat.add_lt_add_of_le_of_lt hprod (Nat.pow_lt_pow_right (by decide) hs)
    _ = 2^(U*U+1) := by rw [pow_succ,Nat.mul_two]
    _ ≤ _ := block_lower .. 

private def last {k : ℕ} (v : Fin k) : Template k := .neg (.ex (fromFormula (PrimeFormula.ltF v.succ 0)))

private theorem last_spec {k U : ℕ} (v : Fin k) (A : Matrix U) (e : Fin k → Fin U) :
    (last v).eval A e=true ↔ (e v).val+1=U := by
  simp only [last,Template.eval.eq_4,Bool.not_eq_true',←Bool.not_eq_true,Tex_true,fromFormula_eval,
    PrimeFormula.ltF_true,Fin.cases_succ,Fin.cases_zero,not_exists,not_lt]
  have bound := (e v).isLt
  exact ⟨fun h => by have := h ⟨U-1,by omega⟩; dsimp at this; omega,
    fun h i => by have := i.isLt; omega⟩

private def plusTwo {k : ℕ} (x y : Fin k) : Template k :=
  .ex (.conj (fromFormula (isNat 2 0)) (fromFormula (addF x.succ 0 y.succ)))

private theorem plusTwo_spec {k U : ℕ} (x y : Fin k) (A : Matrix U) (e : Fin k → Fin U) :
    (plusTwo x y).eval A e=true ↔ (e x).val+2=(e y).val := by
  simp only [plusTwo,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,addF_spec,Fin.cases_zero,Fin.cases_succ]
  exact ⟨fun ⟨z,h,eq⟩ => h ▸ eq,fun h => ⟨⟨2,by have := (e y).isLt; omega⟩,rfl,h⟩⟩

/-- The large-domain formula receives the last index of U² and the bit
position; it selects k = U²+1 and L = V−1 inside the larger domain. -/
private def inner (F : Template 3) : Template 2 :=
  .ex (.ex (.conj (last 0) (.conj (plusTwo 2 1)
    (rewriteMatrix (fun r c => .entry r c) F ![1,3,0]))))

private theorem inner_correct {V k s : ℕ} (F : Template 3) (valid : LocalSpec F) (A : Matrix V)
    (a j : Fin V) (ha : a.val+2=k) (hj : j.val=s) (fits : k<V) (big : 27<V)
    (size : ∀t≤s, ∀p∈primeSet k t,p^3<V) (room : total A+2^s<block k 0) :
    (inner F).eval A ![a,j]=true ↔ (total A).testBit s=true := by
  simp only [inner,Tex_true,Tconj_true,last_spec,plusTwo_spec,Fin.cases_zero]
  let E (b L : Fin V) : Fin 4 → Fin V := Fin.cases L (Fin.cases b ![a,j])
  have call (b L : Fin V) (bk : b.val=k) (lastL : L.val+1=V) :
      (rewriteMatrix (fun r c => .entry r c) F (![1,3,0] : Fin 3 → Fin 4)).eval A (E b L)
        = (total A).testBit s := by
    rw [rewriteMatrix_eval _ A A (by intros; rfl)]
    have args : E b L ∘ ![1,3,0]=![b,j,L] := by funext i; fin_cases i <;> rfl
    rw [args,valid A b j L big (by omega)
      (fun t ht p hp => size t (hj ▸ ht) p (bk ▸ hp)) (by rwa [bk,hj])]
    rw [hj]
  change (∃ b L : Fin V, L.val+1=V ∧ a.val+2=b.val ∧ _) ↔ _
  constructor
  · rintro ⟨b,L,hL,hk,ok⟩
    exact (call b L (hk.symm.trans ha) hL).symm.trans ok
  · intro ok
    let L : Fin V := ⟨V-1,by omega⟩
    have lastL : L.val+1=V := by dsimp [L]; omega
    exact ⟨⟨k,fits⟩,L,lastL,ha,(call _ L rfl lastL).trans ok⟩


private noncomputable def mid (F : Template 3) : Template 1 :=
  .ex (.conj (last 0) (pad 7 (inner F)))

/-- Compile a fixed CRT bit routine to a fixed HAB source formula. The
first square combines the two index digits; seven further squarings make
room for all primes and for the comparison precision. -/
noncomputable def source (F : Template 3) : Form 2 :=
  toSource (compileTemplate @HABProductPadding.cell (mid F) (fun _ => 0) (fun _ => 1))

theorem source_correct (F : Template 3) (valid : LocalSpec F) {U : ℕ} (hU : 2≤U)
    (A : Matrix U) (hi lo : Fin U) :
    (source F).Holds A (pairEnv hi lo) ↔ (total A).testBit (hi.val*U+lo.val)=true := by
  let W := U*U
  let V := HABSpacePadding.size W 7
  let B := widen A
  let C := padded B 7
  let j := code hi lo
  let s := hi.val*U+lo.val
  have jv : j.val=s := by change lo.val+U*hi.val=_; dsimp [s]; ring
  have W4 : 4≤W := Nat.mul_self_le_mul_self hU
  have Vpow : V=U^256 := by
    change HABSpacePadding.size (U*U) 7=_
    rw [HABSpacePadding.size_eq,←pow_two,←pow_mul]
    rfl
  have big : 27<V := by
    rw [Vpow]
    calc
      27 < 2^5 := by decide
      _ ≤ U^5 := Nat.pow_le_pow_left hU _
      _ ≤ U^256 := Nat.pow_le_pow_right (by omega) (by decide)
  have fits : W+1<V := by
    rw [Vpow]
    calc
      W+1 < U^3 := by change U*U+1<U^3; nlinarith [Nat.mul_le_mul_right (U*U) hU,Nat.mul_self_le_mul_self hU]
      _ ≤ U^256 := Nat.pow_le_pow_right (by omega) (by decide)
  have totalEq : total C=total A := (padded_total B (by omega : 2≤W) 7).trans (widen_total hU A)
  have hs : s<W := position_lt hi lo
  have small (t : ℕ) (ht : t≤s) (p : ℕ) (hp : p∈primeSet (W+1) t) : p^3<V := by
    rw [Vpow]; exact cube_bound hU hs ht hp
  have room : total C+2^s<block (W+1) 0 := by rw [totalEq]; exact product_room A hs
  have cand (a : Fin W) (ha : a.val+1=W) :
      (pad 7 (inner F)).eval B (Fin.cases a (fun _ : Fin 1 => j))=true ↔ (total A).testBit s=true := by
    rw [pad_correct _ _ _ _ (by omega : 2≤W)]
    let na := HABSpacePadding.index a 7
    let nj := HABSpacePadding.index j 7
    have ev : (fun i : Fin 2 => HABSpacePadding.index ((Fin.cases a (fun _ : Fin 1 => j) : Fin 2 → Fin W) i) 7)
        = ![na,nj] := by funext i; fin_cases i <;> rfl
    rw [ev,←totalEq]
    exact inner_correct F valid C na nj (by dsimp [na]; rw [HABSpacePadding.index_val]; omega)
      (by dsimp [nj]; rw [HABSpacePadding.index_val,jv]) fits big small room
  rw [source,toSource_correct,compileTemplate_correct @HABProductPadding.cell _ _ _ A B _
    (fun rh rl ch cl e => HABProductPadding.cell_spec rh rl ch cl A e)]
  change (mid F).eval B (fun _ : Fin 1 => j)=true ↔ _
  rw [mid,Tex_true]
  simp only [Tconj_true,last_spec,Fin.cases_zero]
  exact ⟨fun ⟨a,ha,ok⟩ => (cand a ha).mp ok,
    fun ok => ⟨⟨W-1,by omega⟩,by dsimp; omega,(cand _ (by dsimp; omega)).mpr ok⟩⟩

/-- The local arithmetic implementation with the stated explicit size
guarantees suffices for both output coordinates of HAB's iterated multiplication. -/
theorem imult_of_local (F : Template 3) (valid : LocalSpec F) : ImultInFOM :=
  ⟨source F,fun hU A hi lo => source_correct F valid hU A hi lo⟩

end DiophantineNP.HABWideOutput
