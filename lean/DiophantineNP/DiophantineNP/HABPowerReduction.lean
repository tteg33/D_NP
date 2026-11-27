import DiophantineNP.HABPowerCode
import DiophantineNP.HABPowerRows
import DiophantineNP.HABMatrixBind
import DiophantineNP.HABPairInterpretation

/-! Reducing a prime modular-power query to products of short lists. -/
namespace DiophantineNP.HABPowerReduction
open Finset HABGroupPower WidthFormula

/-- All exponent coefficients are encoded in one scalar smaller than the
product of the basis primes. The coefficient at a prime is read by division. -/
theorem pack_weights {s : Finset ℕ} (prime : ∀ d ∈ s, Nat.Prime d)
    (u : ℕ → ℕ) (small : ∀ d ∈ s, u d < d) :
    ∃ h < modulus s, ∀ d ∈ s, h%d=u d := by
  have pair : Set.Pairwise (s : Set ℕ) (fun a b => a.Coprime b) := by
    intro a ha b hb ne
    exact (prime a ha).coprime_iff_not_dvd.mpr fun dvd =>
      ne (((prime b hb).dvd_iff_eq (prime a ha).ne_one).mp dvd).symm
  let h := Nat.chineseRemainderOfFinset u id s (fun d hd => (prime d hd).ne_zero) pair
  refine ⟨h.val,Nat.chineseRemainderOfFinset_lt_prod ..,fun d hd => ?_⟩
  exact Eq.trans (h.property d hd) (Nat.mod_eq_of_lt (small d hd))

/-- Multiplication modulo n² implements addition on values represented by
1+n*x. This allows one ordinary modular-product operation to do both jobs in
the reduction. -/
theorem product_linear (s : Finset ℕ) (v : ℕ → ℕ) (n : ℕ) :
    (∏ d ∈ s, (1+n*v d)) ≡ 1+n*(∑ d ∈ s,v d) [MOD n*n] := by
  induction s using Finset.induction_on with
  | empty => simp [Nat.ModEq]
  | @insert d s hd ih =>
    rw [Finset.prod_insert hd,Finset.sum_insert hd]
    apply (ih.mul_left _).trans
    have h : (1+n*v d)*(1+n*(∑ j ∈ s,v j)) =
        (1+n*(v d+∑ j ∈ s,v j))+(n*n)*(v d*(∑ j ∈ s,v j)) := by ring
    rw [h,Nat.ModEq,Nat.add_mul_mod_self_left]

private theorem prod_exps (a : ℕ) (s : Finset ℕ) (v : ℕ → ℕ) :
    ∏ d ∈ s, a^(v d) = a^(∑ d ∈ s,v d) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert d s hd ih => simp only [prod_insert hd,sum_insert hd,ih,pow_add]

private theorem residue_product (s : Finset ℕ) (f : ℕ → ℕ) (p : ℕ) :
    (∏ d ∈ s,f d%p) ≡ (∏ d ∈ s,f d) [MOD p] := by
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert d s hd ih => simpa only [prod_insert hd] using (Nat.mod_modEq (f d) p).mul ih

private def rowExponent (D h n d : ℕ) : ℕ :=
  if d ∈ D.primeFactors then h%d*(n/d) else 0

/-- Each padded root row is the contribution of its CRT coefficient. -/
def residueRow (D h a p d : ℕ) : ℕ := a^(rowExponent D h (p-1) d)%p

private theorem row_sum {s : Finset ℕ} (prime : ∀ d ∈ s, Nat.Prime d)
    (u : ℕ → ℕ) {h K n : ℕ} (packed : ∀ d ∈ s, h%d=u d) (small : ∀ d ∈ s,d<K) :
    ∑ d ∈ range K,rowExponent (modulus s) h n d = ∑ d ∈ s,u d*(n/d) := by
  simp only [rowExponent,basis_code prime,←Finset.sum_filter]
  have eq : (range K).filter (· ∈ s) = s := by
    ext d
    simp only [mem_filter,mem_range,and_iff_right_iff_imp]
    exact small d
  rw [eq]
  exact sum_congr rfl (fun d hd => by rw [packed d hd])

/-- A scalar certificate. The largest numerical objects guessed here are D
and h, both polynomial in the group order. There is no chosen function on
the basis or guessed table of roots. -/
def Certificate (p a r b D h c K : ℕ) : Prop :=
  let n := p-1
  n < D ∧ h < D ∧ Squarefree D ∧
  (∀ d ∈ D.primeFactors, n.Coprime d ∧ d<K) ∧
  c ≤ K*K ∧
  (c + ∑ d ∈ range K, rowExponent D h n d) ≡ r [MOD n] ∧
  (a^c * ∏ d ∈ range K,residueRow D h a p d)%p=b

/-- Correctness of scalar existential witnesses. Numerical powers in the
last row of the displayed certificate will be accessed through unique
small-root tests. -/
theorem certificate_iff {p a : ℕ} (prime : p.Prime) (ha : 0<a) (hap : a<p) (r b : ℕ) :
    a^r%p=b ↔ ∃ D ≤ (p-1)*primeBound (p-1), ∃ h c, Certificate p a r b D h c (primeBound (p-1)) := by
  let n := p-1
  let K := primeBound n
  have npos : 0<n := Nat.sub_pos_of_lt prime.one_lt
  have expEq (D h c : ℕ) (cg : (c+∑ d ∈ range K,rowExponent D h n d) ≡ r [MOD n]) :
      (a^c * ∏ d ∈ range K,residueRow D h a p d)%p = a^r%p := by
    let v := rowExponent D h n
    have product := (residue_product (range K) (fun d => a^(v d)) p).mul_left (a^c)
    change _ ≡ _ [MOD p]
    apply product.trans
    rw [prod_exps,←pow_add]
    have e : (c+∑ d ∈ range K,v d)%n = r%n := cg
    exact ((ShortResidue.reduce_exponent (p := p) prime ha hap _).symm.trans
      ((congrArg (fun j => a^j%p) e).trans (ShortResidue.reduce_exponent prime ha hap r)))
  constructor
  · intro pow
    obtain ⟨s,card,lo,hi,hs⟩ := basis_exists n npos
    have hp (d) (mem : d ∈ s) := (hs d mem).1
    obtain ⟨u,c,hu,hc,congr⟩ := exponent_factorization hp (Nat.mod_lt r npos) lo
    obtain ⟨h,hlo,packed⟩ := pack_weights hp u hu
    have square : Squarefree (modulus s) := Finset.squarefree_prod_of_pairwise_isCoprime
      (fun i hi j hj ne => Nat.coprime_iff_isRelPrime.mp ((hp i hi).coprime_iff_not_dvd.mpr
        fun dvd => ne (((hp j hj).dvd_iff_eq (hp i hi).ne_one).mp dvd).symm))
      (fun i mem => (hp i mem).squarefree)
    have eq := row_sum (n := n) hp u packed (fun i hi => (hs i hi).2.2)
    have cg := congr.trans (Nat.mod_modEq r n)
    rw [←eq] at cg
    have len : n.log2+1 ≤ K := by
      dsimp [K,primeBound]
      nlinarith [Nat.zero_le ((n.log2+1)^2)]
    have bound : c ≤ K*K := calc
      c ≤ ∑ i ∈ s,u i := hc
      _ ≤ ∑ _i ∈ s,K := sum_le_sum fun i mem => ((hu i mem).trans (hs i mem).2.2).le
      _ = s.card*K := by simp
      _ ≤ K*K := Nat.mul_le_mul_right _ (card.trans len)
    exact ⟨_,hi,h,c,lo,hlo,square,fun i mem => (hs i ((basis_code hp) ▸ mem)).2,
      bound,cg,(expEq _ _ _ cg).trans pow⟩
  · rintro ⟨D,_,h,c,_,_,_,_,_,cg,hb⟩
    exact (expEq _ _ _ cg).symm.trans hb

private theorem card_units (p : ℕ) (prime : p.Prime) : Nat.card (ZMod p)ˣ = p-1 := by
  letI : Fact p.Prime := ⟨prime⟩
  rw [Nat.card_eq_fintype_card,ZMod.card_units]

private theorem pow_val {p : ℕ} [NeZero p] (u : (ZMod p)ˣ) (e : ℕ) :
    ((u^e : (ZMod p)ˣ) : ZMod p).val = (u : ZMod p).val^e%p := by
  rw [←ZMod.val_natCast,Nat.cast_pow,ZMod.natCast_zmod_val,Units.val_pow_eq_pow_val]

private def toUnit {p : ℕ} [Fact p.Prime] (a : ℕ) (ha : 0<a) (hap : a<p) : (ZMod p)ˣ :=
  Units.mk0 (a : ZMod p) (fun h => ha.ne' <| (ZMod.val_natCast_of_lt hap).symm.trans
    ((ZMod.val_eq_zero _).2 h))

private theorem toUnit_val {p : ℕ} [Fact p.Prime] (a : ℕ) (ha : 0<a) (hap : a<p) :
    (toUnit a ha hap : ZMod p).val = a := ZMod.val_natCast_of_lt hap

/-- The row holding a basis prime uses three short powers. Their exponents
are d, (p-1) mod d, and h mod d. All are bounded by the same prime cutoff. -/
theorem activeRow_iff {p a d D h y : ℕ} (prime : p.Prime) (ha : 0<a) (hap : a<p)
    (mem : d ∈ D.primeFactors) (cop : (p-1).Coprime d) :
    y=residueRow D h a p d ↔ ∃ x, 0<x ∧ x<p ∧
      ((x^d%p)*(a^((p-1)%d)%p))%p=1 ∧ y=x^(h%d)%p := by
  letI : Fact p.Prime := ⟨prime⟩
  let g := toUnit a ha hap
  have gv : (g : ZMod p).val=a := toUnit_val .. 
  have gn := card_units p prime
  have rootEq (v : (ZMod p)ˣ) : ((v^d)*g^((p-1)%d)=1) ↔ v=g^((p-1)/d) := by
    rw [←gn,mul_eq_one_iff_eq_inv,root_test g v (gn ▸ cop)]
  have valEq (v : (ZMod p)ˣ) :
      (((v : ZMod p).val^d%p)*(a^((p-1)%d)%p))%p=1 ↔ (v^d)*g^((p-1)%d)=1 := by
    rw [←gv,←pow_val,←pow_val,←ZMod.val_mul]
    change ((↑(v^d*g^((p-1)%d)) : ZMod p).val = 1) ↔ _
    rw [←show (1 : ZMod p).val=1 from ZMod.val_one _]
    exact ⟨fun he => Units.ext (ZMod.val_injective _ he),fun he => by rw [he]; rfl⟩
  have target : residueRow D h a p d =
      ((↑((g^((p-1)/d))^(h%d)) : ZMod p).val) := by
    rw [←pow_mul,pow_val,gv]
    simp [residueRow,rowExponent,mem,Nat.mul_comm]
  constructor
  · rintro rfl
    let u := g^((p-1)/d)
    have pos : 0<(u : ZMod p).val := Nat.pos_of_ne_zero
      (fun z => u.ne_zero ((ZMod.val_eq_zero _).mp z))
    exact ⟨_,pos,ZMod.val_lt _,(valEq u).mpr ((rootEq u).mpr rfl),target.trans (pow_val u _)⟩
  · rintro ⟨x,hx,hxp,root,hval⟩
    let v := toUnit x hx hxp
    have vx : (v : ZMod p).val=x := toUnit_val ..
    have eq := (rootEq v).mp ((valEq v).mp (vx ▸ root))
    rw [target,←eq,pow_val,vx,hval]


open Counting FiniteArithmeticGap

/-- A single formula for products of short lists of residues. The input
matrix supplies the individual bits of each factor. Rows beyond the given
length have no effect on the specification. -/
structure ShortProducts where
  formula : Template 3
  correct {U : ℕ} (A : HAB.Matrix U) (len p b : Fin U) (f : ℕ → ℕ)
    (prime : p.val.Prime) (padding : (p.val+2)^30<U)
    (small : len.val ≤ (primeBound (p.val-1))^2+1)
    (values : ∀ i<len.val, f i<p.val)
    (bits : ∀ i j : Fin U, i.val<len.val → A i j=(f i.val).testBit j.val) :
    formula.eval A ![len,p,b]=true ↔ (∏ d ∈ range len.val,f d)%p.val=b.val

private def ren {k l : ℕ} (v : Template k) (slots : Fin k → Fin l) : Template l :=
  rewriteMatrix (fun r c => .entry r c) v slots

private theorem ren_spec {k l U : ℕ} (v : Template k) (slots : Fin k → Fin l)
    (A : HAB.Matrix U) (e : Fin l → Fin U) : (ren v slots).eval A e=v.eval A (e ∘ slots) :=
  rewriteMatrix_eval _ A A (by intros; rfl) v slots e

/-- Scalar powers with a polylogarithmically bounded exponent use a matrix
whose every row is the same input word. -/
def repeatFormula (prod : ShortProducts) : Template 4 :=
  HABMatrix.bind (.bit 2 0 : Template 6) prod.formula id ![1,2,3]

theorem repeatFormula_correct (prod : ShortProducts) {U : ℕ} (A : HAB.Matrix U)
    (a j p b : Fin U) (prime : p.val.Prime) (ha : a.val<p.val) (padding : (p.val+2)^30<U)
    (small : j.val ≤ (primeBound (p.val-1))^2) :
    (repeatFormula prod).eval A ![a,j,p,b]=true ↔ a.val^j.val%p.val=b.val := by
  rw [repeatFormula,HABMatrix.bind_spec]
  have args : ![a,j,p,b] ∘ (![1,2,3] : Fin 3 → Fin 4) = ![j,p,b] := by
    funext i; fin_cases i <;> rfl
  rw [args]
  change prod.formula.eval (fun _ k => a.val.testBit k.val) ![j,p,b]=true ↔ _
  simpa using prod.correct (fun _ k => a.val.testBit k.val) j p b (fun _ => a.val)
    prime padding (by omega) (fun _ _ => ha) (fun _ _ _ => rfl)

abbrev Administrative := HABPowerCode.Admin
abbrev LocalTest := HABPowerRows.LocalTest

/-- The two scalar arithmetic interfaces contain no unrestricted modular
power. In the local tests all three root-test exponents and c are short. -/
structure ScalarTests where
  admin : Template 6
  admin_correct {U : ℕ} (A : HAB.Matrix U) (p r D h c K : Fin U) (prime : p.val.Prime)
    (padding : (p.val+2)^30<U) :
    admin.eval A ![p,r,D,h,c,K] = true ↔ Administrative p r D h c K
  row : Template 8
  row_correct {U : ℕ} (A : HAB.Matrix U) (p a D h c K d y : Fin U) (prime : p.val.Prime)
    (padding : (p.val+2)^30<U) (ha : a.val<p.val) (hD : 0<D.val)
    (hk : K.val=primeBound (p.val-1)) (hc : c.val≤K.val*K.val) :
    row.eval A ![p,a,D,h,c,K,d,y] = true ↔ LocalTest p a D h c K d y

private def word (p a D h c K d : ℕ) :=
  if d=K then a^c%p else if d<K then residueRow D h a p d else 1

private theorem row_iff {p a r D h c K : ℕ} (prime : p.Prime) (ha : 0<a) (hap : a<p)
    (admin : Administrative p r D h c K) (d y : ℕ) :
    LocalTest p a D h c K d y ↔ y=word p a D h c K d := by
  rcases admin with ⟨_,_,_,_,_,hs,_,_⟩
  by_cases eq : d=K
  · simp [LocalTest,HABPowerRows.LocalTest,word,eq]
  by_cases lt : d<K
  · by_cases mem : d∈D.primeFactors
    · simpa [LocalTest,HABPowerRows.LocalTest,word,eq,lt,mem] using
        (activeRow_iff (D := D) (h := h) (y := y) prime ha hap mem (hs d mem).1).symm
    · simp [LocalTest,HABPowerRows.LocalTest,word,eq,lt,mem,residueRow,rowExponent,Nat.mod_eq_of_lt prime.one_lt]
  · simp [LocalTest,HABPowerRows.LocalTest,word,eq,lt]

private theorem word_lt {p : ℕ} (prime : p.Prime) (a D h c K d : ℕ) :
    word p a D h c K d < p := by
  unfold word residueRow
  split_ifs <;> first | apply Nat.mod_lt _ prime.pos | exact prime.one_lt

private theorem words_product (p : ℕ) (a D h c K : ℕ) :
    (∏ d ∈ range (K+1),word p a D h c K d)%p =
    (a^c * ∏ d ∈ range K,residueRow D h a p d)%p := by
  rw [Finset.prod_range_succ]
  have rows : (∏ d ∈ range K,word p a D h c K d) =
      ∏ d ∈ range K,residueRow D h a p d := by
    apply prod_congr rfl
    intro d hd
    simp [word,mem_range.mp hd,(mem_range.mp hd).ne]
  rw [rows,show word p a D h c K K=a^c%p by simp [word],Nat.mul_comm,Nat.mod_mul_mod]

private def rowBits (S : ScalarTests) : Template 11 :=
  .ex (.conj (ren S.row ![8,9,7,6,5,4,2,0]) (.bit 0 1))

private def lengthOK : Template 9 := .ex <| .conj (fromFormula (isNat 1 0))
  (.atom (.add 0 (1:Fin 9).succ (0:Fin 9).succ))

private def core (prod : ShortProducts) (S : ScalarTests) : Template 9 :=
  .conj lengthOK <| .conj (ren S.admin ![5,7,4,3,2,1])
    (HABMatrix.bind (rowBits S) prod.formula id ![0,5,8])

private theorem length_spec {U : ℕ} (A : HAB.Matrix U) (e : Fin 9 → Fin U) (hU : 1<U) :
    lengthOK.eval A e=true ↔ (e 0).val=(e 1).val+1 := by
  rw [lengthOK,Tex_true]
  simp only [Tconj_true,fromFormula_eval,isNat_spec,Fin.cases_zero]
  simp only [Template.eval,Atom.eval,decide_eq_true_eq,Fin.cases_succ,Fin.cases_zero]
  exact ⟨fun ⟨z,h,eq⟩ => by omega,fun eq => ⟨⟨1,hU⟩,rfl,by change 1+(e 1).val=(e 0).val; omega⟩⟩

private theorem general_core {U : ℕ} (prod : ShortProducts) (S : ScalarTests) (A : HAB.Matrix U)
    (L K c h D p a r b : Fin U) (prime : p.val.Prime) (ha : 0<a.val) (hap : a.val<p.val)
    (padding : (p.val+2)^30<U) :
    (core prod S).eval A ![L,K,c,h,D,p,a,r,b]=true ↔ L.val=K.val+1 ∧
      Administrative p r D h c K ∧ (a.val^c.val * ∏ d ∈ range K.val,residueRow D h a p d)%p.val=b.val := by
  have hU := prime.one_lt.trans p.isLt
  rw [core,Tconj_true,length_spec _ _ hU,Tconj_true,ren_spec]
  have args : ![L,K,c,h,D,p,a,r,b] ∘ (![5,7,4,3,2,1] : Fin 6 → Fin 9) = ![p,r,D,h,c,K] := by
    funext i; fin_cases i <;> rfl
  rw [args]
  change (L.val=K.val+1 ∧ S.admin.eval A ![p,r,D,h,c,K]=true ∧ _) ↔ _
  rw [S.admin_correct A p r D h c K prime padding]
  apply and_congr_right
  intro len
  apply and_congr_right
  intro admin
  have ⟨hk,_,hd,_,_,_,hc,_⟩ := admin
  have posD : 0<D.val := by omega
  let e : Fin 9 → Fin U := ![L,K,c,h,D,p,a,r,b]
  let f := word p a D h c K
  let bits (d j : Fin U) := (rowBits S).eval A (extend j d (e ∘ id))
  have bits_spec (d j : Fin U) : bits d j = (f d.val).testBit j.val := by
    apply Bool.eq_iff_iff.mpr
    dsimp only [bits]
    rw [rowBits,Tex_true]
    simp only [Tconj_true,ren_spec]
    have arg (y : Fin U) : (Fin.cases y (extend j d (e ∘ id)) : Fin 12 → Fin U) ∘
        (![8,9,7,6,5,4,2,0] : Fin 8 → Fin 12) = ![p,a,D,h,c,K,d,y] := by
      funext i; fin_cases i <;> rfl
    simp only [arg]
    change (∃ y : Fin U, S.row.eval A ![p,a,D,h,c,K,d,y]=true ∧ y.val.testBit j.val=true) ↔ _
    simp only [S.row_correct A p a D h c K d _ prime padding hap posD hk hc]
    constructor
    · rintro ⟨y,check,bit⟩
      change (word p a D h c K d).testBit j.val=true
      rwa [←((row_iff prime ha hap admin d y).mp check)]
    · intro bit
      exact ⟨⟨_,(word_lt prime ..).trans p.isLt⟩,(row_iff prime ha hap admin _ _).mpr rfl,bit⟩
  rw [HABMatrix.bind_spec]
  have foldArgs : ![L,K,c,h,D,p,a,r,b] ∘ (![0,5,8] : Fin 3 → Fin 9) = ![L,p,b] := by
    funext i; fin_cases i <;> rfl
  rw [foldArgs]
  change prod.formula.eval bits ![L,p,b]=true ↔ _
  have small : L.val≤(primeBound (p.val-1))^2+1 := by
    rw [len,←hk,pow_two]
    have pos : 0<K.val := by rw [hk]; unfold primeBound; positivity
    nlinarith
  rw [prod.correct bits L p b f prime padding small (fun _ _ => word_lt prime ..)
    (fun d j _ => bits_spec d j),len,words_product p.val]


set_option maxHeartbeats 900000 in
private theorem padding_bounds {p U : ℕ} (prime : p.Prime) (pad : (p+2)^30<U) :
    let K := primeBound (p-1)
    (p-1)*K < U ∧ K*K < U ∧ K+1 < U ∧ p*p<U := by
  let z := p+2
  have z4 : 4≤z := by dsimp [z]; have := prime.two_le; omega
  have logle : (p-1).log2 ≤ p := by
    have hh := Nat.log2_self_le (n := p-1)
    have hh' : (p-1).log2 < 2^((p-1).log2) := Nat.lt_two_pow_self
    have pp : p-1≠0 := by have := prime.one_lt; omega
    exact Nat.le_trans (hh'.le.trans (hh pp)) (Nat.sub_le ..)
  have quarter : 2*((p-1).log2+1)+2 ≤ 2*z := by dsimp [z]; omega
  have kbound : primeBound (p-1) ≤ 128*z^2 := calc
    _ ≤ 32*(2*z)^2 := by apply Nat.mul_le_mul_left; exact Nat.pow_le_pow_left quarter _
    _ = _ := by ring
  have coeff : 128≤z^4 := by calc
    _ ≤ 4^4 := by decide
    _ ≤ _ := Nat.pow_le_pow_left z4 _
  have k6 : primeBound (p-1) ≤ z^6 := calc
    _ ≤ 128*z^2 := kbound
    _ ≤ z^4*z^2 := Nat.mul_le_mul_right _ coeff
    _ = z^6 := by ring
  have zz : 1≤z := by omega
  have top : z^12 < U := (Nat.pow_le_pow_right zz (by decide : 12≤30)).trans_lt pad
  have posK : 0<primeBound (p-1) := by unfold primeBound; positivity
  have sq : primeBound (p-1)*primeBound (p-1) ≤ z^12 := calc
    _ ≤ z^6*z^6 := Nat.mul_le_mul k6 k6
    _ = _ := by ring
  have pb : p ≤ z^6 := (show p ≤ z from by dsimp [z]; omega).trans
    (by simpa only [pow_one] using Nat.pow_le_pow_right zz (by decide : 1≤6))
  have z6 : z^6*z^6=z^12 := by ring
  have small := Nat.mul_le_mul ((Nat.sub_le p 1).trans pb) k6
  have ps := Nat.mul_le_mul pb pb
  have kge : 2≤primeBound (p-1) := by unfold primeBound; nlinarith
  refine ⟨small.trans_lt (z6 ▸ top),sq.trans_lt top,?_,ps.trans_lt (z6 ▸ top)⟩
  have h1 := Nat.mul_le_mul_right (primeBound (p-1)) kge
  omega

private def positiveFormula (prod : ShortProducts) (S : ScalarTests) : Template 4 :=
  .ex (.ex (.ex (.ex (.ex (core prod S)))))

private theorem positive_spec (prod : ShortProducts) (S : ScalarTests) {U : ℕ}
    (A : HAB.Matrix U) (p a r b : Fin U) (prime : p.val.Prime) (ha : 0<a.val) (hap : a.val<p.val)
    (pad : (p.val+2)^30<U) :
    (positiveFormula prod S).eval A ![p,a,r,b]=true ↔ a.val^r.val%p.val=b.val := by
  have args (D h c K L : Fin U) :
      (Fin.cases L (Fin.cases K (Fin.cases c (Fin.cases h (Fin.cases D ![p,a,r,b])))) : Fin 9 → Fin U)
      = ![L,K,c,h,D,p,a,r,b] := by funext i; fin_cases i <;> rfl
  simp only [positiveFormula,Tex_true,args]
  simp_rw [general_core prod S A _ _ _ _ _ p a r b prime ha hap pad]
  rw [certificate_iff prime ha hap]
  constructor
  · rintro ⟨D,h,c,K,L,_,admin,eq⟩
    obtain ⟨hk,bD,lo,lh,sq,hs,hc,cg⟩ := admin
    exact ⟨_,hk ▸ bD,h,c,lo,lh,sq,hk ▸ hs,hk ▸ hc,hk ▸ cg,hk ▸ eq⟩
  · rintro ⟨D,bD,h,c,lo,lh,sq,hs,hc,cg,eq⟩
    let K := primeBound (p.val-1)
    obtain ⟨num,cs,ls,_⟩ := padding_bounds prime pad
    have fitD := bD.trans_lt num
    exact ⟨⟨D,fitD⟩,⟨h,lh.trans fitD⟩,⟨c,hc.trans_lt cs⟩,⟨K,by omega⟩,
      ⟨K+1,ls⟩,rfl,⟨rfl,bD,lo,lh,sq,hs,hc,cg⟩,eq⟩

private def isValue {k : ℕ} (n : ℕ) (i : Fin k) : Template k := fromFormula (isNat n i)

private theorem isValue_spec {k U : ℕ} (n : ℕ) (i : Fin k) (A : HAB.Matrix U) (e : Fin k → Fin U) :
    (isValue n i).eval A e=true ↔ (e i).val=n := by rw [isValue,fromFormula_eval,isNat_spec]

/-- The same four free variables handle zero and nonzero residues, all
natural exponents in the finite universe, and arbitrary proposed answers. -/
def formula (prod : ShortProducts) (S : ScalarTests) : Template 4 :=
  .disj (.conj (isValue 0 1) (.disj (.conj (isValue 0 2) (isValue 1 3))
    (.conj (.neg (isValue 0 2)) (isValue 0 3))))
    (.conj (.neg (isValue 0 1)) (positiveFormula prod S))

theorem formula_correct (prod : ShortProducts) (S : ScalarTests) {U : ℕ} (A : HAB.Matrix U)
    (p a r b : Fin U) (prime : p.val.Prime) (hap : a.val<p.val) (pad : (p.val+2)^30<U) :
    (formula prod S).eval A ![p,a,r,b]=true ↔ a.val^r.val%p.val=b.val := by
  have neg {k : ℕ} (v : Template k) (e : Fin k → Fin U) :
      v.neg.eval A e=true ↔ ¬v.eval A e=true := by simp [Template.eval]
  simp only [formula,Tdisj_true,Tconj_true,neg,isValue_spec]
  change ((a.val=0 ∧ ((r.val=0 ∧ b.val=1) ∨ (r.val≠0 ∧ b.val=0))) ∨
    (a.val≠0 ∧ (positiveFormula prod S).eval A ![p,a,r,b]=true)) ↔ _
  by_cases hz : a.val=0
  · constructor
    · rintro (⟨_,⟨hr,hb⟩|⟨hr,hb⟩⟩|⟨ne,_⟩)
      · rw [hz,hr,pow_zero,Nat.mod_eq_of_lt prime.one_lt,hb]
      · rw [hz,zero_pow hr,Nat.zero_mod,hb]
      · exact False.elim (ne hz)
    · intro result
      refine Or.inl ⟨hz,?_⟩
      by_cases hr : r.val=0
      · rw [hz,hr,pow_zero,Nat.mod_eq_of_lt prime.one_lt] at result
        exact Or.inl ⟨hr,result.symm⟩
      · rw [hz,zero_pow hr,Nat.zero_mod] at result
        exact Or.inr ⟨hr,result.symm⟩
  · simp [hz,positive_spec prod S A p a r b prime (Nat.pos_of_ne_zero hz) hap pad]


private def emptyInput : HABPairInterpretation.Input := fun _ _ _ x => .neg (.atom (.eqv x x))

private noncomputable def squareQuery {k : ℕ} (q : Template k) : Template k :=
  .ex (.conj (isValue 0 0) (HABPairInterpretation.compileTemplate @emptyInput q
    (fun _ => 0) Fin.succ))

private def widen {U : ℕ} (pos : 0<U) (x : Fin U) : Fin (U*U) :=
  HABPairInterpretation.code ⟨0,pos⟩ x

private theorem widen_val {U : ℕ} (pos : 0<U) (x : Fin U) : (widen pos x).val=x.val := by
  change x.val+U*0=x.val
  simp

private theorem squareQuery_spec {k U : ℕ} (q : Template k) (A : HAB.Matrix U) (e : Fin k → Fin U)
    (pos : 0<U) : (squareQuery q).eval A e=true ↔ q.eval (fun _ _ => false) (widen pos ∘ e)=true := by
  rw [squareQuery,Tex_true]
  simp only [Tconj_true,isValue_spec,Fin.cases_zero]
  have eq : (HABPairInterpretation.compileTemplate @emptyInput q (fun _ => (0 : Fin (k+1))) Fin.succ).eval A
      (Fin.cases ⟨0,pos⟩ e) = q.eval (fun _ _ => false) (widen pos ∘ e) := by
    apply HABPairInterpretation.compileTemplate_correct
    intro m rh rl ch cl env
    simp [emptyInput,Template.eval,Atom.eval]
  constructor
  · rintro ⟨z,hz,hv⟩
    have : z=(⟨0,pos⟩ : Fin U) := Fin.ext hz
    rw [this,eq] at hv
    exact hv
  · exact fun h => ⟨⟨0,pos⟩,rfl,eq.trans h⟩

private def squarings (n U : ℕ) := U^(2^n)

private theorem square_more (n U : ℕ) : squarings (n+1) U = squarings n (U*U) := by
  simp only [squarings,pow_succ 2 n,←pow_two,←pow_mul,Nat.mul_comm]

private noncomputable def repeatSquares {k : ℕ} (q : Template k) : ℕ → Template k
  | 0 => q
  | n+1 => squareQuery (repeatSquares q n)

private theorem repeated_correct (prod : ShortProducts) (S : ScalarTests) (n : ℕ) {U : ℕ}
    (A : HAB.Matrix U) (p a r b : Fin U) (prime : p.val.Prime) (hap : a.val<p.val)
    (pad : (p.val+2)^30<squarings n U) :
    (repeatSquares (formula prod S) n).eval A ![p,a,r,b]=true ↔ a.val^r.val%p.val=b.val := by
  induction n generalizing U with
  | zero => exact formula_correct prod S A p a r b prime hap (by simpa [squarings] using pad)
  | succ n ih =>
    have pos := prime.pos.trans p.isLt
    rw [repeatSquares,squareQuery_spec _ _ _ pos]
    have e : widen pos ∘ ![p,a,r,b] = ![widen pos p,widen pos a,widen pos r,widen pos b] := by
      funext i; fin_cases i <;> rfl
    rw [e]
    rw [square_more] at pad
    simpa only [widen_val] using ih (fun _ _ => false) (widen pos p) (widen pos a) (widen pos r) (widen pos b)
      (by simpa only [widen_val] using prime) (by simpa only [widen_val] using hap)
      (by simpa only [widen_val] using pad)

private theorem six_squares {U p : ℕ} (prime : p.Prime) (hp : p<U) : (p+2)^30<squarings 6 U := by
  have hu : 1<U := prime.one_lt.trans hp
  have lo : p+2≤U^2 := by nlinarith
  calc
    (p+2)^30 ≤ (U^2)^30 := Nat.pow_le_pow_left lo _
    _ = U^60 := (pow_mul ..).symm
    _ < U^64 := Nat.pow_lt_pow_right hu (by decide)
    _ = squarings 6 U := rfl

/-- Six applications of the square interpretation remove the polynomial
padding condition. The resulting syntax uses only HAB's source vocabulary. -/
noncomputable def sourceFromTests (prod : ShortProducts) (S : ScalarTests) : HAB.Form 4 :=
  HAB.toSource (repeatSquares (formula prod S) 6)

theorem sourceFromTests_correct (prod : ShortProducts) (S : ScalarTests) {U : ℕ}
    (A : HAB.Matrix U) (p a r b : Fin U) (prime : p.val.Prime) (hap : a.val<p.val) :
    (sourceFromTests prod S).Holds A ![p,a,r,b] ↔ a.val^r.val%p.val=b.val := by
  rw [sourceFromTests,HAB.toSource_correct]
  exact repeated_correct prod S 6 A p a r b prime hap (six_squares prime p.isLt)

private noncomputable def scalarTests (prod : ShortProducts) : ScalarTests where
  admin := HABPowerCode.formula
  admin_correct A p r D h c K hp pad := HABPowerCode.formula_correct A ![p,r,D,h,c,K] hp pad.le
  row := HABPowerRows.row (repeatFormula prod)
  row_correct A p a D h c K d y hp pad ha hD hk hc := by
    have oracle : HABPowerRows.OracleAt (repeatFormula prod) A p (K.val*K.val) := by
      intro g j z hg hj
      exact (repeatFormula_correct prod A g j p z hp hg pad
        (by simpa only [hk,pow_two] using hj)).trans eq_comm
    exact HABPowerRows.row_spec _ A p a D h c K d y oracle hp ha hD
      (by rw [hk]; unfold primeBound; positivity) hc (padding_bounds hp pad).2.2.2

/-- One fixed formula in order, BIT, and strict majority for the entire
prime modular-power query, given only a bit-graph product for short lists.
The source formula has four free variables p,a,r,b. -/
noncomputable def source (prod : ShortProducts) : HAB.Form 4 :=
  sourceFromTests prod (scalarTests prod)

/-- No padding or short-exponent restriction on the source query. -/
theorem source_correct (prod : ShortProducts) {U : ℕ} (A : HAB.Matrix U) (p a r b : Fin U)
    (prime : p.val.Prime) (hap : a.val<p.val) :
    (source prod).Holds A ![p,a,r,b] ↔ a.val^r.val%p.val=b.val :=
  sourceFromTests_correct prod _ A p a r b prime hap


private noncomputable def remainder {k : ℕ} (x p r : Fin k) : HAB.Form k :=
  HAB.toSource (fromFormula (.ex (HABBinaryResidue.qr x.succ p.succ 0 r.succ)))

private theorem remainder_correct {k U : ℕ} (x p r : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U)
    (hp : 0<(e p).val) : (remainder x p r).Holds A e ↔ (e r).val=(e x).val%(e p).val := by
  simp only [remainder,HAB.toSource_correct,fromFormula_eval,PrimeFormula.exists_true,
    HABBinaryResidue.qr_true,Fin.cases_succ,Fin.cases_zero,hp,true_and]
  constructor
  · rintro ⟨_,_,h⟩; exact h
  · exact fun h => ⟨⟨_,(Nat.div_le_self ..).trans_lt (e x).isLt⟩,rfl,h⟩

/-- The paper's ordering POW(a,r,b,p) and its congruence semantics. Input
base and answer can exceed p. -/
noncomputable def primePOW (prod : ShortProducts) : HAB.Form 4 :=
  .ex (.ex (.conj (remainder 2 5 1) (.conj (remainder 4 5 0) ((source prod).rename ![5,1,3,0]))))

theorem primePOW_correct (prod : ShortProducts) {U : ℕ} (A : HAB.Matrix U) (a r b p : Fin U)
    (prime : p.val.Prime) :
    (primePOW prod).Holds A ![a,r,b,p] ↔ a.val^r.val ≡ b.val [MOD p.val] := by
  let e (g y : Fin U) : Fin 6 → Fin U := Fin.cases y (Fin.cases g ![a,r,b,p])
  have e1 (g y : Fin U) := remainder_correct (2:Fin 6) 5 1 A (e g y) prime.pos
  have e2 (g y : Fin U) := remainder_correct (4:Fin 6) 5 0 A (e g y) prime.pos
  have call (g y : Fin U) (hg : g.val<p.val) :
      ((source prod).rename (![5,1,3,0] : Fin 4 → Fin 6)).Holds A (e g y) ↔ g.val^r.val%p.val=y.val := by
    rw [HAB.Form.rename_correct]
    have u : e g y ∘ (![5,1,3,0] : Fin 4 → Fin 6)=![p,g,r,y] := by funext i; fin_cases i <;> rfl
    rw [u,source_correct prod A p g r y prime hg]
  change (∃ g y : Fin U,(remainder 2 5 1).Holds A (e g y) ∧
    (remainder 4 5 0).Holds A (e g y) ∧ _ ) ↔ _
  have powmod : (a.val%p.val)^r.val ≡ a.val^r.val [MOD p.val] := (Nat.mod_modEq ..).pow _
  constructor
  · rintro ⟨g,y,hg,hy,ok⟩
    have gv : g.val=a.val%p.val := (e1 g y).mp hg
    have yv : y.val=b.val%p.val := (e2 g y).mp hy
    have q := (call g y (gv ▸ Nat.mod_lt _ prime.pos)).mp ok
    exact Eq.trans powmod.symm (by rwa [gv,yv] at q)
  · intro congr
    let g : Fin U := ⟨a.val%p.val,(Nat.mod_lt _ prime.pos).trans p.isLt⟩
    let y : Fin U := ⟨b.val%p.val,(Nat.mod_lt _ prime.pos).trans p.isLt⟩
    exact ⟨g,y,(e1 g y).mpr rfl,(e2 g y).mpr rfl,(call g y (Nat.mod_lt _ prime.pos)).mpr (powmod.trans congr)⟩

end DiophantineNP.HABPowerReduction
