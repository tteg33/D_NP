import DiophantineNP.HABMatrixBind
import DiophantineNP.HABBinaryResidue

/-! # Iterated residue product for all rows of the finite universe

A square array of side ceil(sqrt U) holds the U factors and is padded
with ones. Both successive products have few enough factors for the
short prime algorithm. The side length is defined in finite arithmetic
by the first square that leaves the universe. -/

namespace DiophantineNP.HABProductBlocks
open Counting PrimeFormula WidthFormula FiniteArithmeticGap ShortResidue

private def padded (f : ℕ→ℕ) (U m g r : ℕ) : ℕ :=
  if g*m+r<U then f (g*m+r) else 1

private def addr : Predicate :=
  Predicate.ex 4 <| (Predicate.mul 2 3 4).both <|
    Predicate.ex 5 <| (Predicate.add 4 1 5).both (Predicate.entry 5 0)

private def fitsAddr : Predicate :=
  Predicate.ex 4 <| (Predicate.mul 2 3 4).both <| Predicate.ex 5 (Predicate.add 4 1 5)

/-- Address a cell of the square, falling back to the multiplicative identity
when the row lies outside the original matrix. Free slots are value, offset,
square row and side length. -/
private def paddedCell : Template 4 :=
  (addr.either (fitsAddr.neg.both (Predicate.eqN 0 1))).syntaxF
    (fun z => if z=0 then 0 else if z=1 then 1 else if z=2 then 2 else 3)

private theorem paddedCell_spec {U p : ℕ} (f : ℕ→ℕ) (hp : 1<p) (v : Fin 4 → Fin U) :
    paddedCell.eval (fun r b => decide (b.val=f r.val%p)) v =
      decide ((v 0).val=padded f U (v 3).val (v 2).val (v 1).val%p) := by
  apply Bool.eq_iff_iff.mpr
  let table := fun r b : ℕ => decide (b=f r%p)
  rw [paddedCell,Predicate.valid _ _ table]
  simp only [addr, fitsAddr, Predicate.either, Predicate.ex, Predicate.both, Predicate.add,
    Predicate.mul, Predicate.entry, Predicate.neg, Predicate.eqN, table, decide_eq_true_eq,
    Function.update, if_true]
  change ((∃a<U, (v 2).val*(v 3).val=a ∧ ∃b<U, a+(v 1).val=b ∧ (v 0).val=f b%p) ∨
      (¬∃a<U, (v 2).val*(v 3).val=a ∧ ∃b<U, a+(v 1).val=b) ∧ (v 0).val=1) ↔ _
  rw [padded]
  split
  · rename_i hi
    rw [or_iff_left (by rintro ⟨hn,_⟩; exact hn ⟨_,by omega,rfl,_,hi,rfl⟩)]
    constructor
    · rintro ⟨_,_,rfl,_,_,rfl,h⟩; exact h
    · intro h; exact ⟨_,by omega,rfl,_,hi,rfl,h⟩
  · rename_i hi
    rw [Nat.mod_eq_of_lt hp]
    constructor
    · rintro (⟨_,_,rfl,_,hz,rfl,_⟩|⟨_,h⟩) <;> omega
    · intro h; exact Or.inr ⟨fun ⟨a,_,ha,b,hb,hsum⟩ => hi (by omega),h⟩

/-- Group residue predicate. Free slots are proposed residue, group number,
group length and modulus, in that order. -/
private noncomputable def groupCell : Template 4 :=
  HABMatrix.bind paddedCell productResidue ![1,2] ![2,3,0]

private theorem groupCell_spec {U K : ℕ} (f : ℕ→ℕ) (v : Fin 4 → Fin U)
    (hp : (v 3).val.Prime) (hm : (v 2).val*(v 3).val<U-U/2) (hK : 2≤K)
    (hpk : (v 3).val≤2^K) (hcap : 2^((K+1)*K)<U) :
    groupCell.eval (fun r b => decide (b.val=f r.val%(v 3).val)) v =
      decide ((v 0).val=productPrefix (padded f U (v 2).val (v 1).val) (v 2).val%(v 3).val) := by
  rw [groupCell,HABMatrix.bind_spec]
  have mat (r b : Fin U) := paddedCell_spec f hp.one_lt (extend b r (v ∘ ![1,2]))
  have rel : (fun r b : Fin U => paddedCell.eval (fun r b => decide (b.val=f r.val%(v 3).val))
        (extend b r (v ∘ ![1,2]))) =
      fun r b => decide (b.val=padded f U (v 2).val (v 1).val r.val%(v 3).val) :=
    funext fun r => funext fun b => mat r b
  have he : v ∘ ![2,3,0] = ![v 2,v 3,v 0] := by funext i; fin_cases i <;> rfl
  rw [rel,he]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  exact productResidue_spec _ _ _ _ hp hm hK hpk hcap

private theorem prod_append (f : ℕ→ℕ) (n m : ℕ) :
    productPrefix f (n+m)=productPrefix f n*productPrefix (fun i => f (n+i)) m := by
  induction m with
  | zero => simp [productPrefix]
  | succ m ih => rw [← Nat.add_assoc,product_succ,ih,product_succ,mul_assoc]

private theorem grouped (f : ℕ→ℕ) (m n : ℕ) :
    productPrefix (fun g => productPrefix (fun r => f (g*m+r)) m) n = productPrefix f (n*m) := by
  induction n with
  | zero => simp [productPrefix]
  | succ n ih => rw [product_succ,ih,Nat.succ_mul,prod_append]

private noncomputable def folded {k : ℕ} (m p b : Fin k) : Template k :=
  HABMatrix.bind groupCell productResidue ![m,p] ![m,p,b]

private theorem folded_spec {k U K : ℕ} (m p b : Fin k) (v : Fin k → Fin U) (f : ℕ→ℕ)
    (hp : (v p).val.Prime) (hm : (v m).val*(v p).val<U-U/2) (hcov : U≤(v m).val*(v m).val)
    (hK : 2≤K) (hpk : (v p).val≤2^K) (hcap : 2^((K+1)*K)<U) :
    (folded m p b).eval (fun r b => decide (b.val=f r.val%(v p).val)) v = true ↔
      (v b).val=productPrefix f U%(v p).val := by
  rw [folded,HABMatrix.bind_spec]
  let groups := fun i => productPrefix (padded f U (v m).val i) (v m).val
  have mat (r c : Fin U) := groupCell_spec f (extend c r (v ∘ ![m,p])) hp hm hK hpk hcap
  have rel : (fun r c : Fin U => groupCell.eval (fun r b => decide (b.val=f r.val%(v p).val))
        (extend c r (v ∘ ![m,p]))) = fun r c => decide (c.val=groups r.val%(v p).val) :=
    funext fun r => funext fun c => mat r c
  have he : v ∘ ![m,p,b] = ![v m,v p,v b] := by funext i; fin_cases i <;> rfl
  rw [rel,he,productResidue_spec _ _ _ groups hp hm hK hpk hcap]
  have hg := grouped (fun i => if i<U then f i else 1) (v m).val (v m).val
  change productPrefix groups (v m).val = _ at hg
  rw [hg,product_pad f hcov]

private def sqFits {k : ℕ} (m : Fin k) : Formula k := .ex (.atom (.mul m.succ m.succ 0))

private theorem sqFits_spec {k U : ℕ} (m : Fin k) (v : Fin k → Fin U) :
    (sqFits m).eval v=true ↔ (v m).val*(v m).val<U := by
  rw [sqFits,exists_true]
  change (∃w : Fin U, decide ((v m).val*(v m).val=w.val)=true) ↔ _
  exact ⟨fun ⟨w,hw⟩ => (of_decide_eq_true hw) ▸ w.isLt, fun h => ⟨⟨_,h⟩,by simp⟩⟩

private def side {k : ℕ} (m : Fin k) : Formula k :=
  andF (notF (sqFits m)) (notF (.ex (andF (PrimeFormula.ltF 0 m.succ) (notF (sqFits 0)))))

private def IsSide (U m : ℕ) : Prop := U≤m*m ∧ ∀a<m, a*a<U

private theorem side_spec {k U : ℕ} (m : Fin k) (v : Fin k → Fin U) :
    (side m).eval v=true ↔ IsSide U (v m).val := by
  simp only [side,andF_spec,notF_spec,sqFits_spec,exists_true,PrimeFormula.ltF_true,
    Fin.cases_zero,Fin.cases_succ,not_lt,not_exists,not_and_or,not_le]
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨h,fun a ha => (h' ⟨a,ha.trans (v m).isLt⟩).resolve_left (by simpa using ha)⟩
  · rintro ⟨h,h'⟩
    exact ⟨h,fun a => by by_cases he : a.val<(v m).val; exact Or.inr (h' _ he); exact Or.inl (by omega)⟩

private theorem exists_side {U : ℕ} (hU : 3≤U) : ∃ m<U, IsSide U m := by
  have hh : ∃m, U≤m*m := ⟨U,Nat.le_mul_of_pos_right _ (by omega)⟩
  let m := Nat.find hh
  have hm := Nat.find_spec hh
  have hmin (k : ℕ) (hk : k<m) : k*k<U := by
    have hn := Nat.find_min hh hk
    omega
  refine ⟨m,?_,hm,hmin⟩
  by_contra! hu
  have h := hmin (U-1) (by omega)
  have : U-1+1=U := by omega
  nlinarith [Nat.mul_le_mul_left (U-1) (show 2≤U-1 by omega)]

private theorem side_budget {U K p m : ℕ} (hp : p.Prime) (hK : 2≤K) (hpk : p≤2^K)
    (hcap : 2^((K+1)*K)<U) (hs : IsSide U m) : m*p<U-U/2 := by
  have hpk' : p<2^K := by
    apply lt_of_le_of_ne hpk
    intro he
    have hd : 2∣p := he ▸ dvd_pow_self _ (by omega)
    have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
    have hh := Nat.pow_le_pow_right (n:=2) (by decide) hK
    omega
  have hbase : 2*p+1<2^(K+1) := by rw [pow_succ]; omega
  have he : (K+1)*2≤(K+1)*K := Nat.mul_le_mul_left _ hK
  have hsquare : (2*p+1)*(2*p+1)<U := calc
    _ < 2^(K+1)*2^(K+1) := Nat.mul_self_lt_mul_self hbase
    _ = 2^((K+1)*2) := by rw [pow_mul,pow_two]
    _ ≤ 2^((K+1)*K) := Nat.pow_le_pow_right (by decide) he
    _ < U := hcap
  have hm : 2*p+1<m := by
    by_contra! hx
    exact (not_lt_of_ge hs.1) ((Nat.mul_self_le_mul_self hx).trans_lt hsquare)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  have hh := hs.2 n (by omega)
  have hn : 2*p+1≤n := by omega
  have hmul := Nat.mul_le_mul_left n hn
  rw [Nat.succ_mul]
  have hstrict : 2*(n*p+p)<U := by nlinarith
  omega

/-- One fixed query for products of all U input residues. -/
noncomputable def residueProduct {k : ℕ} (p b : Fin k) : Template k :=
  .ex (.conj (fromFormula (side 0)) (folded 0 p.succ b.succ))

theorem residueProduct_spec {k U K : ℕ} (p b : Fin k) (v : Fin k → Fin U) (f : ℕ→ℕ)
    (hp : (v p).val.Prime) (hK : 2≤K) (hpk : (v p).val≤2^K) (hcap : 2^((K+1)*K)<U) :
    (residueProduct p b).eval (fun r a => decide (a.val=f r.val%(v p).val)) v = true ↔
      (v b).val=productPrefix f U%(v p).val := by
  rw [residueProduct,Tex_true]
  simp only [Tconj_true,fromFormula_eval,side_spec,Fin.cases_zero]
  have hU := (v p).isLt; have hpp := hp.two_le
  have run (m : Fin U) (hm : IsSide U m.val) :
      (folded 0 p.succ b.succ).eval (fun r a => decide (a.val=f r.val%(v p).val)) (Fin.cases m v) = true ↔
      (v b).val=productPrefix f U%(v p).val := by
    let e : Fin (k+1) → Fin U := Fin.cases m v
    exact folded_spec 0 p.succ b.succ e f hp (side_budget hp hK hpk hcap hm) hm.1 hK hpk hcap
  constructor
  · rintro ⟨m,hm,h⟩; exact (run m hm).mp h
  · intro h
    obtain ⟨m,hm,hside⟩ := exists_side (U:=U) (by omega)
    exact ⟨⟨m,hm⟩,hside,(run ⟨m,hm⟩ hside).mpr h⟩

/-- Query the product directly on the original matrix of U arbitrary U-bit words. -/
noncomputable def binaryProduct {k : ℕ} (p b : Fin k) : Template k :=
  HABMatrix.bind (HABBinaryResidue.rowResidue (1 : Fin 3) 2 0) (residueProduct p b)
    (fun _ => p) id

private theorem fin_prod (U : ℕ) (f : ℕ→ℕ) : (∏ r : Fin U, f r.val)=productPrefix f U := by
  induction U with
  | zero => simp [productPrefix]
  | succ U ih => rw [Fin.prod_univ_castSucc,product_succ,←ih]; rfl

/-- All U factors participate. No modulus oracle, product circuit or supplied
residue table appears in this fixed finite formula. -/
theorem binaryProduct_spec {k U K : ℕ} (p b : Fin k) (v : Fin k → Fin U) (A : HAB.Matrix U)
    (hp : (v p).val.Prime) (hK : 2≤K) (hpk : (v p).val≤2^K) (hcap : 2^((K+1)*K)<U) :
    (binaryProduct p b).eval A v = true ↔
      (v b).val=(∏ r : Fin U, HAB.rowWord (A r))%(v p).val := by
  let f := fun r : ℕ => if h : r<U then HAB.rowWord (A ⟨r,h⟩) else 0
  have hf (r : Fin U) : f r.val=HAB.rowWord (A r) := by simp [f,r.isLt]
  rw [binaryProduct,HABMatrix.bind_spec]
  let pars : Fin 1 → Fin k := fun _ => p
  have rel : (fun r c : Fin U => (HABBinaryResidue.rowResidue (1 : Fin 3) 2 0).eval A
      (extend c r (v ∘ pars))) = fun r c => decide (c.val=f r.val%(v p).val) := by
    funext r c
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq,hf]
    let e : Fin 3 → Fin U := extend c r (v ∘ pars)
    exact HABBinaryResidue.rowResidue_short 1 2 0 e A hp hK hpk hcap
  change (residueProduct p b).eval _ v = true ↔ _
  rw [rel,residueProduct_spec p b v f hp hK hpk hcap,←fin_prod]
  simp only [hf]

private theorem factorial_collision {U : ℕ} (hU : 4≤U) :
    ∃ x : ℕ, 1<x ∧ x<2^U ∧ ∀ p : ℕ, p.Prime → p*p≤U → x%p=1%p := by
  let m := Nat.sqrt U
  have hm : 2≤m := Nat.le_sqrt.mpr hU
  have hexp : m-1+1=m := by omega
  have hmb : m≤2^(m-1) := by have : m-1<2^(m-1) := Nat.lt_two_pow_self; omega
  have hbt : 1<2^(m-1) := Nat.one_lt_two_pow (by omega)
  have hgap : m+1<2^m := by rw [←hexp,pow_succ] at ⊢; omega
  have hpow (a b : ℕ) (hab : a<b) : a^m<b^m := Nat.pow_lt_pow_left hab (by omega)
  have hlt : m.factorial+1<2^U := calc
    _ ≤ m^m+1 := Nat.add_le_add_right (Nat.factorial_le_pow _) 1
    _ ≤ (m+1)^m := hpow m (m+1) (by omega)
    _ < (2^m)^m := hpow _ _ hgap
    _ = 2^(m*m) := (pow_mul ..).symm
    _ ≤ 2^U := Nat.pow_le_pow_right (by decide) (Nat.sqrt_le _)
  refine ⟨m.factorial+1,by have := Nat.factorial_pos m; omega,hlt,?_⟩
  intro p hp small
  have hd := Nat.dvd_factorial hp.pos (Nat.le_sqrt.mpr small)
  rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd hd,zero_add,Nat.mod_mod]

/-- The supported primes cannot identify an arbitrary positive U-bit value
from its residues alone. The two witnesses are 1 and (floor(sqrt U))!+1. -/
theorem short_prime_collision {U : ℕ} (hU : 4≤U) :
    ∃ x : ℕ, 1<x ∧ x<2^U ∧
      ∀ p K : ℕ, p.Prime → 2≤K → p≤2^K → 2^((K+1)*K)<U → x%p=1%p := by
  obtain ⟨x,hlo,hhi,h⟩ := factorial_collision hU
  refine ⟨x,hlo,hhi,fun p K hp hK hpk hcap => h p hp ?_⟩
  have := HABBinaryResidue.square_fits hK hpk hcap
  omega

/-- Even after any fixed polynomial enlargement of the ambient universe,
the packed modular powers cannot separate all positive U-bit integers. -/
theorem padded_short_prime_collision {U d : ℕ} (hU : 4≤U) (large : 2^(4*d)≤U) :
    ∃ x : ℕ, 1<x ∧ x<2^U ∧
      ∀ p K : ℕ, p.Prime → 2≤K → p≤2^K → 2^((K+1)*K)<U^d → x%p=1%p := by
  obtain ⟨x,hlo,hhi,h⟩ := factorial_collision hU
  refine ⟨x,hlo,hhi,fun p K hp hK hpk hcap => h p hp ?_⟩
  by_contra! hlarge
  have hupper : U≤2^(2*K) := calc
    _ ≤ p*p := hlarge.le
    _ ≤ 2^K*2^K := Nat.mul_self_le_mul_self hpk
    _ = 2^(2*K) := by rw [two_mul,pow_add]
  have expLt : (K+1)*K < (2*K)*d := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
    rw [pow_mul 2 (2*K) d]
    exact hcap.trans_le (Nat.pow_le_pow_left hupper d)
  have hk : K+1<2*d := Nat.lt_of_mul_lt_mul_right (by simpa [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using expLt)
  have impossible := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (large.trans hupper)
  omega

end DiophantineNP.HABProductBlocks
