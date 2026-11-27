import DiophantineNP.HABGroupPower
import DiophantineNP.HABBinaryResidue
import DiophantineNP.HABMatrixBind

/-! # Finite formulas for the local group-power certificate rows -/
namespace DiophantineNP.HABPowerRows
open Counting WidthFormula PrimeFormula FiniteArithmeticGap ShortResidue

abbrev OracleAt {U : ℕ} (power : Template 4) (A : HAB.Matrix U) (p : Fin U) (bound : ℕ) :=
  ∀ a j b : Fin U, a.val<p.val → j.val≤bound →
    (power.eval A ![a,j,p,b]=true ↔ b.val=a.val^j.val%p.val)

private abbrev push {k U : ℕ} (w : Fin U) (v : Fin k→Fin U) : Fin (k+1)→Fin U := Fin.cases w v

private def call {k : ℕ} (power : Template 4) (a j p b : Fin k) : Template k :=
  rewriteMatrix (fun r c => .entry r c) power ![a,j,p,b]

private theorem call_spec {k U B : ℕ} (power : Template 4) (a j p b : Fin k) (A : HAB.Matrix U)
    (v : Fin k→Fin U) (o : OracleAt power A (v p) B) (ha : (v a).val<(v p).val) (hj : (v j).val≤B) :
    (call power a j p b).eval A v=true ↔ (v b).val=(v a).val^(v j).val%(v p).val := by
  rw [call,rewriteMatrix_eval _ A A (by intros; rfl)]
  have he : v ∘ ![a,j,p,b]=![v a,v j,v p,v b] := by funext i; fin_cases i <;> rfl
  rw [he]; exact o _ _ _ ha hj

private def modG {k : ℕ} (x d r : Fin k) : Template k :=
  (HABBinaryResidue.modulo 0 1 2).syntaxF (fun i => if i=0 then x else if i=1 then d else r)

private theorem modG_spec {k U : ℕ} (x d r : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U) :
    (modG x d r).eval A e=true ↔ 0<(e d).val ∧ (e r).val=(e x).val%(e d).val := by
  let t (i j : ℕ) := if h : i<U ∧ j<U then A ⟨i,h.1⟩ ⟨j,h.2⟩ else false
  have eq : A=fun i j => t i.val j.val := by funext i j; simp [t,i.isLt,j.isLt]
  rw [eq,modG,Predicate.valid _ _ t]; rfl

private def remPow {k : ℕ} (power : Template 4) (a h d p b : Fin k) : Template k :=
  .ex (.conj (modG h.succ d.succ 0) (call power a.succ 0 p.succ b.succ))

private theorem remPow_spec {U k B : ℕ} (power : Template 4) (a h d p b : Fin k) (A : HAB.Matrix U)
    (v : Fin k→Fin U) (o : OracleAt power A (v p) B) (ha : (v a).val<(v p).val)
    (hd : 0<(v d).val) (hB : (v d).val≤B) :
    (remPow power a h d p b).eval A v=true ↔ (v b).val=(v a).val^((v h).val%(v d).val)%(v p).val := by
  simp only [remPow,Tex_true,Tconj_true,modG_spec,Fin.cases_succ,Fin.cases_zero,hd,true_and]
  let z : Fin U := ⟨(v h).val%(v d).val,(Nat.mod_lt _ hd).trans (v d).isLt⟩
  have chk (w : Fin U) (hw : w.val=z.val) : (call power a.succ 0 p.succ b.succ).eval A (Fin.cases w v)=true ↔
      (v b).val=(v a).val^z.val%(v p).val := by
    have he : w=z := Fin.ext hw
    subst w
    exact call_spec power a.succ 0 p.succ b.succ A (push z v) o ha ((Nat.mod_lt _ hd).le.trans hB)
  exact ⟨fun ⟨w,hw,hq⟩ => (chk w hw).mp hq,fun hq => ⟨z,rfl,(chk z rfl).mpr hq⟩⟩

private def predecessor {k : ℕ} (s p : Fin k) : Template k :=
  .ex (.conj (fromFormula (isNat 1 0)) (fromFormula (addF s.succ 0 p.succ)))

private theorem predecessor_spec {k U : ℕ} (s p : Fin k) (A : HAB.Matrix U) (v : Fin k→Fin U) (hU : 1<U) :
    (predecessor s p).eval A v=true ↔ (v s).val+1=(v p).val := by
  simp only [predecessor,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,addF_spec,Fin.cases_zero,Fin.cases_succ]
  exact ⟨fun ⟨w,hw,ha⟩ => hw ▸ ha,fun h => ⟨⟨1,hU⟩,rfl,h⟩⟩

private def pairOne {k : ℕ} (x y p : Fin k) : Template k :=
  .ex (.conj (fromFormula (mulF x.succ y.succ 0))
    (.ex (.conj (fromFormula (isNat 1 0)) (modG 1 p.succ.succ 0))))

private theorem pairOne_spec {U k : ℕ} (x y p : Fin k) (A : HAB.Matrix U) (v : Fin k→Fin U)
    (hp : 1<(v p).val) (hs : (v x).val*(v y).val<U) :
    (pairOne x y p).eval A v=true ↔ (v x).val*(v y).val%(v p).val=1 := by
  have hp0 := hp.trans (v p).isLt
  simp only [pairOne,Tex_true,Tconj_true,fromFormula_eval,mulF_spec,isNat_spec,modG_spec,
    Fin.cases_succ,Fin.cases_zero]
  constructor
  · rintro ⟨z,hz,w,hw,_,hr⟩; change w.val=z.val%(v p).val at hr; rw [hz,←hr,hw]
  · intro h; exact ⟨⟨_,hs⟩,rfl,⟨1,hp0⟩,rfl,by omega,h.symm⟩

private def rootPair {k : ℕ} (power : Template 4) (x a d p n : Fin k) : Template k :=
  .ex <| .conj (call power x.succ d.succ p.succ 0) <| .ex <|
    .conj (remPow power a.succ.succ n.succ.succ d.succ.succ p.succ.succ 0)
      (pairOne 1 0 p.succ.succ)

private theorem rootPair_spec {U k B : ℕ} (power : Template 4) (x a d p n : Fin k)
    (A : HAB.Matrix U) (v : Fin k→Fin U) (o : OracleAt power A (v p) B)
    (hp : 1<(v p).val) (ha : (v a).val<(v p).val) (hx : (v x).val<(v p).val)
    (hd : 0<(v d).val) (hB : (v d).val≤B) (hs : (v p).val*(v p).val<U) :
    (rootPair power x a d p n).eval A v=true ↔
      ((v x).val^(v d).val%(v p).val)*((v a).val^((v n).val%(v d).val)%(v p).val)%(v p).val=1 := by
  let u : Fin U := ⟨(v x).val^(v d).val%(v p).val,(Nat.mod_lt _ (by omega)).trans (v p).isLt⟩
  let w : Fin U := ⟨(v a).val^((v n).val%(v d).val)%(v p).val,(Nat.mod_lt _ (by omega)).trans (v p).isLt⟩
  have left (z : Fin U) := call_spec power x.succ d.succ p.succ 0 A (push z v) o hx hB
  have right (z t : Fin U) := remPow_spec power a.succ.succ n.succ.succ d.succ.succ p.succ.succ 0 A
    (push t (push z v)) o ha hd hB
  have last := pairOne_spec (1 : Fin (k+2)) 0 p.succ.succ A (push w (push u v)) hp
    ((Nat.mul_le_mul (Nat.mod_lt _ (by omega : 0<(v p).val)).le (Nat.mod_lt _ (by omega : 0<(v p).val)).le).trans_lt hs)
  simp only [rootPair,Tex_true,Tconj_true]
  constructor
  · rintro ⟨z,hz,t,ht,endv⟩
    have he : z=u := Fin.ext ((left z).mp hz)
    have hf : t=w := Fin.ext ((right z t).mp ht)
    subst z; subst t; exact last.mp endv
  · intro h; exact ⟨u,(left u).mpr rfl,w,(right u w).mpr rfl,last.mpr h⟩

private def rootCase {k : ℕ} (power : Template 4) (a d p h y : Fin k) : Template k :=
  .ex (.conj (predecessor 0 p.succ) <| .ex <| .conj (fromFormula (atLeast 1 0)) <|
    .conj (fromFormula (ltF 0 p.succ.succ)) <|
    .conj (rootPair power 0 a.succ.succ d.succ.succ p.succ.succ 1)
      (remPow power 0 h.succ.succ d.succ.succ p.succ.succ y.succ.succ))

private theorem rootCase_spec {U k B : ℕ} (power : Template 4) (a d p h y : Fin k)
    (A : HAB.Matrix U) (v : Fin k→Fin U) (o : OracleAt power A (v p) B)
    (hp : 1<(v p).val) (ha : (v a).val<(v p).val) (hd : 0<(v d).val)
    (hB : (v d).val≤B) (hs : (v p).val*(v p).val<U) :
    (rootCase power a d p h y).eval A v=true ↔ ∃ x : ℕ, 0<x ∧ x<(v p).val ∧
      (x^(v d).val%(v p).val)*((v a).val^(((v p).val-1)%(v d).val)%(v p).val)%(v p).val=1 ∧
      (v y).val=x^((v h).val%(v d).val)%(v p).val := by
  have hU := hp.trans (v p).isLt
  let n : Fin U := ⟨(v p).val-1,by have := (v p).isLt; omega⟩
  have left (x : Fin U) (hx : x.val<(v p).val) := rootPair_spec power 0 a.succ.succ d.succ.succ p.succ.succ 1
    A (push x (push n v)) o hp ha hx hd hB hs
  have right (x : Fin U) (hx : x.val<(v p).val) := remPow_spec power 0 h.succ.succ d.succ.succ
    p.succ.succ y.succ.succ A (push x (push n v)) o hx hd hB
  simp only [rootCase,Tex_true,Tconj_true,predecessor_spec _ _ _ _ hU,fromFormula_eval,ltF_true,atLeast_true,
    Fin.cases_zero,Fin.cases_succ]
  constructor
  · rintro ⟨z,hz,x,hx0,hx,check,weight⟩
    have he : z=n := Fin.ext (by dsimp [n]; omega)
    subst z; exact ⟨x.val,hx0,hx,(left x hx).mp check,(right x hx).mp weight⟩
  · rintro ⟨x,hx0,hx,check,weight⟩
    let z : Fin U := ⟨x,hx.trans (v p).isLt⟩
    exact ⟨n,by dsimp [n];omega,z,hx0,hx,(left z hx).mpr check,(right z hx).mpr weight⟩

private def mux {k : ℕ} (c x y : Template k) : Template k :=
  .disj (.conj c x) (.conj (.neg c) y)

private theorem mux_spec {k U : ℕ} (c x y : Template k) (A : HAB.Matrix U) (e : Fin k→Fin U) :
    (mux c x y).eval A e = if c.eval A e then x.eval A e else y.eval A e := by
  cases h : c.eval A e <;> simp [mux,Template.eval,h]

def LocalTest (p a D h c K d y : ℕ) : Prop :=
  if d=K then y=a^c%p
  else if d<K ∧ d∈D.primeFactors then
    ∃ x, 0<x ∧ x<p ∧ ((x^d%p)*(a^((p-1)%d)%p))%p=1 ∧ y=x^(h%d)%p
  else y=1

/-- Slots are p, a, D, h, c, K, d, y. -/
def row (power : Template 4) : Template 8 :=
  mux (.atom (.eqv 6 5)) (call power 1 4 0 7)
    (mux (.conj (fromFormula (ltF 6 5)) (fromFormula (HABGroupPower.basisMember 6 2)))
      (rootCase power 1 6 0 3 7) (fromFormula (isNat 1 7)))

theorem row_spec {U : ℕ} (power : Template 4) (A : HAB.Matrix U)
    (p a D h c K d y : Fin U) (o : OracleAt power A p (K.val*K.val))
    (hp : p.val.Prime) (ha : a.val<p.val) (hD : 0<D.val) (hK : 0<K.val)
    (hc : c.val≤K.val*K.val) (hs : p.val*p.val<U) :
    (row power).eval A ![p,a,D,h,c,K,d,y]=true ↔ LocalTest p a D h c K d y := by
  let v : Fin 8→Fin U := ![p,a,D,h,c,K,d,y]
  have hfirst : (Template.atom (.eqv (6 : Fin 8) 5)).eval A v = decide (d.val=K.val) := by
    change decide (d=K)=decide (d.val=K.val)
    simp [Fin.ext_iff]
  have hrest : (Template.conj (fromFormula (ltF 6 5)) (fromFormula (HABGroupPower.basisMember 6 2))).eval A v =
      decide (d.val<K.val ∧ d.val∈D.val.primeFactors) := by
    apply Bool.eq_iff_iff.mpr
    rw [Tconj_true,fromFormula_eval,ltF_true,fromFormula_eval,HABGroupPower.basisMember_spec _ _ _ hD,
      decide_eq_true_eq]; rfl
  change (row power).eval A v=true ↔ _
  rw [row,mux_spec,hfirst,LocalTest]
  by_cases he : d.val=K.val
  · simp only [he,decide_true,if_true]; exact call_spec power 1 4 0 7 A v o ha hc
  · simp only [he,decide_false,Bool.false_eq_true,if_false,mux_spec,hrest]
    by_cases hr : d.val<K.val ∧ d.val∈D.val.primeFactors
    · simp only [hr]
      have hbound := Nat.le_mul_of_pos_right K.val hK
      exact rootCase_spec power 1 6 0 3 7 A v o hp.one_lt ha (Nat.prime_of_mem_primeFactors hr.2).pos
        (hr.1.le.trans hbound) hs
    · simp only [hr,decide_false,Bool.false_eq_true,if_false,fromFormula_eval,isNat_spec]; rfl

end DiophantineNP.HABPowerRows
