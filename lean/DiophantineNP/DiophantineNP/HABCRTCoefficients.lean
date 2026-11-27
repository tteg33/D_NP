import DiophantineNP.HABBoundedProduct
import DiophantineNP.HABCRTRecovery

/-! # Basis products and coefficients as finite residue queries

A basis is supplied as a formula with the proposed member in its first slot.
A residue graph uses the proposed value and modulus in its first two slots.
The remaining parameters and the original input matrix are preserved. -/
namespace DiophantineNP.HABCRTCoefficients
open Counting WidthFormula PrimeFormula FiniteArithmeticGap
open HABBoundedProduct (Supported)

abbrev Members {n U : ℕ} (basis : Template (n+1)) (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ) :=
  ∀ r : Fin U, basis.eval A (Fin.cases r e)=true ↔ r.val∈s

abbrev Fits {U : ℕ} (s : Finset ℕ) := ∀ r ∈ s, r<U

private def ren {a k : ℕ} (p : Template a) (f : Fin a→Fin k) : Template k :=
  rewriteMatrix (fun i j => .entry i j) p f

private theorem ren_spec {a k U : ℕ} (p : Template a) (f : Fin a→Fin k)
    (A : HAB.Matrix U) (e : Fin k→Fin U) : (ren p f).eval A e=p.eval A (e ∘ f) :=
  rewriteMatrix_eval _ A A (by intros;rfl) _ _ _

private def mux {k : ℕ} (c x y : Template k) : Template k := .disj (.conj c x) (.conj (.neg c) y)
private theorem mux_spec {k U : ℕ} (c x y : Template k) (A : HAB.Matrix U) (e : Fin k→Fin U) :
    (mux c x y).eval A e = if c.eval A e then x.eval A e else y.eval A e := by
  cases h : c.eval A e <;> simp [mux,Template.eval,h]

private abbrev push {n U : ℕ} (z : Fin U) (e : Fin n→Fin U) : Fin (n+1)→Fin U := Fin.cases z e

def digit {n : ℕ} (basis : Template (n+1)) : Template (n+2) :=
  mux (ren basis Fin.succ) (.bit 1 0) (fromFormula (isNat 0 0))

theorem digit_spec {n U : ℕ} (basis : Template (n+1)) (A : HAB.Matrix U) (e : Fin n→Fin U)
    (s : Finset ℕ) (members : Members basis A e s) (r c : Fin U) :
    (digit basis).eval A (extend c r e) = (if r.val∈s then r.val else 1).testBit c.val := by
  rw [digit,mux_spec,ren_spec]
  have env : (extend c r e) ∘ Fin.succ = push r e := rfl
  rw [env]
  by_cases h : r.val∈s
  · rw [if_pos ((members r).mpr h),if_pos h];rfl
  · rw [if_neg (mt (members r).mp h),if_neg h]
    apply Bool.eq_iff_iff.mpr
    rw [fromFormula_eval,isNat_spec,Nat.testBit_one_eq_true_iff_self_eq_zero];rfl

/-- Graph of the residue of the product of the entire selected basis. -/
noncomputable def modulus {n : ℕ} (basis : Template (n+1)) : Template (n+2) :=
  HABMatrix.bind (digit basis) (HABProductBlocks.binaryProduct (1 : Fin 2) 0)
    (fun i => i.succ.succ) ![0,1]

theorem modulus_spec {n U : ℕ} (basis : Template (n+1)) (A : HAB.Matrix U) (e : Fin n→Fin U)
    (s : Finset ℕ) (fits : Fits (U:=U) s) (members : Members basis A e s)
    (p b : Fin U) (hp : p.val.Prime) (ok : Supported U p.val) :
    (modulus basis).eval A (extend b p e) = true ↔ b.val=HABCRTRecovery.modulus s%p.val := by
  obtain ⟨K,hK,hpk,hcap⟩ := ok
  rw [modulus,HABMatrix.bind_spec]
  let g (a : ℕ) := if a∈s then a else 1
  have hmat (r c : Fin U) := digit_spec basis A e s members r c
  have eq : (fun r c : Fin U => (digit basis).eval A (extend c r (extend b p e ∘ fun i => i.succ.succ))) =
      fun r c => (g r.val).testBit c.val := funext fun r => funext fun c => hmat r c
  rw [eq,HABProductBlocks.binaryProduct_spec _ _ _ _ hp hK hpk hcap]
  have Upos := hp.pos.trans p.isLt
  have word (r : Fin U) : HAB.rowWord (fun c : Fin U => (g r.val).testBit c.val)=g r.val := by
    apply HAB.rowWord_natural
    dsimp [g];split
    · exact r.isLt.trans Nat.lt_two_pow_self
    · exact Nat.one_lt_two_pow (by omega)
  simp_rw [word]
  have ih : Finset.range U ∩ s = s := Finset.inter_eq_right.mpr (fun i hi => Finset.mem_range.mpr (fits i hi))
  rw [Fin.prod_univ_eq_prod_range]
  change b.val = (∏ i ∈ Finset.range U, if i∈s then i else 1)%p.val ↔ _
  rw [Finset.prod_ite_mem,ih]
  rfl

/-- Include a candidate prime only when it differs from a distinguished prime.
Slots are the candidate, the distinguished prime, then ambient parameters. -/
def erase {n : ℕ} (basis : Template (n+1)) : Template (n+2) :=
  .conj (.neg (.atom (.eqv 0 1))) (ren basis (Fin.cases 0 (fun i => i.succ.succ)))

theorem erase_spec {n U : ℕ} (basis : Template (n+1)) (A : HAB.Matrix U) (e : Fin n→Fin U)
    (s : Finset ℕ) (members : Members basis A e s) (q : Fin U) :
    Members (erase basis) A (push q e) (s.erase q.val) := by
  intro r
  have hr : (push r (push q e)) ∘ Fin.cases 0 (fun i : Fin n => i.succ.succ) = push r e := by
    funext i;refine Fin.cases rfl (fun _=>rfl) i
  rw [erase,Tconj_true,ren_spec]
  change (!decide (r=q))=true ∧ basis.eval A _=true ↔ _
  rw [hr,members]
  simp [Fin.ext_iff,Finset.mem_erase]

/-- Residue of the product with this same target prime omitted. -/
noncomputable def cofactor {n : ℕ} (basis : Template (n+1)) : Template (n+2) :=
  ren (modulus (erase basis)) (Fin.cases 0 (Fin.cases 1 (Fin.cases 1 (fun i => i.succ.succ))))

theorem cofactor_spec {n U : ℕ} (basis : Template (n+1)) (A : HAB.Matrix U) (e : Fin n→Fin U)
    (s : Finset ℕ) (fits : Fits (U:=U) s) (members : Members basis A e s)
    (p b : Fin U) (hp : p.val.Prime) (ok : Supported U p.val) :
    (cofactor basis).eval A (extend b p e)=true ↔ b.val=HABCRTRecovery.cofactor s p.val%p.val := by
  rw [cofactor,ren_spec]
  have eq : extend b p e ∘ Fin.cases 0 (Fin.cases 1 (Fin.cases 1 (fun i : Fin n => i.succ.succ))) =
      extend b p (push p e) := by
    funext i; refine Fin.cases rfl (fun j => ?_) i; refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => rfl) j
  rw [eq]
  exact modulus_spec _ _ _ _ (fun r hr => fits r (Finset.mem_of_mem_erase hr)) (erase_spec _ _ _ _ members p) p b hp ok

/-- Supply the candidate residue, target prime and ambient parameters at
arbitrary free argument positions. -/
def graphAt {n k : ℕ} (query : Template (n+2)) (b p : Fin k) (parameters : Fin n→Fin k) : Template k :=
  ren query (Fin.cases b (Fin.cases p parameters))

theorem graphAt_spec {n k U : ℕ} (query : Template (n+2)) (b p : Fin k) (parameters : Fin n→Fin k)
    (A : HAB.Matrix U) (v : Fin k→Fin U) :
    (graphAt query b p parameters).eval A v = query.eval A (extend (v b) (v p) (v ∘ parameters)) := by
  rw [graphAt,ren_spec]
  apply congrArg (query.eval A)
  funext i; refine Fin.cases rfl (fun j => ?_) i; refine Fin.cases rfl (fun _ => rfl) j

def diff2 {k : ℕ} (p x : Fin k) : Template k :=
  .ex (.conj (fromFormula (isNat 2 0)) (fromFormula (addF x.succ 0 p.succ)))

theorem diff2_spec {k U : ℕ} (p x : Fin k) (A : HAB.Matrix U) (v : Fin k→Fin U) (hU : 2<U) :
    (diff2 p x).eval A v=true ↔ (v x).val+2=(v p).val := by
  simp only [diff2,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,addF_spec,Fin.cases_zero,Fin.cases_succ]
  exact ⟨fun ⟨_,hw,ha⟩ => hw ▸ ha,fun h => ⟨⟨2,hU⟩,rfl,h⟩⟩

private def invAt {k : ℕ} (x p b : Fin k) : Template k :=
  .ex (.conj (diff2 p.succ 0) (fromFormula (ShortPower.formula x.succ 0 p.succ b.succ)))

private theorem invAt_spec {k U : ℕ} (x p b : Fin k) (A : HAB.Matrix U) (v : Fin k→Fin U)
    (hp : (v p).val.Prime) (ok : Supported U (v p).val) (hx : (v x).val<(v p).val) :
    (invAt x p b).eval A v=true ↔ (v b).val=(v x).val^((v p).val-2)%(v p).val := by
  obtain ⟨K,hK,hpk,hcap⟩ := ok
  have hp2 := hp.two_le
  have hU := hp2.trans_lt (v p).isLt
  let t : Fin U := ⟨(v p).val-2,by omega⟩
  have hw := ShortPower.formula_correct x.succ (0 : Fin (k+1)) p.succ b.succ (push t v) hK hx hp.one_lt
    (show t.val<2^K by dsimp [t];omega) hpk hcap
  simp only [invAt,Tex_true,Tconj_true,fromFormula_eval,diff2_spec _ _ _ _ hU,Fin.cases_zero,Fin.cases_succ]
  constructor
  · rintro ⟨z,hz,chk⟩
    have e : z=t := Fin.ext (by dsimp [t];omega)
    subst z;exact hw.mp chk
  · intro h;exact ⟨t,by dsimp [t];omega,hw.mpr h⟩

/-- The distinguished coefficient multiplier, computed by Fermat inversion
from the cofactor residue. -/
noncomputable def inverse {n : ℕ} (basis : Template (n+1)) : Template (n+2) :=
  .ex (.conj (graphAt (cofactor basis) 0 2 (fun i => i.succ.succ.succ)) (invAt 0 2 1))

theorem inverse_spec {n U : ℕ} (basis : Template (n+1)) (A : HAB.Matrix U) (e : Fin n→Fin U)
    (s : Finset ℕ) (fits : Fits (U:=U) s) (members : Members basis A e s)
    (p b : Fin U) (hp : p.val.Prime) (ok : Supported U p.val) :
    (inverse basis).eval A (extend b p e)=true ↔ b.val=HABCRTRecovery.inverse s p.val := by
  let t : Fin U := ⟨HABCRTRecovery.cofactor s p.val%p.val,(Nat.mod_lt _ hp.pos).trans p.isLt⟩
  have graph (w : Fin U) : (graphAt (cofactor basis) 0 2 (fun i => i.succ.succ.succ)).eval A (push w (extend b p e))=true ↔
      w.val=t.val := by rw [graphAt_spec]; exact cofactor_spec basis A e s fits members p w hp ok
  have chk := invAt_spec (0 : Fin (n+3)) 2 1 A (push t (extend b p e)) hp ok (Nat.mod_lt _ hp.pos)
  simp only [inverse,Tex_true,Tconj_true]
  constructor
  · rintro ⟨w,hw,h⟩
    have eq : w=t := Fin.ext ((graph w).mp hw)
    subst w;exact chk.mp h
  · intro h;exact ⟨t,(graph t).mpr rfl,chk.mpr h⟩

/-- A short field multiplication with a representable ordinary product. -/
def mulModAt {k : ℕ} (a b p c : Fin k) : Template k :=
  (ShortResidue.Predicate.ex 4 ((ShortResidue.Predicate.mul 0 1 4).both
    (HABBinaryResidue.modulo 4 2 3))).syntaxF (fun i => if i=0 then a else if i=1 then b else if i=2 then p else c)

theorem mulModAt_spec {k U : ℕ} (a b p c : Fin k) (A : HAB.Matrix U) (v : Fin k→Fin U)
    (hp : 0<(v p).val) (hab : (v a).val*(v b).val<U) :
    (mulModAt a b p c).eval A v=true ↔ (v c).val=(v a).val*(v b).val%(v p).val := by
  let t (i j : ℕ) := if h : i<U ∧ j<U then A ⟨i,h.1⟩ ⟨j,h.2⟩ else false
  have eq : A=fun i j => t i.val j.val := by funext i j; simp [t,i.isLt,j.isLt]
  rw [eq,mulModAt,ShortResidue.Predicate.valid _ _ t]
  change (∃ z<U, (v a).val*(v b).val=z ∧ 0<(v p).val ∧ (v c).val=z%(v p).val) ↔ _
  exact ⟨fun ⟨_,_,rfl,_,h⟩ => h,fun h=>⟨_,hab,rfl,hp,h⟩⟩

/-- Graph of the CRT coefficient formed from the input's residue graph and
the inverse of its basis cofactor. -/
noncomputable def coefficient {n : ℕ} (basis : Template (n+1)) (input : Template (n+2)) : Template (n+2) :=
  .ex (.conj (graphAt input 0 2 (fun i => i.succ.succ.succ)) (.ex (.conj
    (graphAt (inverse basis) 0 3 (fun i => i.succ.succ.succ.succ)) (mulModAt 1 0 3 2))))

theorem coefficient_spec {n U : ℕ} (basis : Template (n+1)) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ) (fits : Fits (U:=U) s)
    (members : Members basis A e s) (p b : Fin U) (hp : p.val.Prime) (ok : Supported U p.val)
    (x : ℕ) (data : ∀ z : Fin U, input.eval A (extend z p e)=true ↔ z.val=x%p.val) :
    (coefficient basis input).eval A (extend b p e)=true ↔
      b.val=HABCRTRecovery.coeff (HABCRTRecovery.inverse s) x p.val := by
  let r : Fin U := ⟨x%p.val,(Nat.mod_lt _ hp.pos).trans p.isLt⟩
  have hI : HABCRTRecovery.inverse s p.val < p.val := Nat.mod_lt _ hp.pos
  let inv : Fin U := ⟨HABCRTRecovery.inverse s p.val,hI.trans p.isLt⟩
  have valG (w : Fin U) : (graphAt input 0 2 (fun i=>i.succ.succ.succ)).eval A (push w (extend b p e))=true ↔
      w.val=r.val := by rw [graphAt_spec]; exact data w
  have invG (w z : Fin U) : (graphAt (inverse basis) 0 3 (fun i=>i.succ.succ.succ.succ)).eval A (push z (push w (extend b p e)))=true ↔
      z.val=inv.val := by rw [graphAt_spec]; exact inverse_spec basis A e s fits members p z hp ok
  have pfit : p.val*p.val<U := by
    obtain ⟨K,hK,hpk,hcap⟩ := ok
    exact (HABBinaryResidue.square_fits hK hpk hcap).trans_le (Nat.sub_le ..)
  have chk := mulModAt_spec (1 : Fin (n+4)) 0 3 2 A (push inv (push r (extend b p e))) hp.pos
    ((Nat.mul_le_mul (Nat.mod_lt x hp.pos).le hI.le).trans_lt pfit)
  simp only [coefficient,Tex_true,Tconj_true]
  constructor
  · rintro ⟨w,hw,z,hz,h⟩
    have e1 : w=r := Fin.ext ((valG w).mp hw)
    have e2 : z=inv := Fin.ext ((invG w z).mp hz)
    subst w;subst z;exact chk.mp h
  · intro h;exact ⟨r,(valG r).mpr rfl,inv,(invG r inv).mpr rfl,chk.mpr h⟩

end DiophantineNP.HABCRTCoefficients
