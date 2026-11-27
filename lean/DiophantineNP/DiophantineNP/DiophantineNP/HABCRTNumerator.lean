import DiophantineNP.HABCRTCoefficients
import DiophantineNP.HABPrimeBlocks

/-! # Fixed residue graph of the numerator for the HAB shift

For each active block with odd product A, compute its residue by the verified
basis-product formula. The unique y<p solving 2y=A+1 modulo an odd prime p
is the residue of (A+1)/2. The product over these half factors and the supplied
input residue gives the numerator used in Theorem 4.1. -/

namespace DiophantineNP.HABCRTNumerator
open Counting WidthFormula PrimeFormula FiniteArithmeticGap ShortResidue
open HABCRTCoefficients (graphAt graphAt_spec Fits Members)
open HABBoundedProduct (Supported)

private def halfP : Predicate :=
  (Predicate.lt 0 2).both <| Predicate.ex 3 <| (Predicate.add 0 0 3).both <|
    Predicate.ex 4 <| (Predicate.eqN 4 1).both <| Predicate.ex 5 <|
    (Predicate.add 1 4 5).both <| Predicate.ex 6 <| (HABBinaryResidue.modulo 3 2 6).both
      (HABBinaryResidue.modulo 5 2 6)

def halfAt {k : ℕ} (y r p : Fin k) : Template k :=
  halfP.syntaxF (fun i => if i=0 then y else if i=1 then r else p)

theorem halfAt_spec {U k B : ℕ} (y r p : Fin k) (A : HAB.Matrix U) (v : Fin k→Fin U)
    (hp : (v p).val.Prime) (ho : Odd (v p).val) (hb : Odd B) (hr : (v r).val=B%(v p).val)
    (cap : (v p).val*(v p).val<U) :
    (halfAt y r p).eval A v=true ↔ (v y).val=((B+1)/2)%(v p).val := by
  let t (i j : ℕ) := if h : i<U ∧ j<U then A ⟨i,h.1⟩ ⟨j,h.2⟩ else false
  have eq : A=fun i j => t i.val j.val := by funext i j; simp [t,i.isLt,j.isLt]
  rw [eq,halfAt,halfP.valid _ t]
  change ((v y).val<(v p).val ∧ ∃ z<U, (v y).val+(v y).val=z ∧ ∃ w<U,w=1 ∧
    ∃ f<U,(v r).val+w=f ∧ ∃ e<U,(0<(v p).val ∧ e=z%(v p).val) ∧
    (0<(v p).val ∧ e=f%(v p).val)) ↔ _
  let d := (v p).val
  let h := (B+1)/2
  have two : 2*h=B+1 := by have := Nat.odd_iff.mp hb;dsimp [h];omega
  have hr' : (v r).val+1 ≡ B+1 [MOD d] := (hr ▸ Nat.mod_modEq B d).add_right 1
  have test {b : ℕ} (hb' : b<d) : b+b ≡ (v r).val+1 [MOD d] ↔ b=h%d := by
    constructor
    · intro chk
      have hh : 2*b ≡ 2*h [MOD d] := by rw [two_mul  b,two];exact chk.trans hr'
      exact (Nat.mod_eq_of_lt hb').symm.trans (Nat.ModEq.cancel_left_of_coprime (Nat.coprime_two_right.mpr ho) hh)
    · intro he
      rw [←two_mul,he]
      rw [←two] at hr'
      exact ((Nat.mod_modEq h d).mul_left 2).trans hr'.symm
  have pd := hp.two_le
  have pp := (v p).isLt
  have hp0 := hp.pos
  have mult := Nat.mul_le_mul_right d pd
  constructor
  · rintro ⟨hy,_,_,rfl,_,_,rfl,_,_,rfl,_,_,⟨_,hz⟩,⟨_,hf⟩⟩
    exact (test hy).mp (hz.symm.trans hf)
  · intro he
    have hy : (v y).val<d := he ▸ Nat.mod_lt _ hp0
    have rz := hr ▸ Nat.mod_lt B hp0
    have chk := (test hy).mpr he
    exact ⟨hy,_,by dsimp [d] at *;omega,rfl,1,by omega,rfl,
      _,by omega,rfl,_,(Nat.mod_lt _ hp0).trans pp,⟨hp0,rfl⟩,hp0,chk⟩

private abbrev push {n U : ℕ} (z : Fin U) (e : Fin n→Fin U) : Fin (n+1)→Fin U := Fin.cases z e

private def mux {k : ℕ} (c x y : Template k) : Template k := .disj (.conj c x) (.conj (.neg c) y)
private theorem mux_spec {k U : ℕ} (c x y : Template k) (A : HAB.Matrix U) (e : Fin k→Fin U) :
    (mux c x y).eval A e = if c.eval A e then x.eval A e else y.eval A e := by
  cases h : c.eval A e <;> simp [mux,Template.eval,h]

/-- The graph in the slots y, i, p, parameters. -/
private noncomputable def halfCell {n : ℕ} (length : Fin n) (blocks : Template (n+2)) : Template (n+3) :=
  mux (fromFormula (ltF 1 length.succ.succ.succ))
    (.ex (.conj (graphAt (HABCRTCoefficients.modulus blocks) 0 3
        (Fin.cases 2 (fun i => i.succ.succ.succ.succ))) (halfAt 1 0 3)))
    (fromFormula (isNat 1 0))

def factor (family : ℕ→Finset ℕ) (s i : ℕ) :=
  if i<s then (HABCRTRecovery.modulus (family i)+1)/2 else 1

private theorem halfCell_spec {n U : ℕ} (length : Fin n) (blocks : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (family : ℕ→Finset ℕ) (p i y : Fin U)
    (hp : p.val.Prime) (ho : Odd p.val) (ok : Supported U p.val)
    (fits : ∀ i : Fin U, i.val<(e length).val → Fits (U:=U) (family i.val))
    (members : ∀ i : Fin U, i.val<(e length).val → Members blocks A (push i e) (family i.val))
    (odd : ∀ i : Fin U, i.val<(e length).val → Odd (HABCRTRecovery.modulus (family i.val))) :
    (halfCell length blocks).eval A (extend y i (push p e))=true ↔
      y.val=factor family (e length).val i.val%p.val := by
  let env := extend y i (push p e)
  have c : (fromFormula (ltF (1:Fin (n+3)) length.succ.succ.succ)).eval A env =
      decide (i.val<(e length).val) := by
    apply Bool.eq_iff_iff.mpr;rw [fromFormula_eval,ltF_true,decide_eq_true_eq];rfl
  change (halfCell length blocks).eval A env=true ↔ _
  rw [halfCell,mux_spec,c,factor]
  by_cases hi : i.val<(e length).val
  · simp only [hi,decide_true,if_true,Tex_true,Tconj_true]
    let z : Fin U := ⟨HABCRTRecovery.modulus (family i.val)%p.val,(Nat.mod_lt _ hp.pos).trans p.isLt⟩
    have chk (w : Fin U) : (graphAt (HABCRTCoefficients.modulus blocks) 0 3
          (Fin.cases 2 (fun q => q.succ.succ.succ.succ))).eval A (push w env)=true ↔ w.val=z.val := by
      rw [graphAt_spec]
      have par : (push w env) ∘ (Fin.cases 2 (fun q : Fin n => q.succ.succ.succ.succ)) = push i e := by
        funext j;refine Fin.cases rfl (fun _=>rfl) j
      rw [par]
      exact HABCRTCoefficients.modulus_spec blocks A (push i e) (family i.val) (fits i hi) (members i hi) p w hp ok
    have hcap : p.val*p.val<U := by
      obtain ⟨K,hK,hpK,cap⟩ := ok
      exact (HABBinaryResidue.square_fits hK hpK cap).trans_le (Nat.sub_le ..)
    have h := halfAt_spec (1:Fin (n+4)) 0 3 A (push z env) hp ho (odd i hi) rfl hcap
    exact ⟨fun ⟨w,hw,hv⟩ => h.mp ((show w=z from Fin.ext ((chk w).mp hw)) ▸ hv),
      fun hv=>⟨z,(chk z).mpr rfl,h.mpr hv⟩⟩
  · simp only [hi,decide_false,Bool.false_eq_true,if_false,fromFormula_eval,isNat_spec,Nat.mod_eq_of_lt hp.one_lt]
    rfl

private noncomputable def halfProduct {n : ℕ} (length : Fin n) (blocks : Template (n+2)) : Template (n+2) :=
  HABMatrix.bind (halfCell length blocks) (HABProductBlocks.residueProduct (1 : Fin 2) 0) Fin.succ ![0,1]

theorem prefix_eq (f : ℕ→ℕ) (k : ℕ) : productPrefix f k=∏ i ∈ Finset.range k,f i := by
  induction k with
  | zero => simp [productPrefix]
  | succ k ih => rw [product_succ,Finset.prod_range_succ,ih]

theorem halfProduct_value (family : ℕ→Finset ℕ) (s : ℕ) :
    (∏ i ∈ Finset.range s,(HABCRTRecovery.modulus (family i)+1)/2) =
    HABCRTShift.halves ((List.range s).map fun i => HABCRTRecovery.modulus (family i)) := by
  rw [←prefix_eq]
  simp only [productPrefix,HABCRTShift.halves,List.map_map,Function.comp_def]

private theorem halfProduct_spec {n U : ℕ} (length : Fin n) (blocks : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (family : ℕ→Finset ℕ) (p b : Fin U)
    (hp : p.val.Prime) (ho : Odd p.val) (ok : Supported U p.val)
    (fits : ∀ i : Fin U, i.val<(e length).val → Fits (U:=U) (family i.val))
    (members : ∀ i : Fin U, i.val<(e length).val → Members blocks A (push i e) (family i.val))
    (odd : ∀ i : Fin U, i.val<(e length).val → Odd (HABCRTRecovery.modulus (family i.val))) :
    (halfProduct length blocks).eval A (extend b p e)=true ↔
      b.val=(∏ i ∈ Finset.range (e length).val,(HABCRTRecovery.modulus (family i)+1)/2)%p.val := by
  rw [halfProduct,HABMatrix.bind_spec]
  let f := factor family (e length).val
  have M : (fun r c : Fin U => (halfCell length blocks).eval A (extend c r (extend b p e ∘ Fin.succ))) =
      fun r c => decide (c.val=f r.val%p.val) := by
    funext r c
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq];exact halfCell_spec length blocks A e family p r c hp ho ok fits members odd
  obtain ⟨K,hK,hpK,hcap⟩ := ok
  have he : extend b p e ∘ (![0,1] : Fin 2→Fin (n+2)) = ![b,p] := by funext q;fin_cases q <;> rfl
  rw [M,he]
  have run := HABProductBlocks.residueProduct_spec (1:Fin 2) 0 ![b,p] f hp hK hpK hcap
  change ((HABProductBlocks.residueProduct (1:Fin 2) 0).eval (fun r c=>decide (c.val=f r.val%p.val)) ![b,p]=true) ↔ b.val=productPrefix f U%p.val at run
  rw [run]
  change b.val=productPrefix (fun i=>if i<(e length).val then _ else 1) U%p.val ↔ _
  rw [product_pad _ (e length).isLt.le,prefix_eq]

/-- The numerator residue graph. Block i in the supplied family is A_(i+1)
in HAB notation, so a shift of length s uses exactly the first s rows. -/
noncomputable def numerator {n : ℕ} (length : Fin n) (blocks input : Template (n+2)) : Template (n+2) :=
  .ex (.conj (graphAt input 0 2 (fun i => i.succ.succ.succ)) (.ex (.conj
    (graphAt (halfProduct length blocks) 0 3 (fun i => i.succ.succ.succ.succ))
    (HABCRTCoefficients.mulModAt 1 0 3 2))))

theorem numerator_spec {n U : ℕ} (length : Fin n) (blocks input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (family : ℕ→Finset ℕ) (x : ℕ) (p b : Fin U)
    (hp : p.val.Prime) (ho : Odd p.val) (ok : Supported U p.val)
    (fits : ∀ i : Fin U, i.val<(e length).val → Fits (U:=U) (family i.val))
    (members : ∀ i : Fin U, i.val<(e length).val → Members blocks A (Fin.cases i e) (family i.val))
    (odd : ∀ i : Fin U, i.val<(e length).val → Odd (HABCRTRecovery.modulus (family i.val)))
    (data : ∀r : Fin U, input.eval A (extend r p e)=true ↔ r.val=x%p.val) :
    (numerator length blocks input).eval A (extend b p e)=true ↔
      b.val=(x*(∏ i ∈ Finset.range (e length).val,(HABCRTRecovery.modulus (family i)+1)/2))%p.val := by
  let y := ∏ i ∈ Finset.range (e length).val,(HABCRTRecovery.modulus (family i)+1)/2
  let xr : Fin U := ⟨x%p.val,(Nat.mod_lt _ hp.pos).trans p.isLt⟩
  let yr : Fin U := ⟨y%p.val,(Nat.mod_lt _ hp.pos).trans p.isLt⟩
  have valG (w : Fin U) : (graphAt input 0 2 (fun i=>i.succ.succ.succ)).eval A (push w (extend b p e))=true ↔
      w.val=xr.val := by rw [graphAt_spec];exact data w
  have prodG (w z : Fin U) : (graphAt (halfProduct length blocks) 0 3 (fun i=>i.succ.succ.succ.succ)).eval A
      (push z (push w (extend b p e)))=true ↔ z.val=yr.val := by
    rw [graphAt_spec];exact halfProduct_spec length blocks A e family p z hp ho ok fits members odd
  have pfit : p.val*p.val<U := by
    obtain ⟨K,hK,hpk,hcap⟩ := ok
    exact (HABBinaryResidue.square_fits hK hpk hcap).trans_le (Nat.sub_le ..)
  have chk := HABCRTCoefficients.mulModAt_spec (1 : Fin (n+4)) 0 3 2 A
    (push yr (push xr (extend b p e))) hp.pos
    ((Nat.mul_le_mul (Nat.mod_lt x hp.pos).le (Nat.mod_lt y hp.pos).le).trans_lt pfit)
  change _ ↔ b.val=(x*y)%p.val
  rw [Nat.mul_mod x y p.val]
  simp only [numerator,Tex_true,Tconj_true]
  constructor
  · rintro ⟨w,hw,z,hz,h⟩
    have e1 : w=xr := Fin.ext ((valG w).mp hw)
    have e2 : z=yr := Fin.ext ((prodG w z).mp hz)
    subst w;subst z;exact chk.mp h
  · intro h;exact ⟨xr,(valG xr).mpr rfl,yr,(prodG xr yr).mpr rfl,chk.mpr h⟩

/-- Identification of the generic short-block product with the concrete
auxiliary blocks used in the final binary shift. -/
theorem prime_halfProduct (k s : ℕ) :
    (∏ i ∈ Finset.range s,(HABCRTRecovery.modulus (HABPrimeBlocks.primeSet k (i+1))+1)/2) =
      HABCRTShift.halves (HABCRTShift.blocks k s) := by
  rw [halfProduct_value]
  simp only [HABCRTRecovery.modulus,HABPrimeBlocks.primeSet_product,HABCRTShift.blocks]

end DiophantineNP.HABCRTNumerator
