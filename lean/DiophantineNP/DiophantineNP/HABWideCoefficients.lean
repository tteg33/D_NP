import DiophantineNP.HABCRTNumerator
import DiophantineNP.HABLargePrimeProduct

/-! # CRT coefficients and rescaling at polynomially bounded primes

The full group-power reduction supplies modular powers and products for
all represented primes. Local arithmetic uses space for p²; p³<U is one
common bound for the complete CRT readout. -/
namespace DiophantineNP.HABWideCoefficients
open Counting WidthFormula PrimeFormula FiniteArithmeticGap
open HABCRTCoefficients (graphAt graphAt_spec Members Fits digit digit_spec erase erase_spec diff2 diff2_spec mulModAt mulModAt_spec)
open HABPowerReduction (ShortProducts)
private abbrev push {n U : ℕ} (z : Fin U) (e : Fin n→Fin U) : Fin (n+1)→Fin U := Fin.cases z e

private theorem square_lt {p U : ℕ} (hp : p.Prime) (wide : p^3<U) : p*p<U := by
  rw [←pow_two]
  exact (Nat.pow_le_pow_right hp.pos (by decide : 2≤3)).trans_lt wide

private def ren {a k : ℕ} (p : Template a) (f : Fin a→Fin k) : Template k :=
  rewriteMatrix (fun i j => .entry i j) p f
private theorem ren_spec {a k U : ℕ} (p : Template a) (f : Fin a→Fin k)
    (A : HAB.Matrix U) (e : Fin k→Fin U) : (ren p f).eval A e=p.eval A (e ∘ f) :=
  rewriteMatrix_eval _ A A (by intros;rfl) _ _ _

private noncomputable def raw (ops : ShortProducts) {k : ℕ} (p b : Fin k) : Template k :=
  (HABLargePrimeProduct.source ops p b).translate
private theorem raw_spec (ops : ShortProducts) {U k : ℕ} (p b : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U)
    (hp : (e p).val.Prime) : (raw ops p b).eval A e=true ↔
      (e b).val=(∏ i : Fin U,HAB.rowWord (A i))%(e p).val := by
  rw [raw,HAB.Form.translate_correct,HABLargePrimeProduct.source_correct ops p b A e hp,eq_comm]

/-- Graph of the residue of the product of the entire selected basis. -/
noncomputable def modulus (ops : ShortProducts) {n : ℕ} (basis : Template (n+1)) : Template (n+2) :=
  HABMatrix.bind (digit basis) (raw ops (1 : Fin 2) 0)
    (fun i => i.succ.succ) ![0,1]

theorem modulus_spec (ops : ShortProducts) {n U : ℕ} (basis : Template (n+1)) (A : HAB.Matrix U) (e : Fin n→Fin U)
    (s : Finset ℕ) (fits : Fits (U:=U) s) (members : Members basis A e s)
    (p b : Fin U) (hp : p.val.Prime) (_wide : p.val^3<U) :
    (modulus ops basis).eval A (extend b p e) = true ↔ b.val=HABCRTRecovery.modulus s%p.val := by
  rw [modulus,HABMatrix.bind_spec]
  let g (a : ℕ) := if a∈s then a else 1
  have hmat (r c : Fin U) := digit_spec basis A e s members r c
  have eq : (fun r c : Fin U => (digit basis).eval A (extend c r (extend b p e ∘ fun i => i.succ.succ))) =
      fun r c => (g r.val).testBit c.val := funext fun r => funext fun c => hmat r c
  rw [eq,raw_spec ops _ _ _ _ hp]
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

/-- Residue of the product with this same target prime omitted. -/
noncomputable def cofactor (ops : ShortProducts) {n : ℕ} (basis : Template (n+1)) : Template (n+2) :=
  ren (modulus ops (erase basis)) (Fin.cases 0 (Fin.cases 1 (Fin.cases 1 (fun i => i.succ.succ))))

theorem cofactor_spec (ops : ShortProducts) {n U : ℕ} (basis : Template (n+1)) (A : HAB.Matrix U) (e : Fin n→Fin U)
    (s : Finset ℕ) (fits : Fits (U:=U) s) (members : Members basis A e s)
    (p b : Fin U) (hp : p.val.Prime) (wide : p.val^3<U) :
    (cofactor ops basis).eval A (extend b p e)=true ↔ b.val=HABCRTRecovery.cofactor s p.val%p.val := by
  rw [cofactor,ren_spec]
  have eq : extend b p e ∘ Fin.cases 0 (Fin.cases 1 (Fin.cases 1 (fun i : Fin n => i.succ.succ))) =
      extend b p (push p e) := by
    funext i; refine Fin.cases rfl (fun j => ?_) i; refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => rfl) j
  rw [eq]
  exact modulus_spec ops _ _ _ _ (fun r hr => fits r (Finset.mem_of_mem_erase hr)) (erase_spec _ _ _ _ members p) p b hp wide

private noncomputable def powAt (ops : ShortProducts) {k : ℕ} (a t p b : Fin k) : Template k :=
  ren (HABPowerReduction.source ops).translate ![p,a,t,b]

private theorem powAt_spec (ops : ShortProducts) {k U : ℕ} (a t p b : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U)
    (hp : (e p).val.Prime) (ha : (e a).val<(e p).val) :
    (powAt ops a t p b).eval A e=true ↔ (e b).val=(e a).val^(e t).val%(e p).val := by
  rw [powAt,ren_spec,HAB.Form.translate_correct]
  have he : e ∘ ![p,a,t,b]=![e p,e a,e t,e b] := by funext i;fin_cases i <;> rfl
  rw [he,HABPowerReduction.source_correct ops A _ _ _ _ hp ha,eq_comm]

private noncomputable def invAt (ops : ShortProducts) {k : ℕ} (x p b : Fin k) : Template k :=
  .ex (.conj (diff2 p.succ 0) (powAt ops x.succ 0 p.succ b.succ))

private theorem invAt_spec (ops : ShortProducts) {k U : ℕ} (x p b : Fin k) (A : HAB.Matrix U)
    (v : Fin k→Fin U) (hp : (v p).val.Prime) (hx : (v x).val<(v p).val) :
    (invAt ops x p b).eval A v=true ↔ (v b).val=(v x).val^((v p).val-2)%(v p).val := by
  have hp2 := hp.two_le
  have hU := hp2.trans_lt (v p).isLt
  let t : Fin U := ⟨(v p).val-2,by omega⟩
  have hw := powAt_spec ops x.succ (0 : Fin (k+1)) p.succ b.succ A (push t v) hp hx
  simp only [invAt,Tex_true,Tconj_true,diff2_spec _ _ _ _ hU,Fin.cases_zero,Fin.cases_succ]
  constructor
  · rintro ⟨z,hz,chk⟩
    have he : z=t := Fin.ext (by dsimp [t];omega)
    subst z;exact hw.mp chk
  · intro h;exact ⟨t,by dsimp [t];omega,hw.mpr h⟩

/-- The distinguished coefficient multiplier, computed by Fermat inversion
from the cofactor residue. -/
noncomputable def inverse (ops : ShortProducts) {n : ℕ} (basis : Template (n+1)) : Template (n+2) :=
  .ex (.conj (graphAt (cofactor ops basis) 0 2 (fun i => i.succ.succ.succ)) (invAt ops 0 2 1))

theorem inverse_spec (ops : ShortProducts) {n U : ℕ} (basis : Template (n+1)) (A : HAB.Matrix U) (e : Fin n→Fin U)
    (s : Finset ℕ) (fits : Fits (U:=U) s) (members : Members basis A e s)
    (p b : Fin U) (hp : p.val.Prime) (wide : p.val^3<U) :
    (inverse ops basis).eval A (extend b p e)=true ↔ b.val=HABCRTRecovery.inverse s p.val := by
  let t : Fin U := ⟨HABCRTRecovery.cofactor s p.val%p.val,(Nat.mod_lt _ hp.pos).trans p.isLt⟩
  have graph (w : Fin U) : (graphAt (cofactor ops basis) 0 2 (fun i => i.succ.succ.succ)).eval A (push w (extend b p e))=true ↔
      w.val=t.val := by rw [graphAt_spec]; exact cofactor_spec ops basis A e s fits members p w hp wide
  have chk := invAt_spec ops (0 : Fin (n+3)) 2 1 A (push t (extend b p e)) hp (Nat.mod_lt _ hp.pos)
  simp only [inverse,Tex_true,Tconj_true]
  constructor
  · rintro ⟨w,hw,h⟩
    have eq : w=t := Fin.ext ((graph w).mp hw)
    subst w;exact chk.mp h
  · intro h;exact ⟨t,(graph t).mpr rfl,chk.mpr h⟩

/-- Graph of the CRT coefficient formed from the input's residue graph and
the inverse of its basis cofactor. -/
noncomputable def coefficient (ops : ShortProducts) {n : ℕ} (basis : Template (n+1)) (input : Template (n+2)) : Template (n+2) :=
  .ex (.conj (graphAt input 0 2 (fun i => i.succ.succ.succ)) (.ex (.conj
    (graphAt (inverse ops basis) 0 3 (fun i => i.succ.succ.succ.succ)) (mulModAt 1 0 3 2))))

theorem coefficient_spec (ops : ShortProducts) {n U : ℕ} (basis : Template (n+1)) (input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (s : Finset ℕ) (fits : Fits (U:=U) s)
    (members : Members basis A e s) (p b : Fin U) (hp : p.val.Prime) (wide : p.val^3<U)
    (x : ℕ) (data : ∀ z : Fin U, input.eval A (extend z p e)=true ↔ z.val=x%p.val) :
    (coefficient ops basis input).eval A (extend b p e)=true ↔
      b.val=HABCRTRecovery.coeff (HABCRTRecovery.inverse s) x p.val := by
  let r : Fin U := ⟨x%p.val,(Nat.mod_lt _ hp.pos).trans p.isLt⟩
  have hI : HABCRTRecovery.inverse s p.val < p.val := Nat.mod_lt _ hp.pos
  let inv : Fin U := ⟨HABCRTRecovery.inverse s p.val,hI.trans p.isLt⟩
  have valG (w : Fin U) : (graphAt input 0 2 (fun i=>i.succ.succ.succ)).eval A (push w (extend b p e))=true ↔
      w.val=r.val := by rw [graphAt_spec]; exact data w
  have invG (w z : Fin U) : (graphAt (inverse ops basis) 0 3 (fun i=>i.succ.succ.succ.succ)).eval A (push z (push w (extend b p e)))=true ↔
      z.val=inv.val := by rw [graphAt_spec]; exact inverse_spec ops basis A e s fits members p z hp wide
  have pfit : p.val*p.val<U := square_lt hp wide
  have chk := mulModAt_spec (1 : Fin (n+4)) 0 3 2 A (push inv (push r (extend b p e))) hp.pos
    ((Nat.mul_le_mul (Nat.mod_lt x hp.pos).le hI.le).trans_lt pfit)
  simp only [coefficient,Tex_true,Tconj_true]
  constructor
  · rintro ⟨w,hw,z,hz,h⟩
    have e1 : w=r := Fin.ext ((valG w).mp hw)
    have e2 : z=inv := Fin.ext ((invG w z).mp hz)
    subst w;subst z;exact chk.mp h
  · intro h;exact ⟨r,(valG r).mpr rfl,inv,(invG r inv).mpr rfl,chk.mpr h⟩


open HABCRTNumerator (factor halfAt halfAt_spec prefix_eq)
private def mux {k : ℕ} (c x y : Template k) : Template k := .disj (.conj c x) (.conj (.neg c) y)
private theorem mux_spec {k U : ℕ} (c x y : Template k) (A : HAB.Matrix U) (e : Fin k→Fin U) :
    (mux c x y).eval A e = if c.eval A e then x.eval A e else y.eval A e := by
  cases h : c.eval A e <;> simp [mux,Template.eval,h]

/-- The graph in the slots y, i, p, parameters. -/
private noncomputable def halfCell (ops : ShortProducts) {n : ℕ} (length : Fin n) (blocks : Template (n+2)) : Template (n+3) :=
  mux (fromFormula (ltF 1 length.succ.succ.succ))
    (.ex (.conj (graphAt (modulus ops blocks) 0 3
        (Fin.cases 2 (fun i => i.succ.succ.succ.succ))) (halfAt 1 0 3)))
    (fromFormula (isNat 1 0))

private theorem halfCell_spec (ops : ShortProducts) {n U : ℕ} (length : Fin n) (blocks : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (family : ℕ→Finset ℕ) (p i y : Fin U)
    (hp : p.val.Prime) (ho : Odd p.val) (wide : p.val^3<U)
    (fits : ∀ i : Fin U, i.val<(e length).val → Fits (U:=U) (family i.val))
    (members : ∀ i : Fin U, i.val<(e length).val → Members blocks A (push i e) (family i.val))
    (odd : ∀ i : Fin U, i.val<(e length).val → Odd (HABCRTRecovery.modulus (family i.val))) :
    (halfCell ops length blocks).eval A (extend y i (push p e))=true ↔
      y.val=factor family (e length).val i.val%p.val := by
  let env := extend y i (push p e)
  have c : (fromFormula (ltF (1:Fin (n+3)) length.succ.succ.succ)).eval A env =
      decide (i.val<(e length).val) := by
    apply Bool.eq_iff_iff.mpr;rw [fromFormula_eval,ltF_true,decide_eq_true_eq];rfl
  change (halfCell ops length blocks).eval A env=true ↔ _
  rw [halfCell,mux_spec,c,factor]
  by_cases hi : i.val<(e length).val
  · simp only [hi,decide_true,if_true,Tex_true,Tconj_true]
    let z : Fin U := ⟨HABCRTRecovery.modulus (family i.val)%p.val,(Nat.mod_lt _ hp.pos).trans p.isLt⟩
    have chk (w : Fin U) : (graphAt (modulus ops blocks) 0 3
          (Fin.cases 2 (fun q => q.succ.succ.succ.succ))).eval A (push w env)=true ↔ w.val=z.val := by
      rw [graphAt_spec]
      have par : (push w env) ∘ (Fin.cases 2 (fun q : Fin n => q.succ.succ.succ.succ)) = push i e := by
        funext j;refine Fin.cases rfl (fun _=>rfl) j
      rw [par]
      exact modulus_spec ops blocks A (push i e) (family i.val) (fits i hi) (members i hi) p w hp wide
    have hcap : p.val*p.val<U := square_lt hp wide
    have h := halfAt_spec (1:Fin (n+4)) 0 3 A (push z env) hp ho (odd i hi) rfl hcap
    exact ⟨fun ⟨w,hw,hv⟩ => h.mp ((show w=z from Fin.ext ((chk w).mp hw)) ▸ hv),
      fun hv=>⟨z,(chk z).mpr rfl,h.mpr hv⟩⟩
  · simp only [hi,decide_false,Bool.false_eq_true,if_false,fromFormula_eval,isNat_spec,Nat.mod_eq_of_lt hp.one_lt]
    rfl


/-- Turn the unique residue supplied at a row into its ordinary binary word. -/
private def bits {n : ℕ} (graph : Template (n+2)) : Template (n+2) :=
  .ex (.conj (ren graph (Fin.cases 0 (fun i => i.succ.succ))) (.bit 0 1))

private theorem bits_spec {n U : ℕ} (graph : Template (n+2)) (A : HAB.Matrix U) (e : Fin n→Fin U)
    (r c : Fin U) (v : Fin U)
    (read : ∀ z : Fin U, graph.eval A (extend z r e)=true ↔ z.val=v.val) :
    (bits graph).eval A (extend c r e)=v.val.testBit c.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [bits,Tex_true,Tconj_true,ren_spec,Template.eval.eq_2]
  have env (w : Fin U) : (push w (extend c r e)) ∘ Fin.cases 0 (fun i : Fin (n+1) => i.succ.succ) =
      extend w r e := by funext i;refine Fin.cases rfl (fun j=>?_) i;refine Fin.cases rfl (fun _=>rfl) j
  constructor
  · rintro ⟨z,hz,h⟩
    have z_eq : z=v := Fin.ext ((read z).mp (env z ▸ hz))
    subst z;exact h
  · intro h;exact ⟨v, (env v).symm ▸ (read v).mpr rfl,h⟩

private noncomputable def halfProduct (ops : ShortProducts) {n : ℕ} (length : Fin n) (blocks : Template (n+2)) :
    Template (n+2) :=
  HABMatrix.bind (bits (halfCell ops length blocks)) (raw ops (1 : Fin 2) 0) Fin.succ ![0,1]

private theorem product_mod (f : ℕ→ℕ) (p k : ℕ) :
    (∏ i ∈ Finset.range k, f i % p) ≡ (∏ i ∈ Finset.range k, f i) [MOD p] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [Finset.prod_range_succ] using ih.mul (Nat.mod_modEq (f k) p)

private theorem halfProduct_spec (ops : ShortProducts) {n U : ℕ} (length : Fin n) (blocks : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (family : ℕ→Finset ℕ) (p b : Fin U)
    (hp : p.val.Prime) (ho : Odd p.val) (wide : p.val^3<U)
    (fits : ∀ i : Fin U, i.val<(e length).val → Fits (U:=U) (family i.val))
    (members : ∀ i : Fin U, i.val<(e length).val → Members blocks A (push i e) (family i.val))
    (odd : ∀ i : Fin U, i.val<(e length).val → Odd (HABCRTRecovery.modulus (family i.val))) :
    (halfProduct ops length blocks).eval A (extend b p e)=true ↔
      b.val=(∏ i ∈ Finset.range (e length).val,(HABCRTRecovery.modulus (family i)+1)/2)%p.val := by
  rw [halfProduct,HABMatrix.bind_spec]
  let f := factor family (e length).val
  let residue (r : Fin U) : Fin U := ⟨f r.val%p.val,(Nat.mod_lt _ hp.pos).trans p.isLt⟩
  have M : (fun r c : Fin U => (bits (halfCell ops length blocks)).eval A (extend c r (extend b p e ∘ Fin.succ))) =
      fun r c => (residue r).val.testBit c.val := by
    funext r c
    apply bits_spec (halfCell ops length blocks) A (push p e) r c (residue r)
    exact fun z => halfCell_spec ops length blocks A e family p r z hp ho wide fits members odd
  have he : extend b p e ∘ (![0,1] : Fin 2→Fin (n+2)) = ![b,p] := by funext q;fin_cases q <;> rfl
  rw [M,he,raw_spec ops _ _ _ _ hp]
  have word (r : Fin U) : HAB.rowWord (fun c : Fin U => (residue r).val.testBit c.val)=(residue r).val :=
    HAB.rowWord_natural ((residue r).isLt.trans Nat.lt_two_pow_self)
  simp_rw [word]
  change b.val=(∏ r : Fin U,f r.val%p.val)%p.val ↔ _
  rw [Fin.prod_univ_eq_prod_range (fun i => f i % p.val) U]
  rw [show (∏ i ∈ Finset.range U,f i%p.val)%p.val=(∏ i ∈ Finset.range U,f i)%p.val from product_mod .., ←prefix_eq]
  change b.val=productPrefix (fun i=>if i<(e length).val then _ else 1) U%p.val ↔ _
  rw [product_pad _ (e length).isLt.le,prefix_eq]

/-- The numerator residue graph. Block i in the supplied family is A_(i+1)
in HAB notation, so a shift of length s uses exactly the first s rows. -/
noncomputable def numerator (ops : ShortProducts) {n : ℕ} (length : Fin n) (blocks input : Template (n+2)) : Template (n+2) :=
  .ex (.conj (graphAt input 0 2 (fun i => i.succ.succ.succ)) (.ex (.conj
    (graphAt (halfProduct ops length blocks) 0 3 (fun i => i.succ.succ.succ.succ))
    (HABCRTCoefficients.mulModAt 1 0 3 2))))

theorem numerator_spec (ops : ShortProducts) {n U : ℕ} (length : Fin n) (blocks input : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n→Fin U) (family : ℕ→Finset ℕ) (x : ℕ) (p b : Fin U)
    (hp : p.val.Prime) (ho : Odd p.val) (wide : p.val^3<U)
    (fits : ∀ i : Fin U, i.val<(e length).val → Fits (U:=U) (family i.val))
    (members : ∀ i : Fin U, i.val<(e length).val → Members blocks A (Fin.cases i e) (family i.val))
    (odd : ∀ i : Fin U, i.val<(e length).val → Odd (HABCRTRecovery.modulus (family i.val)))
    (data : ∀r : Fin U, input.eval A (extend r p e)=true ↔ r.val=x%p.val) :
    (numerator ops length blocks input).eval A (extend b p e)=true ↔
      b.val=(x*(∏ i ∈ Finset.range (e length).val,(HABCRTRecovery.modulus (family i)+1)/2))%p.val := by
  let y := ∏ i ∈ Finset.range (e length).val,(HABCRTRecovery.modulus (family i)+1)/2
  let xr : Fin U := ⟨x%p.val,(Nat.mod_lt _ hp.pos).trans p.isLt⟩
  let yr : Fin U := ⟨y%p.val,(Nat.mod_lt _ hp.pos).trans p.isLt⟩
  have valG (w : Fin U) : (graphAt input 0 2 (fun i=>i.succ.succ.succ)).eval A (push w (extend b p e))=true ↔
      w.val=xr.val := by rw [graphAt_spec];exact data w
  have prodG (w z : Fin U) : (graphAt (halfProduct ops length blocks) 0 3 (fun i=>i.succ.succ.succ.succ)).eval A
      (push z (push w (extend b p e)))=true ↔ z.val=yr.val := by
    rw [graphAt_spec];exact halfProduct_spec ops length blocks A e family p z hp ho wide fits members odd
  have pfit : p.val*p.val<U := square_lt hp wide
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

end DiophantineNP.HABWideCoefficients
