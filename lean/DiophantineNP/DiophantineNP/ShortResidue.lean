import DiophantineNP.ShortPower
import DiophantineNP.SmallSumTemplate
import Mathlib.FieldTheory.Finite.Basic

/-! # Products in a short prime residue field

A bounded rectangular array of unary columns fits in a single majority
quantifier. In Chinese remainder representation this gives iterated
multiplication by adding discrete logarithms, including zero factors.
-/
namespace DiophantineNP.ShortResidue
open Counting WidthFormula PrimeFormula FiniteArithmeticGap Finset

/-- Ordinary integer primitive root, stated without finite-field coercions. -/
theorem primitive_root {p : ℕ} (hp : p.Prime) :
    ∃ g, 0<g ∧ g<p ∧ ∀ y, 0<y → y<p → ∃ j<p-1, g^j%p=y := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨g,hg⟩ := IsCyclic.exists_monoid_generator (α:=(ZMod p)ˣ)
  have hn : (g : ZMod p).val ≠ 0 := by
    intro h
    exact g.ne_zero ((ZMod.val_eq_zero _).mp h)
  refine ⟨(g : ZMod p).val, Nat.pos_of_ne_zero hn, ZMod.val_lt _, fun y hy hyp => ?_⟩
  have hyn : (y : ZMod p) ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    simp [ZMod.val_natCast_of_lt hyp] at hh
    omega
  let u := Units.mk0 (y : ZMod p) hyn
  obtain ⟨j,hj⟩ := (Submonoid.mem_powers_iff _ _).mp (hg u)
  let D := Fintype.card (ZMod p)ˣ
  have hmod : g^(j%D)=g^j := pow_mod_card _ _
  have he : (↑g : ZMod p)^(j%D)=(y : ZMod p) := by
    exact congrArg Units.val (hmod.trans hj)
  refine ⟨j%D,by rw [← ZMod.card_units p]; exact Nat.mod_lt _ Fintype.card_pos,?_⟩
  rw [← ZMod.val_natCast, Nat.cast_pow,ZMod.natCast_zmod_val,he,ZMod.val_natCast_of_lt hyp]

/-- Reduction of an exponent modulo p−1 is valid for any nonzero residue. -/
theorem reduce_exponent {p g : ℕ} (hp : p.Prime) (hg : 0<g) (hgp : g<p) (j : ℕ) :
    g^(j%(p-1))%p=g^j%p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hh : (g:ZMod p) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    simp [ZMod.val_natCast_of_lt hgp] at this
    omega
  let u := Units.mk0 (g:ZMod p) hh
  have he := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) (pow_mod_card u j)
  rw [ZMod.card_units] at he
  change (g:ZMod p) ^ (j%(p-1)) = (g:ZMod p)^j at he
  simpa only [← Nat.cast_pow, ZMod.val_natCast] using congrArg ZMod.val he

theorem logs_product (f l : ℕ → ℕ) (g p n : ℕ) (h : ∀ i<n, g^(l i)%p=f i%p) :
    g^(Readout.prefixSum l n)%p = productPrefix f n % p := by
  induction n with
  | zero => simp [Readout.prefixSum,productPrefix]
  | succ n ih =>
    rw [Readout.prefixSum,product_succ,pow_add,Nat.mul_mod,Nat.mul_mod (productPrefix f n),
      ih (fun i hi => h i (by omega)),h n (by omega)]

/-- A named presentation of the existing template syntax. All variables
compile to ordinary indices; relation entries keep their row/column order. -/
structure Predicate where
  syntaxF : {k : ℕ} → (ℕ → Fin k) → Template k
  holds : ℕ → (ℕ → ℕ → Bool) → (ℕ → ℕ) → Prop
  valid {k U : ℕ} (σ : ℕ → Fin k) (table : ℕ → ℕ → Bool) (env : Fin k → Fin U) :
    (syntaxF σ).eval (fun r c => table r.val c.val) env=true ↔ holds U table (fun i => (env (σ i)).val)

namespace Predicate
def both (p q : Predicate) : Predicate where
  syntaxF σ := .conj (p.syntaxF σ) (q.syntaxF σ)
  holds U t e := p.holds U t e ∧ q.holds U t e
  valid σ t e := by rw [Tconj_true,p.valid,q.valid]

def neg (p : Predicate) : Predicate where
  syntaxF σ := .neg (p.syntaxF σ)
  holds U t e := ¬p.holds U t e
  valid σ t e := by simp only [Template.eval, Bool.not_eq_true',← Bool.not_eq_true,p.valid]

def either (p q : Predicate) : Predicate where
  syntaxF σ := .disj (p.syntaxF σ) (q.syntaxF σ)
  holds U t e := p.holds U t e ∨ q.holds U t e
  valid σ t e := by rw [Tdisj_true,p.valid,q.valid]

private theorem pushEnv {k U : ℕ} (x : ℕ) (σ : ℕ → Fin k) (env : Fin k → Fin U) (z : Fin U) :
    (fun i => ((Fin.cases z env : Fin (k+1) → Fin U) (Function.update (Fin.succ ∘ σ) x 0 i)).val) =
      Function.update (fun i => (env (σ i)).val) x z.val := by
  funext i
  by_cases h : i=x
  · subst i; simp
  · simp [h]

def ex (x : ℕ) (p : Predicate) : Predicate where
  syntaxF σ := .ex (p.syntaxF (Function.update (Fin.succ ∘ σ) x 0))
  holds U t e := ∃ j<U, p.holds U t (Function.update e x j)
  valid {k U} σ t env := by
    rw [Tex_true]
    simp_rw [p.valid,pushEnv]
    constructor
    · rintro ⟨j,h⟩; exact ⟨j,j.isLt,h⟩
    · rintro ⟨j,hj,h⟩; exact ⟨⟨j,hj⟩,h⟩

noncomputable def maj (x : ℕ) (p : Predicate) : Predicate := by
  classical
  exact { syntaxF := fun σ => .maj (p.syntaxF (Function.update (Fin.succ ∘ σ) x 0))
          holds := fun U t e => U/2 < ((range U).filter (fun j => p.holds U t (Function.update e x j))).card
          valid := by
            intro k U σ t env
            change decide (U/2 < count _) = true ↔ _
            rw [decide_eq_true_eq]
            apply Iff.of_eq
            apply congrArg (fun n => U/2 < n)
            unfold count
            apply Finset.card_bij (fun j _ => j.val)
            · intro j hj
              simp only [mem_filter,mem_univ,true_and,p.valid,pushEnv] at hj
              exact mem_filter.mpr ⟨mem_range.mpr j.isLt,hj⟩
            · intro _ _ _ _ h; exact Fin.ext h
            · intro x hx
              obtain ⟨hx,h⟩ := mem_filter.mp hx
              refine ⟨⟨x,mem_range.mp hx⟩,?_,rfl⟩
              simp only [mem_filter,mem_univ,true_and,p.valid,pushEnv]
              exact h }

def entry (r c : ℕ) : Predicate where
  syntaxF σ := .entry (σ r) (σ c)
  holds _ t env := t (env r) (env c) = true
  valid _ _ _ := Iff.rfl

def eqN (x m : ℕ) : Predicate where
  syntaxF σ := fromFormula (isNat m (σ x))
  holds _ _ e := e x=m
  valid _ _ _ := by rw [fromFormula_eval,isNat_spec]

def lt (x y : ℕ) : Predicate where
  syntaxF σ := fromFormula (ltF (σ x) (σ y))
  holds _ _ e := e x<e y
  valid _ _ _ := by rw [fromFormula_eval,ltF_true]

def le (x y : ℕ) : Predicate := (lt y x).neg

def add (x y z : ℕ) : Predicate where
  syntaxF σ := fromFormula (addF (σ x) (σ y) (σ z))
  holds _ _ e := e x+e y=e z
  valid _ _ _ := by rw [fromFormula_eval,addF_spec]

def mul (x y z : ℕ) : Predicate where
  syntaxF σ := fromFormula (mulF (σ x) (σ y) (σ z))
  holds _ _ e := e x*e y=e z
  valid _ _ _ := by rw [fromFormula_eval,mulF_spec]

/-- The suffix with exactly floor(U/2)−s elements. Defined by an offset from
the upper half, whose first element is the ceiling of U/2. -/
private def top (x : ℕ) : Predicate where
  syntaxF σ := .neg (.maj (.atom (.leq (σ x).succ 0)))
  holds U _ e := U-U/2 ≤ e x
  valid {k U} σ t env := by
    change (!decide (U/2 < count (fun z : Fin U => decide ((env (σ x)).val ≤ z.val))))=true ↔ _
    have hf : Finset.univ.filter (fun z : Fin U => decide ((env (σ x)).val ≤ z.val) = true) = Finset.Ici (env (σ x)) := by
      ext a; simp only [mem_filter,mem_univ,true_and,decide_eq_true_eq,mem_Ici]; rfl
    rw [count,hf,Fin.card_Ici]
    simp; omega

private def suffix (z s : ℕ) : Predicate where
  syntaxF σ := .ex (.conj ((top 0).syntaxF (fun _ => 0))
    (fromFormula (addF 0 (σ s).succ (σ z).succ)))
  holds U _ e := U-U/2+e s≤e z
  valid {k U} σ t env := by
    rw [Tex_true]
    simp only [Tconj_true,(top 0).valid,fromFormula_eval,addF_spec,Fin.cases_succ,Fin.cases_zero]
    change (∃v : Fin U, U-U/2 ≤ v.val ∧ v.val+(env (σ s)).val=(env (σ z)).val) ↔ _
    constructor
    · rintro ⟨v,hv,he⟩; omega
    · intro h
      exact ⟨⟨(env (σ z)).val-(env (σ s)).val,by have := (env (σ z)).isLt; omega⟩,by dsimp; omega,by dsimp; omega⟩

end Predicate
open Predicate
local infixr:35 " ⋀ " => Predicate.both

private noncomputable def countLower (extra : Bool) (z s : ℕ) (h : Predicate) :=
  Predicate.maj z ((if extra then (eqN z 0).either h else h).either (Predicate.suffix z s))

private theorem countLower_iff (extra : Bool) (z s : ℕ) (hsz : s ≠ z) (h : Predicate)
    (U : ℕ) (t : ℕ → ℕ → Bool) (env : ℕ → ℕ) (S : Finset ℕ) (h0 : 0∉S)
    (hU : 1<U) (hshort : ∀ j∈S,j<U-U/2) (ht : env s ≤ U/2)
    (hh : ∀ j<U, h.holds U t (Function.update env z j) ↔ j∈S) :
    (countLower extra z s h).holds U t env ↔ env s < S.card+extra.toNat := by
  classical
  let low := if extra then insert 0 S else S
  have hlow (j : ℕ) (hj : j∈low) : j<U-U/2 := by
    cases extra with
    | false => exact hshort j hj
    | true =>
      rcases mem_insert.mp hj with rfl|hx
      · omega
      · exact hshort j hx
  let c := U-U/2 + env s
  have hc : c ≤ U := by dsimp [c]; omega
  have hd : Disjoint low (Ico c U) := by
    apply disjoint_left.mpr
    intro j hx hy
    have := hlow j hx
    have := (mem_Ico.mp hy).1
    dsimp [c] at *; omega
  have cardLow : low.card=S.card+extra.toNat := by cases extra <;> simp [low,h0]
  unfold countLower Predicate.maj
  dsimp only
  have sets : (range U).filter (fun j => ((if extra then (eqN z 0).either h else h).either
      (Predicate.suffix z s)).holds U t (Function.update env z j)) = low ∪ Ico c U := by
    ext j
    by_cases hu : j<U
    · have hm := hh j hu
      simp only [mem_filter,mem_range,hu,true_and,mem_union,mem_Ico,and_true,either,Predicate.suffix,
        Function.update_self,Function.update_of_ne hsz]
      cases extra <;> simp [eqN,low,c,hm]
    · have hx : j∉low := fun he => hu ((hlow j he).trans_le (Nat.sub_le U _))
      simp [hu,hx]
  rw [sets,card_union_of_disjoint hd,Nat.card_Ico,cardLow]
  dsimp [c]; omega

private noncomputable def exactLower (z s : ℕ) (h : Predicate) :=
  (countLower true z s h).both (countLower false z s h).neg

private theorem exactLower_iff (z s : ℕ) (hsz : s ≠ z) (h : Predicate) (U : ℕ)
    (t : ℕ → ℕ → Bool) (env : ℕ→ℕ) (S : Finset ℕ) (h0 : 0∉S)
    (hU : 1<U) (hshort : ∀ j∈S,j<U-U/2) (ht : env s ≤ U/2)
    (hh : ∀ j<U, h.holds U t (Function.update env z j) ↔ j∈S) :
    (exactLower z s h).holds U t env ↔ env s = S.card := by
  change (_ ∧ ¬_) ↔ _
  rw [countLower_iff true z s hsz h U t env S h0 hU hshort ht hh,
    countLower_iff false z s hsz h U t env S h0 hU hshort ht hh]
  simp; omega

private def tally (p : ℕ) (f : ℕ→ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | n+1 => tally p f n ∪ Ico (n*p+1) (n*p+1+f n)

private theorem tally_mem (p : ℕ) (f : ℕ→ℕ) (n z : ℕ) :
    z∈tally p f n ↔ ∃ r<n, ∃ u<f r, z=r*p+u+1 := by
  induction n with
  | zero => simp [tally]
  | succ n ih =>
    simp only [tally,mem_union,mem_Ico,ih]
    constructor
    · rintro (⟨r,hr,u,hu,h⟩|⟨h1,h2⟩)
      · exact ⟨r,by omega,u,hu,h⟩
      · exact ⟨n,by omega,z-(n*p+1),by omega,by omega⟩
    · rintro ⟨r,hr,u,hu,h⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hh|rfl
      · exact Or.inl ⟨r,hh,u,hu,h⟩
      · exact Or.inr ⟨by omega,by omega⟩

private theorem tally_bounds {p n z : ℕ} (f : ℕ→ℕ) (h : ∀ r<n, f r≤p) (hz : z∈tally p f n) :
    0<z ∧ z≤n*p := by
  obtain ⟨r,hr,u,hu,rfl⟩ := (tally_mem ..).mp hz
  have := h r hr
  have hm := Nat.mul_le_mul_right p (show r+1≤n by omega)
  rw [Nat.succ_mul] at hm
  omega

private theorem tally_card {p : ℕ} (f : ℕ→ℕ) (n : ℕ) (h : ∀ r<n, f r≤p) :
    (tally p f n).card = Readout.prefixSum f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hh := fun (r : ℕ) (hr : r<n) => h r (by omega)
    have hd : Disjoint (tally p f n) (Ico (n*p+1) (n*p+1+f n)) := by
      apply disjoint_left.mpr
      intro z h1 h2
      have := (tally_bounds f hh h1).2
      have := (mem_Ico.mp h2).1
      omega
    simp [tally,card_union_of_disjoint hd,ih hh,Readout.prefixSum]

/-- Variables 0,1,4 are the row count, column bound and proposed sum.
Slot 5 codes a cell, slots 6 and 7 carry its row and column. The cell (r,u)
is encoded by r*p+u+1; zero is reserved for the strict-majority correction. -/
private def rectangle (cell : Predicate) : Predicate :=
  Predicate.ex 6 <| Predicate.ex 7 <| lt 6 0 ⋀ lt 7 1 ⋀ cell ⋀
    (Predicate.ex 8 <| Predicate.ex 9 <| Predicate.ex 10 <|
      mul 6 1 8 ⋀ add 8 7 9 ⋀ eqN 10 1 ⋀ add 9 10 5)

def cellEnv (env : ℕ→ℕ) (z r u : ℕ) := Function.update (Function.update (Function.update env 5 z) 6 r) 7 u

private theorem rectangle_spec (cell : Predicate) (U : ℕ) (t : ℕ→ℕ→Bool) (env : ℕ→ℕ) (f : ℕ→ℕ)
    (hn : env 0 < U) (hp : env 1 < U) (hU : 1<U) (hb : ∀ r<env 0, f r≤env 1)
    (hcell : ∀ z<U, ∀ r<env 0, ∀ u<env 1, cell.holds U t (cellEnv env z r u) ↔ u<f r) (z : ℕ) (hz : z<U) :
    (rectangle cell).holds U t (Function.update env 5 z) ↔ z∈tally (env 1) f (env 0) := by
  rw [tally_mem]
  simp only [rectangle,Predicate.ex,Predicate.both,lt,mul,add,eqN]
  constructor
  · rintro ⟨r,hr,u,hu,hs,hs',hc,d,hd,c,hd',one,h1,hm,ha,ho,ha'⟩
    simp [Function.update] at hs hs' hm ha ho ha'
    exact ⟨r,hs,u,(hcell z hz r hs u hs').mp hc,by omega⟩
  · rintro ⟨r,hr,u,hu,hz'⟩
    have ht := hb r hr
    refine ⟨r,hr.trans hn,u,hu.trans_le ht |>.trans hp,?_,?_,(hcell z hz r hr u (hu.trans_le ht)).mpr hu,
      r*(env 1),by omega,r*(env 1)+u,by omega,1,hU,?_,?_,?_,?_⟩ <;> simp [Function.update] <;> omega

noncomputable def summed (cell : Predicate) : Predicate := exactLower 5 4 (rectangle cell)

theorem summed_spec (cell : Predicate) (U : ℕ) (t : ℕ→ℕ→Bool) (env : ℕ→ℕ) (f : ℕ→ℕ)
    (hn : env 0 < U) (hp : env 1 < U) (hU : 1<U) (hb : ∀ r<env 0, f r≤env 1)
    (hsize : env 0*env 1<U-U/2) (hs : env 4≤U/2)
    (hcell : ∀ z<U, ∀ r<env 0, ∀ u<env 1, cell.holds U t (cellEnv env z r u) ↔ u<f r) :
    (summed cell).holds U t env ↔ env 4 = Readout.prefixSum f (env 0) := by
  rw [summed,exactLower_iff _ _ (by decide) _ _ _ _ (tally (env 1) f (env 0)),
    tally_card f _ hb]
  · exact fun h => by have := (tally_bounds f hb h).1; omega
  · exact hU
  · exact fun z hz => (tally_bounds f hb hz).2.trans_lt hsize
  · exact hs
  · exact rectangle_spec cell U t env f hn hp hU hb hcell

/-- Unconditional threshold-adder for bounded numerical rows. -/
noncomputable def unarySum : Template 3 := (summed (entry 6 7)).syntaxF (fun i => if i=0 then 0 else if i=1 then 1 else 2)

theorem unarySum_spec {U : ℕ} (n p s : Fin U) (f : ℕ→ℕ) (hU : 1<U)
    (hb : ∀ r<n.val,f r≤p.val) (hsize : n.val*p.val<U-U/2) (hs : s.val≤U/2) :
    unarySum.eval (fun r c => decide (c.val<f r.val)) ![n,p,s] = true ↔
      s.val=Readout.prefixSum f n.val := by
  let e : ℕ→ℕ := fun i => if i=0 then n.val else if i=1 then p.val else s.val
  have hc := summed_spec (entry 6 7) U (fun r u => decide (u<f r)) e f n.isLt p.isLt hU hb hsize hs
    (fun _ _ _ _ _ _ => by simp [entry,cellEnv,Function.update])
  unfold unarySum
  rw [Predicate.valid _ _ (fun r u => decide (u<f r))]
  simpa [e] using hc

private def arithmetic {n : ℕ} (φ : Formula n) (v : Fin n → ℕ) : Predicate where
  syntaxF σ := rewriteMatrix (fun r c => .entry r c) (fromFormula φ) (σ ∘ v)
  holds U _ e := ∃ w : Fin n → Fin U, (∀ i, (w i).val=e (v i)) ∧ φ.eval w=true
  valid σ t env := by
    rw [rewriteMatrix_eval _ _ (fun r c => t r.val c.val) (by intros; rfl),fromFormula_eval]
    constructor
    · intro h; exact ⟨_,fun _ => rfl,h⟩
    · rintro ⟨w,hw,h⟩
      have e : w=env ∘ (σ ∘ v) := funext fun i => Fin.ext (hw i)
      rwa [e] at h

def shortPow (g j p v : ℕ) : Predicate :=
  arithmetic (ShortPower.formula (0:Fin 4) 1 2 3) ![g,j,p,v]

theorem shortPow_iff (g j p v : ℕ) (U K : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ)
    (hp : (e p).Prime) (hg : e g<e p) (hj : e j<e p) (hv : e v<U) (hpU : e p<U)
    (hK : 2≤K) (hpk : e p ≤ 2^K) (hcap : 2^((K+1)*K)<U) :
    (shortPow g j p v).holds U t e ↔ e v=(e g)^(e j)%(e p) := by
  constructor
  · rintro ⟨w,hw,h⟩
    have hh := ShortPower.formula_sound _ _ _ _ w h
    simpa [hw] using hh
  · intro h
    let w : Fin 4 → Fin U := ![⟨e g,hg.trans hpU⟩,⟨e j,hj.trans hpU⟩,⟨e p,hpU⟩,⟨e v,hv⟩]
    refine ⟨w,fun i => ?_,(ShortPower.formula_correct 0 1 2 3 w hK hg hp.one_lt (hj.trans_le hpk) hpk hcap).mpr h⟩
    fin_cases i <;> rfl

/-- No generator search is required in the finite syntax. It suffices to
guess any nonzero base that supplies a logarithm for each input row. -/
private def hit : Predicate := Predicate.ex 14 (entry 6 14 ⋀ shortPow 3 13 1 14)

private theorem hit_iff {U K p g : ℕ} (f : ℕ→ℕ) (e : ℕ→ℕ) (ep : e 1=p) (eg : e 3=g)
    (hp : p.Prime) (hg : g<p) (hj : e 13<p) (hpU : p<U) (hK : 2≤K) (hpk : p≤2^K)
    (hcap : 2^((K+1)*K)<U) :
    hit.holds U (fun r v => decide (v=f r%p)) e ↔ g^(e 13)%p=f (e 6)%p := by
  simp only [hit,Predicate.ex,Predicate.both,entry,decide_eq_true_eq]
  constructor
  · rintro ⟨v,hv,he,h⟩
    simp [Function.update] at he
    have hh := (shortPow_iff 3 13 1 14 U K _ (Function.update e 14 v)
      (by simpa [Function.update,ep] using hp) (by simpa [Function.update,ep,eg] using hg)
      (by simpa [Function.update,ep] using hj) (by simpa using hv) (by simpa [Function.update,ep] using hpU)
      hK (by simpa [Function.update,ep] using hpk) hcap).mp h
    simp [Function.update,ep,eg] at hh
    omega
  · intro h
    let v := f (e 6)%p
    have hv := (Nat.mod_lt (f (e 6)) hp.pos).trans hpU
    refine ⟨v,hv,by simp [v,Function.update],?_⟩
    apply (shortPow_iff 3 13 1 14 U K _ _
      (by simpa [Function.update,ep] using hp) (by simpa [Function.update,ep,eg] using hg)
      (by simpa [Function.update,ep] using hj) (by simpa using hv) (by simpa [Function.update,ep] using hpU)
      hK (by simpa [Function.update,ep] using hpk) hcap).mpr
    simpa [v,Function.update,ep,eg] using h.symm

private def hasLog : Predicate := Predicate.ex 13 (lt 13 1 ⋀ hit)
private def logCell : Predicate := (Predicate.ex 13 (lt 13 1 ⋀ le 13 7 ⋀ hit)).neg

private theorem logConditions {U K p g : ℕ} (f : ℕ→ℕ) (e : ℕ→ℕ) (ep : e 1=p) (eg : e 3=g)
    (hp : p.Prime) (hg : g<p) (hpU : p<U) (hK : 2≤K) (hpk : p≤2^K) (hcap : 2^((K+1)*K)<U) :
    (hasLog.holds U (fun r v => decide (v=f r%p)) e ↔ ∃ j<p, g^j%p=f (e 6)%p) ∧
    (logCell.holds U (fun r v => decide (v=f r%p)) e ↔ ¬∃ j<p, j≤e 7 ∧ g^j%p=f (e 6)%p) := by
  have he (j : ℕ) (hj : j<p) := hit_iff f (Function.update e 13 j) (by simp [Function.update,ep])
    (by simp [Function.update,eg]) hp hg (by simpa using hj) hpU hK hpk hcap
  simp only [hasLog,logCell,Predicate.neg,Predicate.ex,Predicate.both,le,lt]
  simp [Function.update,ep] at he ⊢
  constructor
  · constructor
    · rintro ⟨j,_,hj,h⟩; exact ⟨j,hj,(he j hj).mp h⟩
    · rintro ⟨j,hj,h⟩; exact ⟨j,hj.trans hpU,hj,(he j hj).mpr h⟩
  · constructor
    · intro h j hj hj7 hh
      exact h j (hj.trans hpU) hj hj7 ((he j hj).mpr hh)
    · intro h j _ hj hj7 hh
      exact h j hj hj7 ((he j hj).mp hh)

private noncomputable def minLog (p g x : ℕ) : ℕ := by
  classical
  exact if h : ∃j<p, g^j%p=x then Nat.find h else p

private theorem minLog_spec {p g x : ℕ} (h : ∃ j<p,g^j%p=x) :
    minLog p g x<p ∧ g^(minLog p g x)%p=x ∧
      ∀ u, (¬∃j<p, j≤u ∧ g^j%p=x) ↔ u<minLog p g x := by
  classical
  rw [minLog,dif_pos h]
  have hf := Nat.find_spec h
  refine ⟨hf.1,hf.2,fun u => ?_⟩
  constructor
  · intro hn
    by_contra! hle
    exact hn ⟨_,hf.1,hle,hf.2⟩
  · rintro hu ⟨j,hj,hju,hpow⟩
    exact (Nat.find_min h (hju.trans_lt hu)) ⟨hj,hpow⟩

private theorem product_zero_iff (f : ℕ→ℕ) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    productPrefix f n%p=0 ↔ ∃ i<n,f i%p=0 := by
  induction n with
  | zero => simp [productPrefix,Nat.mod_eq_of_lt hp.one_lt]
  | succ n ih =>
    rw [product_succ,← Nat.dvd_iff_mod_eq_zero,hp.dvd_mul,Nat.dvd_iff_mod_eq_zero,
      Nat.dvd_iff_mod_eq_zero,ih]
    constructor
    · rintro (⟨i,hi,h⟩|h)
      · exact ⟨i,by omega,h⟩
      · exact ⟨n,by omega,h⟩
    · rintro ⟨i,hi,h⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h'|rfl
      · exact Or.inl ⟨i,h',h⟩
      · exact Or.inr h

private def zeroRow : Predicate := Predicate.ex 6 <| lt 6 0 ⋀ (Predicate.ex 14 (eqN 14 0 ⋀ entry 6 14))

private def covered : Predicate := (Predicate.ex 6 (lt 6 0 ⋀ hasLog.neg)).neg

private def reduceSum : Predicate := Predicate.ex 11 <| Predicate.ex 12 <| Predicate.ex 17 <|
  Predicate.ex 18 <| Predicate.ex 19 <| eqN 17 1 ⋀ add 11 17 1 ⋀ lt 12 11 ⋀ mul 18 11 19 ⋀
    add 19 12 4 ⋀ shortPow 3 12 1 2

private theorem reduceSum_iff {U K p g : ℕ} (f : ℕ→ℕ) (e : ℕ→ℕ) (ep : e 1=p) (eg : e 3=g)
    (hp : p.Prime) (hg : g<p) (hpU : p<U) (hs : e 4<U) (hv : e 2<U) (hK : 2≤K) (hpk : p≤2^K) (hcap : 2^((K+1)*K)<U) :
    reduceSum.holds U (fun r v => decide (v=f r%p)) e ↔ e 2=g^(e 4%(p-1))%p := by
  simp only [reduceSum,Predicate.ex,Predicate.both,eqN,add,lt,mul]
  have hpp := hp.two_le
  constructor
  · rintro ⟨m,hm,j,hj,one,_,q,_,B,_,ho,hpm,hjm,hq,hs',h⟩
    simp [Function.update,ep] at ho hpm hjm hq hs'
    have hd : j=e 4%(p-1) := by
      rw [show p-1=m by omega,← hs',← hq,Nat.mul_comm q m,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hjm]
    let v := Function.update (Function.update (Function.update (Function.update (Function.update e 11 m) 12 j) 17 one) 18 q) 19 B
    have hpow := (shortPow_iff 3 12 1 2 U K _ v (by simpa [v,Function.update,ep] using hp)
      (by simpa [v,Function.update,ep,eg] using hg) (by simp [v,Function.update,ep]; omega)
      (by simpa [v,Function.update] using hv) (by simpa [v,Function.update,ep] using hpU)
      hK (by simpa [v,Function.update,ep] using hpk) hcap).mp h
    simpa [v,Function.update,ep,eg,hd] using hpow
  · intro h
    let m := p-1
    let j := e 4%m
    let q := e 4/m
    have hpos : 0<m := by dsimp [m]; omega
    have hj := Nat.mod_lt (e 4) hpos
    have hjp : j<p := hj.trans_le (Nat.sub_le p 1)
    have hq := Nat.div_le_self (e 4) m
    have hsum : q*m+j=e 4 := by rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    let v := Function.update (Function.update (Function.update (Function.update (Function.update e 11 m) 12 j) 17 1) 18 q) 19 (q*m)
    have hpow : (shortPow 3 12 1 2).holds U (fun r v => decide (v=f r%p)) v := by
      apply (shortPow_iff 3 12 1 2 U K _ v (by simpa [v,Function.update,ep] using hp)
        (by simpa [v,Function.update,ep,eg] using hg) (by simpa [v,Function.update,ep] using hjp)
        (by simpa [v,Function.update] using hv) (by simpa [v,Function.update,ep] using hpU)
        hK (by simpa [v,Function.update,ep] using hpk) hcap).mpr
      simpa [v,Function.update,ep,eg,j,m] using h
    refine ⟨m,by dsimp [m]; omega,j,hjp.trans hpU,1,by omega,q,by omega,q*m,by omega,
      ?_,?_,?_,?_,?_,hpow⟩ <;> simp [Function.update,ep,m] <;> omega

private noncomputable def collect := Predicate.ex 4 <| (Predicate.top 4).neg ⋀ summed logCell ⋀ reduceSum

private noncomputable def program : Predicate :=
  (zeroRow ⋀ eqN 2 0).either (Predicate.ex 3 <| (eqN 3 0).neg ⋀ lt 3 1 ⋀ covered ⋀ collect)

private theorem covered_iff {U K p g : ℕ} (f : ℕ→ℕ) (e : ℕ→ℕ) (ep : e 1=p) (eg : e 3=g)
    (hp : p.Prime) (hg : g<p) (hpU : p<U) (hn : e 0<U)
    (hK : 2≤K) (hpk : p≤2^K) (hcap : 2^((K+1)*K)<U) :
    covered.holds U (fun r v => decide (v=f r%p)) e ↔ ∀ r<e 0, ∃j<p,g^j%p=f r%p := by
  have hl (r : ℕ) := (logConditions f (Function.update e 6 r) (by simp [Function.update,ep])
    (by simp [Function.update,eg]) hp hg hpU hK hpk hcap).1
  simp only [covered,Predicate.neg,Predicate.ex,Predicate.both,lt]
  simp [Function.update] at hl ⊢
  constructor
  · intro h r hr; exact (hl r).mp (h r (hr.trans hn) hr)
  · intro h r _ hr; exact (hl r).mpr (h r hr)

private theorem collect_iff {U K p g : ℕ} (f : ℕ→ℕ) (e : ℕ→ℕ) (ep : e 1=p) (eg : e 3=g)
    (hp : p.Prime) (hg0 : 0<g) (hg : g<p) (hpU : p<U) (hn : e 0<U) (hv : e 2<U)
    (hsize : e 0*p<U-U/2) (hK : 2≤K) (hpk : p≤2^K) (hcap : 2^((K+1)*K)<U)
    (hc : ∀ r<e 0, ∃j<p,g^j%p=f r%p) :
    collect.holds U (fun r v => decide (v=f r%p)) e ↔ e 2=productPrefix f (e 0)%p := by
  let n := e 0
  let l := fun r => minLog p g (f r%p)
  have hlog (r : ℕ) (hr : r<n) := minLog_spec (hc r hr)
  let total := Readout.prefixSum l n
  have hsum (i : ℕ) (hi : i≤n) : Readout.prefixSum l i ≤ i*p := by
    induction i with
    | zero => simp [Readout.prefixSum]
    | succ i ih =>
      rw [Readout.prefixSum,Nat.succ_mul]
      exact Nat.add_le_add (ih (by omega)) (hlog i (by omega)).1.le
  have htotal := hsum n le_rfl
  change total≤e 0*p at htotal
  have hterm (s : ℕ) (hs : s<U-U/2) : (summed logCell).holds U (fun r v => decide (v=f r%p))
      (Function.update e 4 s) ↔ s=total := by
    let e' := Function.update e 4 s
    have e0 : e' 0=n := by simp [e',n]
    have e1 : e' 1=p := by simp [e',ep]
    have e3 : e' 3=g := by simp [e',eg]
    apply summed_spec logCell U _ e' l (e0 ▸ hn) (e1 ▸ hpU) (hp.one_lt.trans hpU)
      (by rintro r hr; rw [e0] at hr; rw [e1]; exact (hlog r hr).1.le)
      (by rw [e0,e1];exact hsize) (by simp [e']; omega)
    intro z _ r hr u _
    rw [e0] at hr
    let w := cellEnv e' z r u
    have h := (logConditions f w (by simp [w,cellEnv,Function.update,e1])
      (by simp [w,cellEnv,Function.update,e3]) hp hg hpU hK hpk hcap).2
    simpa only [w,cellEnv,Function.update_self,Function.update_of_ne (by decide : (6:ℕ)≠7)] using
      h.trans (by simpa [w,cellEnv,Function.update,l] using (hlog r hr).2.2 u)
  have hre (s : ℕ) (hs : s<U) := reduceSum_iff f (Function.update e 4 s) (by simp [Function.update,ep])
    (by simp [Function.update,eg]) hp hg hpU (by simpa using hs) (by simpa [Function.update] using hv) hK hpk hcap
  have hprod : g^(total%(p-1))%p=productPrefix f n%p :=
    (reduce_exponent hp hg0 hg total).trans (logs_product f l g p n (fun r hr => (hlog r hr).2.1))
  simp only [collect,Predicate.ex,Predicate.both,Predicate.neg,Predicate.top,Function.update_self,not_le]
  constructor
  · rintro ⟨s,hs,hc,hv',hh⟩
    have h := (hre s hs).mp hh
    have hst := (hterm s hc).mp hv'
    simpa [Function.update,ep,eg,hst,hprod,n] using h
  · intro h
    have hsmall : total < U-U/2 := htotal.trans_lt hsize
    have hU := hsmall.trans_le (Nat.sub_le _ _)
    refine ⟨total,hU,hsmall,(hterm total hsmall).mpr rfl,(hre total hU).mpr ?_⟩
    simpa [Function.update,ep,eg,hprod,n] using h

private theorem zeroRow_iff {U p : ℕ} (f : ℕ→ℕ) (e : ℕ→ℕ) (hn : e 0<U) :
    zeroRow.holds U (fun r v => decide (v=f r%p)) e ↔ ∃ r<e 0,f r%p=0 := by
  simp [zeroRow,Predicate.ex,Predicate.both,lt,eqN,entry,Function.update]
  constructor
  · rintro ⟨r,_,hr,_,hh⟩; exact ⟨r,hr,hh.symm⟩
  · rintro ⟨r,hr,h⟩; exact ⟨r,hr.trans hn,hr,by omega,h.symm⟩

/-- One fixed binary-relation template returns the complete residue of an
iterated product. The relation supplies (row, residue), and the three free
variables specify row count, prime and the proposed output residue. -/
noncomputable def productResidue : Template 3 :=
  program.syntaxF (fun n => if n=0 then 0 else if n=1 then 1 else 2)

theorem productResidue_spec {U K : ℕ} (n p b : Fin U) (f : ℕ→ℕ) (hp : p.val.Prime)
    (hsize : n.val*p.val<U-U/2) (hK : 2≤K) (hpk : p.val≤2^K) (hcap : 2^((K+1)*K)<U) :
    productResidue.eval (fun r v => decide (v.val=f r.val%p.val)) ![n,p,b]=true ↔
      b.val=productPrefix f n.val%p.val := by
  let t := fun r v => decide (v=f r%p.val)
  let e := fun i : ℕ => (![n,p,b] (if i=0 then 0 else if i=1 then 1 else 2)).val
  unfold productResidue
  rw [Predicate.valid _ _ t]
  change program.holds U t e ↔ _
  have hcov (g : ℕ) (hg : g<p.val) := covered_iff f (Function.update e 3 g)
    (by rfl) (by simp) hp hg p.isLt n.isLt hK hpk hcap
  have hcalc (g : ℕ) (hg0 : 0<g) (hg : g<p.val) := collect_iff f (Function.update e 3 g)
    (by rfl) (by simp) hp hg0 hg p.isLt n.isLt b.isLt hsize hK hpk hcap
  have hz := (zeroRow_iff (p:=p.val) f e n.isLt).trans (product_zero_iff f hp n.val).symm
  change (zeroRow.holds U t e ∧ b.val=0 ∨
    ∃g<U, ¬g=0 ∧ g<p.val ∧ covered.holds U t (Function.update e 3 g) ∧ collect.holds U t (Function.update e 3 g)) ↔ _
  constructor
  · rintro (⟨hh,hb⟩|⟨g,_,hg,hp',hc,h⟩)
    · exact hb.trans (hz.mp hh).symm
    · exact (hcalc g (by omega) hp' ((hcov g hp').mp hc)).mp h
  · intro h
    by_cases hz' : productPrefix f n.val%p.val=0
    · exact Or.inl ⟨hz.mpr hz',h.trans hz'⟩
    · obtain ⟨g,hg0,hg,gen⟩ := primitive_root hp
      have hh (r : ℕ) (hr : r<n.val) : ∃ j<p.val,g^j%p.val=f r%p.val := by
        have hzero : f r%p.val≠0 := fun h0 => hz' ((product_zero_iff f hp n.val).mpr ⟨r,hr,h0⟩)
        obtain ⟨j,hj,he⟩ := gen _ (Nat.pos_of_ne_zero hzero) (Nat.mod_lt _ hp.pos)
        exact ⟨j,by omega,he⟩
      exact Or.inr ⟨g,hg.trans p.isLt,(by omega),hg,(hcov g hg).mpr hh,(hcalc g hg0 hg hh).mpr h⟩

end DiophantineNP.ShortResidue
