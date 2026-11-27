import DiophantineNP.ScalarSignedPower
import DiophantineNP.ScalarDivision
import DiophantineNP.ScalarProjection
import DiophantineNP.Corollary
import DiophantineNP.TailRadix

/-! # Bit bounds for fixed scalar programs -/

namespace DiophantineNP.Blueprint
open LaurentBounds ScalarProgram ScalarProjection FormulaLaurent
open scoped BigOperators
noncomputable section

/-- The output magnitude is polynomial in the input magnitudes. -/
def ValueTame (op : Operation) : Prop :=
  ∃ c : ℕ, ∀ a b : ℤ, (op.apply a b).natAbs ≤ (a.natAbs + b.natAbs + 2)^c

/-- The output bit length is linear in the input bit lengths. -/
def BitTame (op : Operation) : Prop :=
  ∃ c : ℕ, ∀ a b : ℤ, signedBits (op.apply a b) ≤ c * (signedBits a + signedBits b)

/-- The output bit length is linear in the bit length of the first argument
and in the magnitude of the second. This is the growth law of a power. -/
def PowerTame (op : Operation) : Prop :=
  ∃ c : ℕ, ∀ a b : ℤ, signedBits (op.apply a b) ≤ c * (b.natAbs + 1) * signedBits a

/-- Index terms. Their values stay polynomial in the inputs, so they may be
used as exponents. -/
inductive SmallTerm {I : Type} : Term I → Prop
  | input (i : I) : SmallTerm (.input i)
  | literal (z : ℤ) : SmallTerm (.literal z)
  | app {op : Operation} {l r : Term I} :
      ValueTame op → SmallTerm l → SmallTerm r → SmallTerm (.app op l r)

/-- Terms whose intermediate values all have polynomial bit length. A power
is allowed when its exponent is an index term. -/
inductive TameTerm {I : Type} : Term I → Prop
  | small {t : Term I} : SmallTerm t → TameTerm t
  | app {op : Operation} {l r : Term I} :
      BitTame op → TameTerm l → TameTerm r → TameTerm (.app op l r)
  | power {op : Operation} {l r : Term I} :
      PowerTame op → TameTerm l → SmallTerm r → TameTerm (.app op l r)

private def Growth {I : Type} (f : (I → ℤ) → ℕ) : Prop :=
  ∃ c : ℕ, ∀ x B, 2 ≤ B → (∀ i, (x i).natAbs ≤ B) → f x ≤ B^c

private theorem Growth.mono {I : Type} {f g : (I → ℤ) → ℕ} (h : Growth g)
    (hfg : ∀x, f x ≤ g x) : Growth f := by
  obtain ⟨c,hc⟩ := h
  exact ⟨c, fun x B hB hx => (hfg x).trans (hc x B hB hx)⟩

private theorem growth_const {I : Type} (n : ℕ) : Growth (fun _ : I → ℤ => n) := by
  refine ⟨n,fun x B hB _ => ?_⟩
  have hf : n ≤ 2^n := by
    induction n with
    | zero => decide
    | succ n ih => rw [pow_succ]; have h := Nat.two_pow_pos n; omega
  exact hf.trans (Nat.pow_le_pow_left hB _)

private theorem Growth.add {I : Type} {f g : (I → ℤ) → ℕ} (hf : Growth f) (hg : Growth g) :
    Growth fun x => f x + g x := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  refine ⟨max a b+1, fun x B hB hx => ?_⟩
  have hl := (ha x B hB hx).trans (Nat.pow_le_pow_right (by omega : 0 < B) (le_max_left a b))
  have hr := (hb x B hB hx).trans (Nat.pow_le_pow_right (by omega : 0 < B) (le_max_right a b))
  rw [pow_succ]
  have hm := Nat.mul_le_mul_left (B^(max a b)) hB
  change f x + g x ≤ _
  omega

private theorem Growth.mul {I : Type} {f g : (I → ℤ) → ℕ} (hf : Growth f) (hg : Growth g) :
    Growth fun x => f x * g x := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  exact ⟨a+b,fun x B hB hx => (Nat.mul_le_mul (ha x B hB hx) (hb x B hB hx)).trans_eq (pow_add B a b).symm⟩

private theorem Growth.pow {I : Type} {f : (I → ℤ) → ℕ} (hf : Growth f) (n : ℕ) :
    Growth fun x => f x ^ n := by
  obtain ⟨a,ha⟩ := hf
  exact ⟨a*n,fun x B hB hx => (Nat.pow_le_pow_left (ha x B hB hx) n).trans_eq (pow_mul B a n).symm⟩

private theorem Growth.max {I : Type} {f g : (I → ℤ) → ℕ} (hf : Growth f) (hg : Growth g) :
    Growth fun x => max (f x) (g x) :=
  (hf.add hg).mono (fun x => by exact max_le (Nat.le_add_right ..) (Nat.le_add_left ..))

private theorem Growth.signed {I : Type} {f : (I → ℤ) → ℤ}
    (h : Growth fun x => (f x).natAbs) : Growth fun x => signedBits (f x) := by
  apply (h.add (growth_const 2)).mono
  intro x
  dsimp [signedBits, bits]
  have := Nat.log2_le_self (f x).natAbs
  omega

private theorem magnitude_peak {I : Type} {t : Term I} (h : SmallTerm t) :
    (Growth fun x => (t.run x).natAbs) ∧ (Growth fun x => t.peak x) := by
  induction h with
  | input i =>
    have hm : Growth fun x : I → ℤ => (x i).natAbs := ⟨1,fun x B _ hx => by simpa using hx i⟩
    exact ⟨hm,Growth.signed hm⟩
  | literal z => exact ⟨growth_const z.natAbs,growth_const (signedBits z)⟩
  | @app op l r hop _ _ hl hr =>
    obtain ⟨c,hc⟩ := hop
    have hm : Growth fun x : I → ℤ => (op.apply (l.run x) (r.run x)).natAbs :=
      Growth.mono (Growth.pow (Growth.add (Growth.add hl.1 hr.1) (growth_const 2)) c) (fun _ => hc _ _)
    exact ⟨hm,Growth.max (Growth.signed hm) (Growth.max hl.2 hr.2)⟩

theorem SmallTerm.bound {I : Type} {t : Term I} (h : SmallTerm t) :
    ∃ c : ℕ, ∀ (x : I → ℤ) (B : ℕ), 2 ≤ B → (∀ i, (x i).natAbs ≤ B) →
      (t.run x).natAbs ≤ B^c ∧ t.peak x ≤ B^c := by
  obtain ⟨hm,hp⟩ := magnitude_peak h
  obtain ⟨c,hc⟩ := Growth.max hm hp
  exact ⟨c,fun x B hB hx => max_le_iff.mp (hc x B hB hx)⟩

theorem TameTerm.peak_le {I : Type} {t : Term I} (h : TameTerm t) :
    ∃ c : ℕ, ∀ (x : I → ℤ) (B : ℕ), 2 ≤ B → (∀ i, (x i).natAbs ≤ B) → t.peak x ≤ B^c := by
  change Growth _
  induction h with
  | small hs => exact (magnitude_peak hs).2
  | @app op l r hop _ _ hl hr =>
    obtain ⟨c,hc⟩ := hop
    have hb : Growth fun x : I → ℤ => signedBits (op.apply (l.run x) (r.run x)) :=
      Growth.mono (Growth.mul (growth_const c) (Growth.add (Growth.mono hl l.result_le_peak)
        (Growth.mono hr r.result_le_peak))) (fun _ => hc _ _)
    exact Growth.max hb (Growth.max hl hr)
  | @power op l r hop _ hs hl =>
    obtain ⟨c,hc⟩ := hop
    obtain ⟨hm,hr⟩ := magnitude_peak hs
    have hb : Growth fun x : I → ℤ => signedBits (op.apply (l.run x) (r.run x)) :=
      Growth.mono (Growth.mul (Growth.mul (growth_const c) (Growth.add hm (growth_const 1)))
        (Growth.mono hl l.result_le_peak)) (fun _ => hc _ _)
    exact Growth.max hb (Growth.max hl hr)

theorem peak_poly_of_tame {k : ℕ} {num den : Packing.IntegerTerm k}
    (hn : TameTerm num) (hd : TameTerm den) :
    ∃ c : ℕ, ∀ U, 0 < U → ∀ t : Fin k → Fin U,
      max (num.peak (Packing.termInputs t)) (den.peak (Packing.termInputs t)) ≤ (1+U)^c := by
  obtain ⟨c,hc⟩ := Growth.max hn.peak_le hd.peak_le
  refine ⟨c,fun U hU t => hc (Packing.termInputs t) (1+U) (by omega) ?_⟩
  intro i
  cases i with
  | none => change (U:ℤ).natAbs ≤ 1+U; simp
  | some i => have ht := (t i).isLt; change ((t i).val:ℤ).natAbs ≤ 1+U; simp only [Int.natAbs_natCast]; omega

private theorem magnitude_le_two_pow (z : ℤ) : z.natAbs ≤ 2^(signedBits z) :=
  Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (by dsimp [signedBits,bits]; omega))

private theorem signed_le_of_mag {z : ℤ} {h : ℕ} (hz : z.natAbs ≤ 2^h) :
    signedBits z ≤ h+2 := by
  by_cases h0 : z.natAbs = 0
  · simp [signedBits,bits,h0]
  · have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ((Nat.log2_self_le h0).trans hz)
    dsimp [signedBits,bits]
    omega

/-- A polynomial magnitude bound implies a linear bit bound for a fixed operation. -/
theorem ValueTame.bitTame {op : Operation} (hv : ValueTame op) : BitTame op := by
  obtain ⟨c,hc⟩ := hv
  refine ⟨c+1,fun a b => ?_⟩
  let M := max (signedBits a) (signedBits b)
  have ha := (magnitude_le_two_pow a).trans (Nat.pow_le_pow_right (by decide) (le_max_left _ (signedBits b)))
  have hb := (magnitude_le_two_pow b).trans (Nat.pow_le_pow_right (by decide) (le_max_right (signedBits a) _))
  have hM : M+2 ≤ signedBits a + signedBits b := by dsimp [M,signedBits,bits]; omega
  have hsum : a.natAbs+b.natAbs+2 ≤ 2^(signedBits a+signedBits b) := by
    apply le_trans _ (Nat.pow_le_pow_right (by decide) hM)
    change _ ≤ 2^(M+2)
    change a.natAbs ≤ 2^M at ha
    change b.natAbs ≤ 2^M at hb
    rw [pow_add]
    have := Nat.two_pow_pos M
    omega
  have hmag := (hc a b).trans (Nat.pow_le_pow_left hsum c)
  rw [← pow_mul] at hmag
  have hbits := signed_le_of_mag hmag
  rw [Nat.add_mul,one_mul,Nat.mul_comm c]
  have : 2 ≤ signedBits a := by dsimp [signedBits,bits]; omega
  omega

theorem valueTame_ofPolynomial (p : MvPolynomial Bool ℤ) : ValueTame (ofPolynomial p) := by
  obtain ⟨A,hA⟩ := Compiler.eval_magnitude_bound p
  refine ⟨3*A,fun a b => ?_⟩
  let B := a.natAbs + b.natAbs + 2
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hlog : 2^B.log2 ≤ B := Nat.log2_self_le (by omega)
  have hx (i : Bool) : (if i then b else a).natAbs ≤ 2^(B.log2+1) := by
    apply le_trans _ (Nat.lt_log2_self (n:=B)).le
    cases i <;> dsimp [B] <;> omega
  have hmag := hA (B.log2+1) (fun i : Bool => if i then b else a) hx
  have hb3 : 2^(B.log2+1+1) ≤ B^3 := by
    have h4 := Nat.pow_le_pow_left hB 2
    calc
      _ = 4 * 2^B.log2 := by rw [pow_succ,pow_succ]; omega
      _ ≤ B^2 * B := Nat.mul_le_mul h4 hlog
      _ = B^3 := by ring
  change (MvPolynomial.eval _ p).natAbs ≤ B^(3*A)
  apply hmag.trans
  rw [Nat.mul_comm A,pow_mul,pow_mul]
  exact Nat.pow_le_pow_left hb3 A

theorem bitTame_ofPolynomial (p : MvPolynomial Bool ℤ) : BitTame (ofPolynomial p) :=
  (valueTame_ofPolynomial p).bitTame

theorem valueTame_division : ValueTame divisionOperation := by
  refine ⟨1,fun a b => ?_⟩
  simp only [divisionOperation_apply,positiveDiv,pow_one]
  split
  · exact (Int.natAbs_ediv_le_natAbs a b).trans (by omega)
  · simp

theorem bitTame_division : BitTame divisionOperation := valueTame_division.bitTame

theorem powerTame_signedPower (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) :
    PowerTame (signedPower hc hq) := by
  refine ⟨1,fun a b => ?_⟩
  simp only [one_mul,signedPower_apply]
  have hab : b.toNat ≤ b.natAbs := by omega
  have hmag : (a^b.toNat).natAbs ≤ 2^(signedBits a*b.toNat) := by
    rw [Int.natAbs_pow,pow_mul]
    exact Nat.pow_le_pow_left (magnitude_le_two_pow a) b.toNat
  apply (signed_le_of_mag hmag).trans
  have hmul := Nat.mul_le_mul_right (signedBits a) hab
  have ha : 2 ≤ signedBits a := by dsimp [signedBits,bits]; omega
  rw [Nat.add_mul,one_mul,Nat.mul_comm (signedBits a) b.toNat]
  omega

namespace Logarithm

open MvPolynomial PowerTests Compiler
open PowerPolynomial (less leq eqn)

private abbrev Slots := Unit ⊕ PowerPolynomial.Witness
private abbrev Vars := Option Bool ⊕ Slots
private abbrev Poly := MvPolynomial Vars ℤ

private def arg : Poly := X (.inl (some false))
private def exponent : Poly := X (.inl none)
private def power : Poly := X (.inr (.inl ()))

private def powerEquation : Poly :=
  bind₁ (Sum.elim ![2,exponent,power] (fun i => X (.inr (.inr i)))) PowerPolynomial.polynomial

private def graph : Compiler.Formula Vars :=
  .either (.both (leq arg 1) (eqn exponent 0))
    (.both (leq 2 arg) (.both (.zero powerEquation)
      (.both (leq power arg) (less arg (2*power)))))

private theorem powerEquation_value (a b y : ℤ) (w : Slots → ℤ) :
    eval (Sum.elim (opInputs a b y) w) powerEquation =
      PowerPolynomial.value 2 y (w (.inl ())) (w ∘ Sum.inr) := by
  change eval₂Hom (RingHom.id ℤ) _ _ = _
  rw [powerEquation, eval₂Hom_bind₁]
  change eval _ _ = eval _ _
  congr 2
  funext i
  rcases i with i|i
  · fin_cases i <;> simp [exponent,power,opInputs]
  · simp

private theorem graph_iff (a b y : ℤ) (w : Slots → ℤ) :
    graph.Holds (Sum.elim (opInputs a b y) w) ↔
      (a ≤ 1 ∧ y = 0) ∨
      (2 ≤ a ∧ PowerPolynomial.value 2 y (w (.inl ())) (w ∘ Sum.inr) = 0 ∧
       w (.inl ()) ≤ a ∧ a < 2 * w (.inl ())) := by
  simp [graph, Formula.Holds, powerEquation_value, arg, exponent, power, opInputs]

private theorem log_small {a : ℤ} (h : a ≤ 1) : a.toNat.log2 = 0 := by
  have hm : a.toNat ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with h|h <;> rw [h] <;> decide

private theorem sound (hc : Cyclic) (hq : Quadratic) (a b y : ℤ) (w : Slots → ℤ)
    (h : graph.Holds (Sum.elim (opInputs a b y) w)) : y = (a.toNat.log2 : ℤ) := by
  rcases (graph_iff ..).1 h with ⟨ha,rfl⟩ | ⟨ha,hp,hl,hu⟩
  · simp [log_small ha]
  obtain ⟨g,n,hg,rfl,hw⟩ := (PowerPolynomial.exact_over_integers hc hq _ _ _).1 ⟨_,hp⟩
  have hg' : g = 2 := by omega
  subst g
  rw [hw] at hl hu
  have ha' := Int.toNat_of_nonneg (by omega : 0 ≤ a)
  have hlo : 2^n ≤ a.toNat := by omega
  have hhi : a.toNat < 2^(n+1) := by rw [pow_succ]; omega
  rw [(Nat.log2_eq_iff (by omega : a.toNat ≠ 0)).2 ⟨hlo,hhi⟩]

private theorem honest (hc : Cyclic) (hq : Quadratic) :
    ∃ K p : ℕ, ∀ a b : ℤ, ∃ w : Slots → ℤ,
      intCost w ≤ K*(signedBits a + signedBits b + signedBits (a.toNat.log2 : ℤ) + 2)^p ∧
      graph.Holds (Sum.elim (opInputs a b (a.toNat.log2 : ℤ)) w) := by
  obtain ⟨C,hC⟩ := PowerPolynomial.complete_quartic hc hq
  refine ⟨C+1,4,fun a b => ?_⟩
  let n := a.toNat.log2
  let B := signedBits a + signedBits b + signedBits (n:ℤ) + 2
  obtain ⟨u,hu,hcost⟩ := hC 2 n
  let w : Slots → ℤ := Sum.elim (fun _ => ((2^n:ℕ):ℤ)) u
  refine ⟨w,?_,?_⟩
  · have hna : n ≤ a.natAbs.log2 := by cases a <;> simp [n]
    have hnB : n+4 ≤ B := by dsimp [B,signedBits,bits]; omega
    have hbits : inputBits 2 n (2^n) ≤ n+4 := by
      have hn := Nat.lt_two_pow_self (n:=n)
      have hsum : 2+2+n+2^n < 2^(n+4) := by rw [pow_add]; norm_num; omega
      exact Nat.succ_le_of_lt ((Nat.log2_lt (by omega)).2 hsum)
    have haux := hcost.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (hbits.trans hnB) 4))
    have hpow : B ≤ B^4 := Nat.le_self_pow (by decide) _
    have hw : intCost w = n+2+intCost u := by
      simp [intCost,w,Fintype.sum_sum_type,bits,Nat.log2_two_pow,Nat.add_assoc]
    rw [hw]
    change _ ≤ (C+1)*B^4
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · apply (graph_iff ..).2
    by_cases ha : a ≤ 1
    · exact Or.inl ⟨ha,by simp [log_small ha]⟩
    have hapos : 0 ≤ a := by omega
    have ha' := Int.toNat_of_nonneg hapos
    have hlhu := (Nat.log2_eq_iff (by omega : a.toNat ≠ 0)).1 (rfl : a.toNat.log2 = n)
    change 2 ^ n ≤ a.toNat ∧ a.toNat < 2 ^ (n+1) at hlhu
    rw [pow_succ] at hlhu
    refine Or.inr ⟨by omega,?_,?_,?_⟩
    · exact hu
    · change (((2^n:ℕ):ℤ)) ≤ a
      omega
    · change a < 2 * (((2^n:ℕ):ℤ))
      omega

def operation (hc : Cyclic) (hq : Quadratic) : Operation :=
  Operation.ofShortFormula (fun a _ => (a.toNat.log2 : ℤ)) graph (sound hc hq) (honest hc hq)

end Logarithm

theorem exists_log2Operation (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) :
    ∃ op : Operation, (∀ a b : ℤ, op.apply a b = (a.toNat.log2 : ℤ)) ∧ ValueTame op := by
  refine ⟨Logarithm.operation hc hq, fun _ _ => rfl, 1, fun a b => ?_⟩
  change ((a.toNat.log2 : ℤ)).natAbs ≤ (a.natAbs + b.natAbs + 2)^1
  rw [pow_one,Int.natAbs_natCast]
  have h := Nat.log2_le_self a.toNat
  cases a <;> simp_all
  omega

end
end DiophantineNP.Blueprint
