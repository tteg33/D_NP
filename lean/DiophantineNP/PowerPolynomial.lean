import DiophantineNP.StepCompiler
import DiophantineNP.IntegerPower

/-! # One fixed polynomial for the integer power graph

The equation includes the two elliptic windows, the two Pell tests and the
zero/one-base branches. The two external arithmetic hypotheses explicitly
name the rational generator and canonical-height quadraticity for curve 37a1.
-/

namespace DiophantineNP.PowerPolynomial

open MvPolynomial Compiler PowerTests

noncomputable section

local infixr:35 " ⋏ " => Compiler.Formula.both
local infixr:30 " ⋎ " => Compiler.Formula.either

abbrev Registers := (Fin 10 ⊕ Fin 10) ⊕ Fin 5
abbrev Variables := Fin 3 ⊕ Registers

private def in₁ (i : Fin 10) : Registers := .inl (.inl i)
private def in₂ (i : Fin 10) : Registers := .inl (.inr i)
private def in₃ (i : Fin 5) : Registers := .inr i

private def unpack (w : Registers → ℤ) : IntegerTrace :=
  ⟨unpackStep (w ∘ in₁), unpackStep (w ∘ in₂), w (in₃ 0), w (in₃ 1), w (in₃ 2),
    w (in₃ 3), w (in₃ 4)⟩

private def inputs (g e y : ℕ) : Fin 3 → ℤ := ![(g:ℤ),e,y]

variable {σ : Type*}

private def window (c : Fin 10 → Poly σ) (V : Poly σ) : Formula σ :=
  stepGate c ⋏ leq (V*c 8) (c 9) ⋏ leq (c 9) (V^2*c 8)

private theorem window_iff (x : σ → ℤ) (c : Fin 10 → Poly σ) (V : Poly σ) (v : ℕ)
    (hV : eval x V = v) : (window c V).Holds x ↔
      let a := fun i => eval x (c i)
      StepSpec a ∧ (unpackStep a).Window v := by
  simp only [window, Formula.Holds, stepGate_iff, holds_leq, map_mul, map_pow, hV]
  constructor
  · rintro ⟨hs,hl,hu⟩
    obtain ⟨hv,ha,hb⟩ := decode_step hs
    rw [ha,hb] at hl hu
    exact ⟨hs,hv,by exact_mod_cast hl,by exact_mod_cast hu⟩
  · rintro ⟨hs,_,hl,hu⟩
    obtain ⟨_,ha,hb⟩ := decode_step hs
    rw [ha,hb]
    exact ⟨hs,by exact_mod_cast hl,by exact_mod_cast hu⟩

private def pellGate (C s t : Poly σ) : Formula σ :=
  leq 0 s ⋏ less s t ⋏ eqn (s^2-C*s*t+t^2) 1

private theorem pellGate_iff (x : σ → ℤ) (C s t : Poly σ) :
    (pellGate C s t).Holds x ↔ Pell.Admissible (eval x C) (eval x s) (eval x t) := by
  simp [pellGate, Formula.Holds, Pell.Admissible]

private def congruent (m a b : Poly σ) : Formula σ := .divides m (b-a)

private theorem congruent_iff (x : σ → ℤ) (m a b : Poly σ) :
    (congruent m a b).Holds x ↔ (eval x a) ≡ (eval x b) [ZMOD (eval x m)] := by
  simp [congruent, Formula.Holds, Int.modEq_iff_dvd]

private def smallGate (g e y : Poly σ) : Formula σ :=
  (eqn g 1 ⋏ eqn y 1) ⋎ (eqn g 0 ⋏ ((eqn e 0 ⋏ eqn y 1) ⋎ (less 0 e ⋏ eqn y 0)))

private def mainGate (g e y : Poly σ) (a b : Fin 10 → Poly σ) (p : Fin 5 → Poly σ) : Formula σ :=
  let T := g+e+y+2^1024
  let C := T+5
  let A := p 2
  leq 2 g ⋏ window a T ⋏ window b (a 8) ⋏ pellGate C (p 0) (p 1) ⋏
    congruent (C-2) (p 0) e ⋏ eqn A (p 1+g^2+y+T+10) ⋏ pellGate A (p 3) (p 4) ⋏
    congruent (A-2) (p 3) e ⋏ congruent (A*g-g^2-1) y (p 4+(g-A)*p 3) ⋏ leq (p 4) (b 8)

private def basic (i : Fin 3) : Poly Variables := X (.inl i)
private def reg (i : Registers) : Poly Variables := X (.inr i)

def formula : Formula Variables :=
  leq 0 (basic 0) ⋏ leq 0 (basic 1) ⋏ leq 0 (basic 2) ⋏
  (smallGate (basic 0) (basic 1) (basic 2) ⋎
   mainGate (basic 0) (basic 1) (basic 2) (reg ∘ in₁) (reg ∘ in₂) (reg ∘ in₃))

private theorem main_iff (g e y : ℕ) (w : Registers → ℤ) :
    (mainGate (basic 0) (basic 1) (basic 2) (reg ∘ in₁) (reg ∘ in₂) (reg ∘ in₃)).Holds
      (Sum.elim (inputs g e y) w) ↔
    StepSpec (w ∘ in₁) ∧ StepSpec (w ∘ in₂) ∧ IntegerMain g e y (unpack w) := by
  let x := Sum.elim (inputs g e y) w
  let T : Poly Variables := basic 0+basic 1+basic 2+2^1024
  have hT : eval x T = (total g e y : ℤ) := by
    simp only [T,x,basic,total,map_add,map_pow,eval_X,map_ofNat,Sum.elim_inl, Nat.cast_add, Nat.cast_pow,Nat.cast_ofNat]
    rfl
  have hg : eval x (basic 0) = g := by simp [x,basic,inputs]
  have he : eval x (basic 1) = e := by simp [x,basic,inputs]
  have hy : eval x (basic 2) = y := by simp [x,basic,inputs]
  have hr (i : Registers) : eval x (reg i) = w i := by simp [x,reg]
  have eval₁ : (fun i => eval x ((reg ∘ in₁) i)) = w ∘ in₁ := funext (fun i => hr _)
  have eval₂ : (fun i => eval x ((reg ∘ in₂) i)) = w ∘ in₂ := funext (fun i => hr _)
  have h₁ := window_iff x (reg ∘ in₁) T (total g e y) hT
  rw [eval₁] at h₁
  have h₂ (hs : StepSpec (w ∘ in₁)) :=
    window_iff x (reg ∘ in₂) ((reg ∘ in₁) 8) (unpackStep (w ∘ in₁)).start
      ((hr _).trans (decode_step hs).2.1)
  change (mainGate ..).Holds x ↔ _
  simp only [mainGate, Formula.Holds, holds_leq, holds_eqn, pellGate_iff, congruent_iff]
  change (_ ∧ (window (reg ∘ in₁) T).Holds x ∧ _ ∧ _) ↔ _
  rw [h₁]
  simp only [Function.comp_apply, map_sub, map_one, map_add, map_mul, map_pow, map_ofNat,
    hg, he, hy, hr]
  constructor
  · rintro ⟨bg,⟨hs,wa⟩,wb,rest⟩
    obtain ⟨ht,wb'⟩ := (h₂ hs).1 wb
    rw [eval₂] at ht wb'
    obtain ⟨v,u,a,p,m,c,t⟩ := rest
    refine ⟨hs,ht,by exact_mod_cast bg,wa,wb',?_,?_,?_,p,m,c,?_⟩
    · simpa only [total, Nat.cast_add, Nat.cast_pow,Nat.cast_ofNat,unpack] using v
    · simpa only [total, Nat.cast_add, Nat.cast_pow,Nat.cast_ofNat,unpack] using u
    · simpa only [total, Nat.cast_add, Nat.cast_pow,Nat.cast_ofNat,unpack] using a
    · exact t.trans_eq (decode_step ht).2.1
  · rintro ⟨hs,ht,bg,wa,wb,v,u,a,p,m,c,t⟩
    refine ⟨by exact_mod_cast bg,(And.intro hs wa), (h₂ hs).2 ?_,?_,?_,?_,p,m,c,?_⟩
    · rw [eval₂]; exact ⟨ht,wb⟩
    · simpa only [total, Nat.cast_add, Nat.cast_pow,Nat.cast_ofNat,unpack] using v
    · simpa only [total, Nat.cast_add, Nat.cast_pow,Nat.cast_ofNat,unpack] using u
    · simpa only [total, Nat.cast_add, Nat.cast_pow,Nat.cast_ofNat,unpack] using a
    · exact t.trans_eq (decode_step ht).2.1.symm

private theorem holds_iff (g e y : ℕ) (w : Registers → ℤ) :
    formula.Holds (Sum.elim (inputs g e y) w) ↔
    Small g e y ∨ (StepSpec (w ∘ in₁) ∧ StepSpec (w ∘ in₂) ∧ IntegerMain g e y (unpack w)) := by
  rw [formula,Formula.Holds,Formula.Holds,Formula.Holds,Formula.Holds,main_iff]
  simp [smallGate,Formula.Holds,basic,inputs,PowerTests.Small]

private theorem register_sound (hc : Cyclic) (hq : Quadratic) {g e y : ℕ} (w : Registers → ℤ)
    (hw : formula.Holds (Sum.elim (inputs g e y) w)) : y = g^e := by
  rcases (holds_iff g e y w).1 hw with h | ⟨_,_,h⟩
  · exact integer_sound hc hq (w := unpack w) (Or.inl h)
  · exact integer_sound hc hq (Or.inr h)

private theorem size_le {w : Step} {B : ℕ} (h : w.Bounded B) : stepSize w ≤ B := by
  rcases h with ⟨h₁,h₂,h₃⟩
  exact max_le (max_le h₁ h₃) h₂

private theorem registers_complete (hc : Cyclic) (hq : Quadratic) (g e : ℕ) :
    ∃ w : Registers → ℤ, formula.Holds (Sum.elim (inputs g e (g^e)) w) ∧
      ∀ i, (w i).natAbs ≤ 2^(budget (total g e (g^e))) := by
  obtain ⟨t,ht,ha,hb,hp⟩ := integer_complete hc hq g e
  rcases ht with h | h
  · refine ⟨fun _ => 0, (holds_iff ..).2 (Or.inl h), fun _ => Nat.zero_le _⟩
  obtain ⟨a,ha',hea,hba⟩ := encode_step t.first h.2.1.1
  obtain ⟨b,hb',heb,hbb⟩ := encode_step t.second h.2.2.1.1
  let p : Fin 5 → ℤ := ![t.s₀,t.t₀,t.A,t.s,t.t]
  let w : Registers → ℤ := Sum.elim (Sum.elim a b) p
  have huw : unpack w = t := by cases t; simp_all [unpack,w,p,Function.comp_def,in₁,in₂,in₃]
  refine ⟨w,(holds_iff ..).2 (Or.inr ⟨ha',hb',huw ▸ h⟩),?_⟩
  rintro ((i|i)|i)
  · exact (hba i).trans (size_le ha)
  · exact (hbb i).trans (size_le hb)
  · apply hp
    fin_cases i <;> simp [w,p]

/-- The same finite witness type is used for every base, exponent and output. -/
abbrev GateWitness := formula.Aux
noncomputable instance : Fintype GateWitness := Fintype.ofFinite _
abbrev Witness := Registers ⊕ GateWitness

private def gateSlots : Formula σ → ℕ
  | .zero _ => 0
  | .nonnegative _ => 4
  | .divides _ _ => 1
  | .both f g | .either f g => gateSlots f + gateSlots g

private theorem card_aux (f : Formula σ) : Nat.card f.Aux = gateSlots f := by
  induction f with
  | zero _ => simp [Formula.Aux,gateSlots]
  | nonnegative _ => simp [Formula.Aux,gateSlots]
  | divides _ _ => simp [Formula.Aux,gateSlots]
  | both f g hf hg => simp only [Formula.Aux,gateSlots,Nat.card_sum,hf,hg]
  | either f g hf hg => simp only [Formula.Aux,gateSlots,Nat.card_sum,hf,hg]

/-- Twenty-five primary registers and 167 arithmetic-gate witness slots. -/
theorem witness_arity : Fintype.card Witness = 192 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (Registers ⊕ formula.Aux) = _
  rw [Nat.card_sum, card_aux]
  have : gateSlots formula = 167 := rfl
  rw [this]
  simp [Registers]

/-- The three native inputs are ordered base, exponent, output. -/
def polynomial : MvPolynomial (Fin 3 ⊕ Witness) ℤ :=
  rename (Equiv.sumAssoc (Fin 3) Registers GateWitness) formula.compile

def value (g e y : ℤ) (w : Witness → ℤ) : ℤ :=
  eval (Sum.elim ![g,e,y] w) polynomial

private theorem value_eq (g e y : ℤ) (w : Witness → ℤ) :
    value g e y w = eval (Sum.elim (Sum.elim ![g,e,y] (w ∘ Sum.inl)) (w ∘ Sum.inr)) formula.compile := by
  rw [value,polynomial,eval_rename]
  congr 2
  funext i
  rcases i with (i|i)|i <;> rfl

private theorem formula_of_zero {g e y : ℤ} {w : Witness → ℤ} (hw : value g e y w = 0) :
    formula.Holds (Sum.elim ![g,e,y] (w ∘ Sum.inl)) :=
  (formula.compile_exact _).1 ⟨w ∘ Sum.inr, (value_eq ..).symm.trans hw⟩

/-- A satisfying assignment of any size returns the intended power. -/
theorem sound (hc : Cyclic) (hq : Quadratic) (g e y : ℕ) (w : Witness → ℤ)
    (hw : value g e y w = 0) : y = g^e :=
  register_sound hc hq (w ∘ Sum.inl) (formula_of_zero hw)

private theorem bits_mono {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b := by
  unfold bits
  apply Nat.add_le_add_right
  by_cases ha : a = 0
  · simp [ha]
  · exact (Nat.le_log2 (by omega : b ≠ 0)).2 ((Nat.log2_self_le ha).trans h)

private theorem bits_of_mag {a k : ℕ} (h : a ≤ 2^k) : bits a ≤ k+1 := by
  simpa [bits, Nat.log2_two_pow] using bits_mono h

private theorem register_cost {τ : Type} [Fintype τ] (w : τ → ℤ) (h : ℕ) (hb : ∀ i, bits (w i).natAbs ≤ h) :
    intCost w ≤ Fintype.card τ*(h+1) := by
  unfold intCost
  calc _ ≤ ∑ _ : τ, (h+1) := by
          apply Finset.sum_le_sum
          exact fun i _ => Nat.add_le_add_right (hb i) 1
       _ = _ := by simp

/-- Every true input has a witness for this same polynomial. Its *total*
signed bit cost is quartic in `1 + floor(log₂(2+g+e+y))`. -/
theorem complete_quartic (hc : Cyclic) (hq : Quadratic) :
    ∃ K : ℕ, ∀ g e : ℕ, ∃ w : Witness → ℤ, value g e (g^e : ℕ) w = 0 ∧
      intCost w ≤ K*(inputBits g e (g^e))^4 := by
  obtain ⟨A,hA⟩ := formula.compile_linear_cost
  let D : ℕ := 5+3*45^3*1025^4
  refine ⟨(Fintype.card Registers+A)*(D+3), fun g e => ?_⟩
  let y := g^e
  let I := inputBits g e y
  let B := budget (total g e y)
  let h := B+I+1
  obtain ⟨w,hw,hb⟩ := registers_complete hc hq g e
  have hb' (i) : bits (w i).natAbs ≤ h := (bits_of_mag (hb i)).trans (by dsimp [h,B,y]; omega)
  have hinput (i : Fin 3) : bits ((inputs g e y i).natAbs) ≤ I := by
    fin_cases i <;> apply bits_mono
    · change g ≤ 2+g+e+y; omega
    · change e ≤ 2+g+e+y; omega
    · change y ≤ 2+g+e+y; omega
  have hx : ∀ i, bits ((Sum.elim (inputs g e y) w i).natAbs) ≤ h := by
    rintro (i|i)
    · exact (hinput i).trans (by dsimp [h]; omega)
    · exact hb' i
  obtain ⟨z,hz,hcost⟩ := hA h _ hx hw
  refine ⟨Sum.elim w z, ?_, ?_⟩
  · rw [value_eq]; exact hz
  · have hsum : intCost (Sum.elim w z) = intCost w + intCost z := by simp [intCost,Fintype.sum_sum_type]
    rw [hsum]
    have hlen := budget_input_bits g e y
    change B ≤ D*I^4 at hlen
    have hi : 1 ≤ I := by dsimp [I,inputBits]; omega
    have hpos : 1 ≤ I^4 := Nat.one_le_pow _ _ hi
    have hi4 : I ≤ I^4 := Nat.le_self_pow (by decide : 4 ≠ 0) _
    have htotal : h+1 ≤ (D+3)*I^4 := by
      dsimp [h]; rw [Nat.add_mul]; omega
    calc
      _ ≤ Fintype.card Registers*(h+1)+A*(h+1) := Nat.add_le_add (register_cost w h hb') hcost
      _ = (Fintype.card Registers+A)*(h+1) := (Nat.add_mul ..).symm
      _ ≤ (Fintype.card Registers+A)*((D+3)*I^4) := Nat.mul_le_mul_left _ htotal
      _ = _ := (Nat.mul_assoc ..).symm

/-- Exact over all signed inputs. Any zero forces a nonnegative base, exponent
and output; the converse includes `0^0=1` by Lean's natural-power convention. -/
theorem exact_over_integers (hc : Cyclic) (hq : Quadratic) (g e y : ℤ) :
    (∃ w, value g e y w = 0) ↔
    ∃ a n : ℕ, g = (a:ℤ) ∧ e = (n:ℤ) ∧ y = ((a^n:ℕ):ℤ) := by
  constructor
  · rintro ⟨w,hw⟩
    have hh := formula_of_zero hw
    obtain ⟨hg,he,hy,_⟩ := hh
    have hge : 0 ≤ g := by simpa [leq,Formula.Holds,basic] using hg
    have hee : 0 ≤ e := by simpa [leq,Formula.Holds,basic] using he
    have hye : 0 ≤ y := by simpa [leq,Formula.Holds,basic] using hy
    obtain ⟨a,rfl⟩ : ∃ a : ℕ, (a:ℤ) = g := ⟨_,Int.toNat_of_nonneg hge⟩
    obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n:ℤ) = e := ⟨_,Int.toNat_of_nonneg hee⟩
    obtain ⟨b,rfl⟩ : ∃ b : ℕ, (b:ℤ) = y := ⟨_,Int.toNat_of_nonneg hye⟩
    exact ⟨a,n,rfl,rfl,by exact_mod_cast sound hc hq a n b w hw⟩
  · rintro ⟨a,n,rfl,rfl,rfl⟩
    obtain ⟨_,h⟩ := complete_quartic hc hq
    obtain ⟨w,hw,_⟩ := h a n
    exact ⟨w,hw⟩

end
end DiophantineNP.PowerPolynomial
