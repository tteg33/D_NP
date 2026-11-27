import DiophantineNP.EvaluatorNodes

/-! # Uniform programs for input-dependent families -/

namespace DiophantineNP.Blueprint
open LaurentBounds ScalarProgram ScalarProjection FormulaLaurent
open scoped BigOperators
noncomputable section

abbrev Family (k : ℕ) (α : Type) := (U : ℕ) → (Fin k → Fin U) → α
def NatCode (k : ℕ) (a : Family k ℕ) : Prop :=
  ∃ p : Packing.IntegerTerm k, SmallTerm p ∧ ∀ U t, 0 < U → p.run (Packing.termInputs t) = (a U t : ℤ)
def RatCode (k : ℕ) (a : Family k ℚ) : Prop :=
  ∃ p q : Packing.IntegerTerm k, TameTerm p ∧ TameTerm q ∧ ∀ U t, 0 < U →
    0 < q.run (Packing.termInputs t) ∧ (p.run (Packing.termInputs t) : ℚ) / (q.run (Packing.termInputs t) : ℚ) = a U t
def ExprCode (k d : ℕ) (a : Family k (Expr d)) : Prop :=
  ∃ e : ((Option (Fin k)) → ℤ) → Expr d,
    Nonempty (Evaluated (Option (Fin k)) d (ValidInput k) e) ∧
    ∀ U t, 0 < U → ScalarEquiv U (e (Packing.termInputs t)) (a U t)

open ConcreteGrid

namespace RatCode
variable {k : ℕ} {a b : Family k ℚ}

theorem literal (q : ℚ) : RatCode k (fun _ _ => q) := by
  refine ⟨.literal q.num, .literal q.den, .small (.literal _), .small (.literal _), ?_⟩
  intro U t _
  simp only [Arith.run_lit]
  exact ⟨by exact_mod_cast q.den_pos, by simpa using (Rat.num_div_den q)⟩

theorem ofNat {a : Family k ℕ} (ha : NatCode k a) : RatCode k (fun U t => (a U t : ℚ)) := by
  obtain ⟨p, hp, hv⟩ := ha
  refine ⟨p, .literal 1, .small hp, .small (.literal 1), ?_⟩
  intro U t hU
  simp [hv U t hU]

theorem neg (ha : RatCode k a) : RatCode k (fun U t => -a U t) := by
  obtain ⟨p,q,hp,hq,h⟩ := ha
  refine ⟨Arith.sub (.literal 0) p, q, Arith.tame_sub (.small (.literal 0)) hp, hq, ?_⟩
  intro U t hU
  have hv := h U t hU
  exact ⟨hv.1, by simp [← hv.2, neg_div]⟩

theorem mul (ha : RatCode k a) (hb : RatCode k b) : RatCode k (fun U t => a U t * b U t) := by
  obtain ⟨p,q,hp,hq,h⟩ := ha
  obtain ⟨v,w,hv,hw,g⟩ := hb
  refine ⟨Arith.mul p v, Arith.mul q w, Arith.tame_mul hp hv, Arith.tame_mul hq hw, ?_⟩
  intro U t hU
  obtain ⟨hpos,hval⟩ := h U t hU
  obtain ⟨gpos,gval⟩ := g U t hU
  exact ⟨by simpa using mul_pos hpos gpos, by simp [← hval, ← gval, div_mul_div_comm]⟩

theorem add (ha : RatCode k a) (hb : RatCode k b) : RatCode k (fun U t => a U t + b U t) := by
  obtain ⟨p,q,hp,hq,h⟩ := ha
  obtain ⟨v,w,hv,hw,g⟩ := hb
  refine ⟨Arith.add (Arith.mul p w) (Arith.mul v q), Arith.mul q w,
    Arith.tame_add (Arith.tame_mul hp hw) (Arith.tame_mul hv hq), Arith.tame_mul hq hw, ?_⟩
  intro U t hU
  obtain ⟨hpos,hval⟩ := h U t hU
  obtain ⟨gpos,gval⟩ := g U t hU
  refine ⟨by simpa using mul_pos hpos gpos, ?_⟩
  simp only [Arith.run_add, Arith.run_mul, Int.cast_add, Int.cast_mul, ← hval, ← gval]
  rw [div_add_div _ _ (by exact_mod_cast hpos.ne') (by exact_mod_cast gpos.ne')]
  ring

theorem divPos (ha : RatCode k a) (hb : RatCode k b) (pos : ∀ U t, 0 < U → 0 < b U t) :
    RatCode k (fun U t => a U t / b U t) := by
  obtain ⟨p,q,hp,hq,h⟩ := ha
  obtain ⟨v,w,hv,hw,g⟩ := hb
  refine ⟨Arith.mul p w, Arith.mul q v, Arith.tame_mul hp hw, Arith.tame_mul hq hv, ?_⟩
  intro U t hU
  obtain ⟨hpos,hval⟩ := h U t hU
  obtain ⟨gpos,gval⟩ := g U t hU
  have hpos' := pos U t hU
  rw [← gval] at hpos'
  have hvp : 0 < v.run (Packing.termInputs t) := by
    exact_mod_cast ((div_pos_iff_of_pos_right (by exact_mod_cast gpos)).mp hpos')
  exact ⟨by simpa using mul_pos hpos hvp, by simp [← hval, ← gval, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]⟩

theorem pow (ha : RatCode k a) (n : ℕ) : RatCode k (fun U t => (a U t)^n) := by
  obtain ⟨p,q,hp,hq,h⟩ := ha
  refine ⟨Arith.fixedPow p n, Arith.fixedPow q n, Arith.tame_fixedPow hp n, Arith.tame_fixedPow hq n, ?_⟩
  intro U t hU
  obtain ⟨hpos,hval⟩ := h U t hU
  exact ⟨by simpa using pow_pos hpos n, by simp [← hval, div_pow]⟩
end RatCode

namespace ExprCode
variable {k d : ℕ} {f g : Family k (Expr d)} {a b : Family k ℕ}

theorem const {r : Family k ℚ} (hr : RatCode k r) : ExprCode k d (fun U t => rational (r U t)) := by
  obtain ⟨p,q,hp,hq,h⟩ := hr
  have pos : ∀ ι, ValidInput k ι → 0 < q.run ι := by
    rintro _ ⟨U,t,hU,rfl⟩; exact (h U t hU).1
  refine ⟨_, ⟨Evaluated.scalar p q hp hq pos⟩, ?_⟩
  intro U t hU
  apply ScalarEquiv.scalar
  obtain ⟨hq,hval⟩ := h U t hU
  rw [PNat.toPNat'_coe (by omega), ← Int.cast_natCast, Int.toNat_of_nonneg hq.le, hval]
  simpa using (Rat.num_div_den (r U t)).symm

theorem monomial (v : Fin d → ℤ) : ExprCode k d (fun _ _ => .monomial v) :=
  ⟨_, ⟨Evaluated.monomial v⟩, fun _ _ _ => .monomial _⟩

theorem add (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (hf : ExprCode k d f)
    (hg : ExprCode k d g) : ExprCode k d (fun U t => (f U t).add (g U t)) := by
  obtain ⟨_,⟨E⟩,h⟩ := hf
  obtain ⟨_,⟨F⟩,i⟩ := hg
  exact ⟨_, ⟨E.add hc hq F⟩, fun U t hU => .add (h U t hU) (i U t hU)⟩

theorem neg (hf : ExprCode k d f) : ExprCode k d (fun U t => (f U t).neg) := by
  obtain ⟨_,⟨E⟩,h⟩ := hf
  exact ⟨_, ⟨E.neg⟩, fun U t hU => .neg (h U t hU)⟩

theorem mul (hf : ExprCode k d f) (hg : ExprCode k d g) : ExprCode k d (fun U t => (f U t).mul (g U t)) := by
  obtain ⟨_,⟨E⟩,h⟩ := hf
  obtain ⟨_,⟨F⟩,i⟩ := hg
  exact ⟨_, ⟨E.mul F⟩, fun U t hU => .mul (h U t hU) (i U t hU)⟩

theorem pow (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (hf : ExprCode k d f)
    (hn : NatCode k a) : ExprCode k d (fun U t => (f U t).pow (a U t)) := by
  obtain ⟨_,⟨E⟩,h⟩ := hf
  obtain ⟨p,hp,hv⟩ := hn
  have pos : ∀ ι, ValidInput k ι → 0 ≤ p.run ι := by
    rintro _ ⟨U,t,hU,rfl⟩; rw [hv U t hU]; positivity
  refine ⟨_, ⟨E.pow hc hq p hp pos⟩, ?_⟩
  intro U t hU
  dsimp only
  simp only [hv U t hU, Int.toNat_natCast]
  exact .pow _ (h U t hU)

theorem threshold (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (hf : ExprCode k d f)
    (hn : NatCode k a) (hb : NatCode k b) (range : ∀ U t, 0 < U → b U t ≤ a U t + 1) :
    ExprCode k d (fun U t => (f U t).threshold (a U t) (b U t)) := by
  obtain ⟨_,⟨E⟩,h⟩ := hf
  obtain ⟨p,hp,hv⟩ := hn
  obtain ⟨q,hq',hw⟩ := hb
  refine ⟨_, ⟨E.threshold hc hq p q hp hq' ?_⟩, ?_⟩
  · rintro _ ⟨U,t,hU,rfl⟩
    rw [hv U t hU, hw U t hU]
    exact ⟨by positivity, by positivity, by exact_mod_cast range U t hU⟩
  · intro U t hU
    dsimp only
    simp only [hv U t hU, hw U t hU, Int.toNat_natCast]
    exact .threshold _ _ (h U t hU)

theorem geometric (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (j : Fin d)
    (hs : NatCode k a) (hJ : NatCode k b) : ExprCode k d (fun U t => .geometric j (a U t) (b U t)) := by
  obtain ⟨p,hp,hv⟩ := hs
  obtain ⟨q,hq',hw⟩ := hJ
  refine ⟨_, ⟨Evaluated.geometric hc hq j p q hp hq' ?_⟩, ?_⟩
  · rintro _ ⟨U,t,hU,rfl⟩
    rw [hv U t hU, hw U t hU]; exact ⟨by positivity, by positivity⟩
  · intro U t hU
    dsimp only
    simp only [hv U t hU, hw U t hU, Int.toNat_natCast]
    exact .geometric _ _ _

theorem project (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (hf : ExprCode k d f)
    (j : Fin d) (hs : NatCode k (fun U _ => size U)) :
    ExprCode k d (fun U t => (f U t).project j (period U)) := by
  obtain ⟨_,⟨E⟩,h⟩ := hf
  obtain ⟨p,hp,hv⟩ := hs
  have pos : ∀ ι, ValidInput k ι → 0 < p.run ι := by
    rintro _ ⟨U,t,hU,rfl⟩
    rw [hv U t hU]; exact_mod_cast (period U).property
  refine ⟨_, ⟨E.project hc hq j p hp pos⟩, ?_⟩
  intro U t hU
  dsimp only
  rw [hv U t hU]
  simp only [Int.toNat_natCast]
  have eq : (size U).toPNat' = period U := by
    apply Subtype.ext
    exact PNat.toPNat'_coe (period U).property
  rw [eq]
  exact .project _ (h U t hU)
end ExprCode

end
end DiophantineNP.Blueprint
