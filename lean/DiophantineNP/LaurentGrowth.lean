import DiophantineNP.LaurentBounds

/-! # Polynomial bit growth for fixed Laurent expression trees

The parameterized family fixes the syntax before choosing `U`. Values of power
and threshold exponents must be polynomial in `U`. Rational constants and
monomial exponents have the size hypotheses used in the manuscript.
-/

namespace DiophantineNP.LaurentBounds

noncomputable section

/-- A numerical value is bounded by one fixed power of the input size. -/
def Poly (f : ℕ → ℕ) : Prop := ∃ c : ℕ, ∀ u, f u ≤ (u+2)^c

/-- A natural number has polynomial bit length. -/
def PolyBits (f : ℕ → ℕ) : Prop := ∃ e : ℕ → ℕ, Poly e ∧ ∀ u, f u ≤ 2^(e u)

lemma Poly.mono {f g : ℕ → ℕ} (hg : Poly g) (h : ∀ u, f u ≤ g u) : Poly f := by
  obtain ⟨c, hc⟩ := hg
  exact ⟨c, fun u => (h u).trans (hc u)⟩

lemma poly_const (a : ℕ) : Poly (fun _ => a) :=
  ⟨a, fun u => (Nat.lt_two_pow_self (n := a)).le.trans (Nat.pow_le_pow_left (by omega) a)⟩

lemma Poly.mul {f g : ℕ → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun u => f u * g u) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨k, hk⟩ := hg
  exact ⟨c+k, fun u => (Nat.mul_le_mul (hc u) (hk u)).trans_eq (pow_add _ _ _).symm⟩

lemma Poly.add {f g : ℕ → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun u => f u + g u) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨k, hk⟩ := hg
  refine ⟨c+k+1, fun u => ?_⟩
  have A := (hc u).trans (Nat.pow_le_pow_right (by omega : 0 < u+2) (by omega : c ≤ c+k))
  have B := (hk u).trans (Nat.pow_le_pow_right (by omega : 0 < u+2) (by omega : k ≤ c+k))
  rw [pow_succ]
  nlinarith [Nat.mul_le_mul_left ((u+2)^(c+k)) (show 2 ≤ u+2 by omega)]

lemma PolyBits.mono {f g : ℕ → ℕ} (hg : PolyBits g) (h : ∀ u, f u ≤ g u) : PolyBits f := by
  obtain ⟨e, he, hb⟩ := hg
  exact ⟨e, he, fun u => (h u).trans (hb u)⟩

lemma polyBits_const (a : ℕ) : PolyBits (fun _ => a) :=
  ⟨fun _ => a, poly_const a, fun _ => (Nat.lt_two_pow_self (n := a)).le⟩

lemma PolyBits.mul {f g : ℕ → ℕ} (hf : PolyBits f) (hg : PolyBits g) :
    PolyBits (fun u => f u * g u) := by
  obtain ⟨e, he, h⟩ := hf
  obtain ⟨e', he', h'⟩ := hg
  exact ⟨_, he.add he', fun u => (Nat.mul_le_mul (h u) (h' u)).trans_eq (pow_add _ _ _).symm⟩

lemma PolyBits.add {f g : ℕ → ℕ} (hf : PolyBits f) (hg : PolyBits g) :
    PolyBits (fun u => f u + g u) := by
  obtain ⟨e, he, h⟩ := hf
  obtain ⟨e', he', h'⟩ := hg
  refine ⟨fun u => e u + e' u + 1, (he.add he').add (poly_const 1), fun u => ?_⟩
  have A := (h u).trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : e u ≤ e u+e' u))
  have B := (h' u).trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : e' u ≤ e u+e' u))
  change f u + g u ≤ _
  rw [pow_succ]
  omega

lemma PolyBits.pow {f n : ℕ → ℕ} (hf : PolyBits f) (hn : Poly n) :
    PolyBits (fun u => (f u)^(n u)) := by
  obtain ⟨e, he, h⟩ := hf
  exact ⟨_, he.mul hn, fun u => (Nat.pow_le_pow_left (h u) (n u)).trans_eq (pow_mul _ _ _).symm⟩

lemma PolyBits.log2 {f : ℕ → ℕ} (hf : PolyBits f) : Poly (fun u => (f u).log2) := by
  obtain ⟨e, he, h⟩ := hf
  apply he.mono
  intro u
  by_cases hz : f u = 0
  · simp [hz]
  · exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ((Nat.log2_self_le hz).trans (h u))

/-- The hypotheses on numerical parameters of a tree of fixed shape. -/
inductive Admissible {d : ℕ} : (ℕ → Expr d) → Prop where
  | scalar (p : ℕ → ℤ) (q : ℕ → ℕ+) (hp : PolyBits (fun u => (p u).natAbs))
      (hq : PolyBits (fun u => q u)) : Admissible (fun u => .scalar (p u) (q u))
  | monomial (v : ℕ → Fin d → ℤ)
      (hv : Poly (fun u => Finset.univ.sup fun j => (v u j).natAbs)) :
      Admissible (fun u => .monomial (v u))
  | geometric (j : Fin d) (stride J : ℕ → ℕ) (hs : Poly stride) (hJ : Poly J) :
      Admissible (fun u => .geometric j (stride u) (J u))
  | add {f g} (hf : Admissible f) (hg : Admissible g) : Admissible (fun u => (f u).add (g u))
  | neg {f} (hf : Admissible f) : Admissible (fun u => (f u).neg)
  | mul {f g} (hf : Admissible f) (hg : Admissible g) : Admissible (fun u => (f u).mul (g u))
  | pow {f} (hf : Admissible f) (n : ℕ → ℕ) (hn : Poly n) : Admissible (fun u => (f u).pow (n u))
  | threshold {f} (hf : Admissible f) (n k : ℕ → ℕ) (hn : Poly n) :
      Admissible (fun u => (f u).threshold (n u) (k u))
  | project {f} (hf : Admissible f) (j : Fin d) (period : ℕ → ℕ+) :
      Admissible (fun u => (f u).project j (period u))

/-- The radius has polynomial *value*. The denominator and coefficient budget
have polynomial *bit length*. Each exponent depends only on the fixed family. -/
theorem Admissible.bounds {d : ℕ} {f : ℕ → Expr d} (hf : Admissible f) :
    PolyBits (fun u => (f u).bounds.denominator) ∧
    PolyBits (fun u => (f u).bounds.height) ∧ Poly (fun u => (f u).bounds.radius) := by
  induction hf with
  | scalar p q hp hq =>
    exact ⟨hq, ((polyBits_const 1).add hp).mono (fun _ => by dsimp [Expr.bounds]; omega), poly_const 0⟩
  | monomial v hv => exact ⟨polyBits_const 1, polyBits_const 1, hv⟩
  | geometric j stride J hs hJ =>
    have hpow : PolyBits (fun u => 2^(J u)) := (polyBits_const 2).pow hJ
    refine ⟨polyBits_const 1, hpow.mono (fun u => ?_), (hJ.mul hs).mono (fun u => ?_)⟩
    · change max 1 (2^(J u)-1) ≤ 2^(J u)
      have : 0 < 2^(J u) := pow_pos (by decide) _
      omega
    · exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  | neg _ ih | project _ _ _ ih => exact ih
  | add _ _ hf hg =>
    exact ⟨hf.1.mul hg.1, (hg.1.mul hf.2.1).add (hf.1.mul hg.2.1),
      (hf.2.2.add hg.2.2).mono (fun _ => by dsimp [Expr.bounds]; omega)⟩
  | mul _ _ hf hg => exact ⟨hf.1.mul hg.1, hf.2.1.mul hg.2.1, hf.2.2.add hg.2.2⟩
  | pow _ n hn ih => exact ⟨ih.1.pow hn, ih.2.1.pow hn, hn.mul ih.2.2⟩
  | threshold _ n k hn ih => exact ⟨((polyBits_const 2).mul ih.1).pow hn,
      ((polyBits_const 2).mul (ih.1.add ih.2.1)).pow hn, hn.mul ih.2.2⟩

/-- Single polynomial bound for the manuscript's `G + length D + length H`.
Binary length here is `log₂ + 1`, including one digit for zero. -/
theorem Admissible.total_size {d : ℕ} {f : ℕ → Expr d} (hf : Admissible f) :
    ∃ c : ℕ, ∀ u, let b := (f u).bounds
      b.radius + (b.denominator.log2+1) + (b.height.log2+1) ≤ (u+2)^c := by
  obtain ⟨hD,hH,hG⟩ := hf.bounds
  exact (hG.add (hD.log2.add (poly_const 1))).add (hH.log2.add (poly_const 1))

end
end DiophantineNP.LaurentBounds
