import DiophantineNP.NaturalBridge
import DiophantineNP.PackingBridge
import Mathlib.Tactic.NormNum

/-! # Turning a short rational evaluator into the packed integer graph

The rational approximation and its Diophantine evaluator may be proved
independently. A single four-square gate then selects the integer with strict
error less than one half. Its auxiliary bit cost is controlled by the
denominator already charged to the evaluator.
-/
namespace DiophantineNP.Packing

open MvPolynomial

abbrev Scalar (k : ℕ) := (U : ℕ) → (Fin k → Fin U) → ℚ
abbrev RatVar (k : ℕ) := Slot k ⊕ Unit

def ratArguments {U k : ℕ} (t : Fin k → Fin U) (p q : ℤ) : RatVar k → ℤ :=
  Sum.elim (arguments t p) (fun _ => q)

/-- Honest witnesses include the numerator and positive denominator of the result.
Every root represents this same rational value, allowing different fractions. -/
def ShortRationalGraph {k : ℕ} (f : Scalar k) : Prop :=
  ∃ (r C : ℕ) (P : MvPolynomial (RatVar k ⊕ Fin r) ℤ), ∀ U, 0<U → ∀ t : Fin k → Fin U,
    (∃ (p q : ℤ) (w : Fin r → ℤ),
      intCost w + (bits p.natAbs+1) + (bits q.natAbs+1) ≤ (1+U)^C ∧
      aeval (Sum.elim (ratArguments t p q) w) P = 0) ∧
    (∀ (p q : ℤ) w, aeval (Sum.elim (ratArguments t p q) w) P = 0 →
      0 < q ∧ (p : ℚ)/(q : ℚ) = f U t)

/-- A half-unit neighborhood of the intended integer suffices. -/
def RoundsTo {k : ℕ} (f : Scalar k) (φ : Counting.Formula (k+1)) : Prop :=
  ∀ U, 0<U → ∀ t : Fin k → Fin U, |f U t - (packed φ t : ℚ)| < 1/2

private theorem strict_square {p q y : ℤ} (hq : 0 < q) :
    0 ≤ q^2 - (2*(p-q*y))^2 - 1 ↔ |(p : ℚ)/q - (y : ℚ)| < 1/2 := by
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hu : (p : ℚ) / q - y = ((p : ℚ) - q * y) / q := by field_simp
  rw [hu, abs_div, abs_of_pos hq', div_lt_div_iff₀ hq' (by norm_num), one_mul,
    ← abs_of_pos (a := (2:ℚ)) (by norm_num), ← abs_mul, abs_lt]
  have h : -q < (p-q*y)*2 ∧ (p-q*y)*2 < q ↔
      -(q : ℚ) < ((p : ℚ) - q*y)*2 ∧ ((p : ℚ) - q*y)*2 < q := by norm_cast
  rw [← h]
  rw [show 0 ≤ q^2 - (2*(p-q*y))^2 - 1 ↔ (2*(p-q*y))^2 < q^2 by omega,
    sq_lt_sq, abs_of_pos hq, abs_lt, mul_comm 2]

private theorem unique_integer {p q x y : ℤ} (hx : |(p:ℚ)/q - x| < 1/2)
    (hy : |(p:ℚ)/q - y| < 1/2) : x=y := by
  obtain ⟨hx₁,hx₂⟩ := abs_lt.mp hx
  obtain ⟨hy₁,hy₂⟩ := abs_lt.mp hy
  have h₁ : (x:ℚ) < (y:ℚ)+1 := by linarith
  have h₂ : (y:ℚ) < (x:ℚ)+1 := by linarith
  norm_cast at h₁ h₂
  omega

private abbrev RoundAux (r : ℕ) := Fin r ⊕ (Bool ⊕ Fin 4)

private def wslot {r : ℕ} (i : Fin r) : RoundAux r := .inl i
private def frac {r : ℕ} (b : Bool) : RoundAux r := .inr (.inl b)
private def square {r : ℕ} (i : Fin 4) : RoundAux r := .inr (.inr i)

private def ratRename {k r : ℕ} : RatVar k ⊕ Fin r → Slot k ⊕ RoundAux r
  | .inl (.inl .universeSize) => .inl .universeSize
  | .inl (.inl (.parameter i)) => .inl (.parameter i)
  | .inl (.inl .output) => .inr (frac false)
  | .inl (.inr ()) => .inr (frac true)
  | .inr i => .inr (wslot i)

private noncomputable def roundPoly {k r : ℕ} (P : MvPolynomial (RatVar k ⊕ Fin r) ℤ) :
    MvPolynomial (Slot k ⊕ RoundAux r) ℤ :=
  let p : MvPolynomial (Slot k ⊕ RoundAux r) ℤ := X (.inr (frac false))
  let q : MvPolynomial (Slot k ⊕ RoundAux r) ℤ := X (.inr (frac true))
  let y : MvPolynomial (Slot k ⊕ RoundAux r) ℤ := X (.inl .output)
  (rename ratRename P)^2 +
    (q^2-(2*(p-q*y))^2-1-FourSquare.total (fun i => X (.inr (square i))))^2

private theorem round_zero {U k r : ℕ} (t : Fin k → Fin U) (y : ℤ) (v : RoundAux r → ℤ)
    (P : MvPolynomial (RatVar k ⊕ Fin r) ℤ) :
    aeval (Sum.elim (arguments t y) v) (roundPoly P) = 0 ↔
      aeval (Sum.elim (ratArguments t (v (frac false)) (v (frac true))) (v ∘ wslot)) P = 0 ∧
      (v (frac true))^2 - (2*(v (frac false)-v (frac true)*y))^2-1 =
        FourSquare.total (v ∘ square) := by
  let e := Sum.elim (arguments t y) v
  have h : eval e (rename ratRename P) =
      eval (Sum.elim (ratArguments t (v (frac false)) (v (frac true))) (v ∘ wslot)) P := by
    rw [eval_rename]
    apply congrArg (fun f => eval f P)
    funext s
    rcases s with ((s|u)|i)
    · cases s <;> rfl
    · cases u; rfl
    · rfl
  change eval e (roundPoly P) = 0 ↔ eval _ P = 0 ∧ _
  simp only [roundPoly, map_add, map_pow, map_sub, map_mul, map_ofNat, map_one,
    FourSquare.total, eval_X, h, e, Sum.elim_inr, Sum.elim_inl, arguments, Function.comp_apply]
  rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)]
  simp [sub_eq_zero]

private def roundWitness {r : ℕ} (w : Fin r → ℤ) (p q : ℤ) (v : Fin 4 → ℤ) : RoundAux r → ℤ :=
  Sum.elim w (Sum.elim (fun b : Bool => if b then q else p) v)

private theorem short_squares {q s : ℤ} (hs : 0≤s) (hsq : s ≤ q^2) :
    ∃ v : Fin 4 → ℤ, FourSquare.total v=s ∧ ∀ i, (v i).natAbs ≤ q.natAbs := by
  obtain ⟨a,b,c,d,he⟩ := Nat.sum_four_squares s.toNat
  have he' : (a:ℤ)^2+b^2+c^2+d^2 = s := by
    rw [← Int.toNat_of_nonneg hs]
    exact_mod_cast he
  let v : Fin 4 → ℤ := ![(a:ℤ),b,c,d]
  refine ⟨v,he',?_⟩
  intro i
  have hi : (v i)^2 ≤ q^2 := by
    fin_cases i <;> dsimp [v] <;> nlinarith [sq_nonneg (a:ℤ),sq_nonneg (b:ℤ),
      sq_nonneg (c:ℤ),sq_nonneg (d:ℤ)]
  have hh := (sq_le_sq.mp hi)
  exact_mod_cast (show ((v i).natAbs : ℤ) ≤ (q.natAbs : ℤ) by simpa using hh)

private theorem round_cost {r : ℕ} (w : Fin r → ℤ) (p q : ℤ) (v : Fin 4 → ℤ)
    (h : ∀ i, (v i).natAbs ≤ q.natAbs) :
    intCost (roundWitness w p q v) ≤
      5*(intCost w + (bits p.natAbs+1) + (bits q.natAbs+1)) := by
  have hv : intCost v ≤ 4*(bits q.natAbs+1) := calc
    _ ≤ ∑ _i : Fin 4, (bits q.natAbs+1) :=
      Finset.sum_le_sum (fun i _ => Nat.add_le_add_right (FourSquare.bits_mono (h i)) 1)
    _ = _ := by simp
  have hh : intCost (roundWitness w p q v) =
      intCost w + ((bits p.natAbs+1)+(bits q.natAbs+1)+intCost v) := by
    simp [intCost, roundWitness, Fintype.sum_sum_type, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc]
  omega

/-- A globally sound rational graph and a uniform analytic error estimate suffice.
This bound includes the four fresh comparison witnesses and the two fraction fields. -/
theorem packing_of_rational_evaluators
    (construction : ∀ (k : ℕ) (φ : Counting.Formula (k+1)),
      ∃ f : Scalar k, ShortRationalGraph f ∧ RoundsTo f φ) : PackingClaim := by
  intro k φ
  obtain ⟨f,⟨r,C,P,hP⟩,approx⟩ := construction k φ
  let E := Fintype.equivFin (RoundAux r)
  refine ⟨_,C+3,rename (Sum.map id E) (roundPoly P),?_⟩
  intro U hU t
  obtain ⟨honest,sound⟩ := hP U hU t
  have reindex (v : Fin (Fintype.card (RoundAux r)) → ℤ) (y : ℤ) :
      aeval (Sum.elim (arguments t y) v) (rename (Sum.map id E) (roundPoly P)) =
      aeval (Sum.elim (arguments t y) (v ∘ E)) (roundPoly P) := by
    change eval _ (rename _ _) = eval _ _
    rw [eval_rename]
    apply congrArg (fun h => eval h (roundPoly P))
    funext s; cases s <;> rfl
  constructor
  · obtain ⟨p,q,w,short,hzero⟩ := honest
    obtain ⟨hq, hr⟩ := sound p q w hzero
    let y : ℤ := packed φ t
    have happ := approx U hU t
    rw [← hr] at happ
    have hslack := (strict_square (y := y) hq).2 (by exact_mod_cast happ)
    obtain ⟨v,hv,hcost⟩ := short_squares hslack
      (show q^2-(2*(p-q*y))^2-1 ≤ q^2 by nlinarith [sq_nonneg (2*(p-q*y))])
    let aux := roundWitness w p q v
    refine ⟨aux ∘ E.symm, ?_, ?_⟩
    · have he : intCost (aux ∘ E.symm) = intCost aux :=
        E.symm.sum_comp (fun i => bits (aux i).natAbs+1)
      rw [he]
      refine (round_cost w p q v hcost).trans ((Nat.mul_le_mul_left 5 short).trans ?_)
      have : 5 ≤ (1+U)^3 := (by decide : 5 ≤ 2^3).trans (Nat.pow_le_pow_left (by omega) _)
      simpa [pow_add, Nat.mul_comm] using Nat.mul_le_mul_right ((1+U)^C) this
    · rw [reindex]
      simp only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
      apply (round_zero ..).2
      exact ⟨hzero,hv.symm⟩
  · intro y w hw
    rw [reindex, round_zero] at hw
    obtain ⟨hq,hr⟩ := sound _ _ _ hw.1
    have hnon : 0 ≤ FourSquare.total ((w ∘ E) ∘ square) := by unfold FourSquare.total; positivity
    have hnear := (strict_square hq).1 (hw.2.symm ▸ hnon)
    have ht := approx U hU t
    rw [← hr] at ht
    exact unique_integer hnear (by exact_mod_cast ht)

end DiophantineNP.Packing
