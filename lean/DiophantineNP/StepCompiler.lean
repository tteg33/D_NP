import DiophantineNP.IntegerCurveStep
import DiophantineNP.ConstraintCost
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Compiling the six-coordinate elliptic height test

Slots 0–5 store the two reduced x-coordinates and the first y-coordinate;
6–7 store modular inverses certifying coprimality, and 8–9 store the two
heights. Every inverse may be taken below its positive denominator.
-/

namespace DiophantineNP.PowerPolynomial

open MvPolynomial Compiler PowerTests

noncomputable section

variable {σ : Type*}
abbrev Poly (σ : Type*) := MvPolynomial σ ℤ

local infixr:35 " ⋏ " => Compiler.Formula.both
local infixr:30 " ⋎ " => Compiler.Formula.either

def eqn (p q : Poly σ) : Formula σ := .zero (p-q)
def leq (p q : Poly σ) : Formula σ := .nonnegative (q-p)
def less (p q : Poly σ) : Formula σ := .nonnegative (q-p-1)

@[simp] theorem holds_eqn (x : σ → ℤ) (p q : Poly σ) : (eqn p q).Holds x ↔ eval x p = eval x q := by
  simp [eqn, Formula.Holds, sub_eq_zero]
@[simp] theorem holds_leq (x : σ → ℤ) (p q : Poly σ) : (leq p q).Holds x ↔ eval x p ≤ eval x q := by
  simp [leq, Formula.Holds]
@[simp] theorem holds_less (x : σ → ℤ) (p q : Poly σ) : (less p q).Holds x ↔ eval x p < eval x q := by
  simp only [less, Formula.Holds, map_sub, map_one]
  omega

/-- `h` is the maximum absolute value of two signed integer entries. -/
def heightGate (a b h : Poly σ) : Formula σ :=
  leq a h ⋏ leq (-a) h ⋏ leq b h ⋏ leq (-b) h ⋏ (eqn a h ⋎ eqn (-a) h ⋎ eqn b h ⋎ eqn (-b) h)

@[simp] theorem heightGate_iff (x : σ → ℤ) (a b h : Poly σ) :
    (heightGate a b h).Holds x ↔ eval x h = ↑(max (eval x a).natAbs (eval x b).natAbs) := by
  simp only [heightGate, Formula.Holds, holds_leq, holds_eqn, map_neg, Nat.cast_max,
    Int.natCast_natAbs]
  rw [abs_eq_max_neg, abs_eq_max_neg]
  omega

/-- A modular inverse certifies a Bézout equation. -/
private theorem primitive_of_inverse {u v k : ℤ} (h : v ∣ 1-u*k) : IsCoprime u v := by
  obtain ⟨b,hb⟩ := h
  exact ⟨k,b,by linarith only [hb]⟩

/-- A reduced inverse never increases the magnitude budget. -/
theorem bounded_inverse {u v : ℤ} (hv : 0 < v) (h : IsCoprime u v) :
    ∃ k : ℤ, v ∣ 1-u*k ∧ k.natAbs ≤ v.natAbs := by
  obtain ⟨a,b,h⟩ := h
  have hm : u*a ≡ 1 [ZMOD v] := Int.modEq_iff_dvd.mpr ⟨b,by linarith only [h]⟩
  have hm' := ((Int.mod_modEq a v).mul_left u).trans hm
  refine ⟨a%v, hm'.dvd, ?_⟩
  have hn := Int.emod_nonneg a hv.ne'
  have hl := Int.emod_lt_of_pos a hv
  exact_mod_cast (show ((a%v).natAbs : ℤ) ≤ (v.natAbs : ℤ) by
    rw [Int.natAbs_of_nonneg hn, Int.natAbs_of_nonneg hv.le]; omega)

/-- This gate is parameterized by a polynomial tuple, so it can be embedded
without renaming variable types in a larger fixed circuit. -/
def stepGate (c : Fin 10 → Poly σ) : Formula σ :=
  let u := c 0; let v := c 1; let r := c 2; let s := c 3
  let a := c 4; let b := c 5
  less 0 v ⋏ less 0 s ⋏ less 0 b ⋏ (less 0 u ⋎ less u 0) ⋏
  .divides v (1-u*c 6) ⋏ .divides b (1-a*c 7) ⋏
  eqn ((r^2+r*s)*v^3) ((u^3-u*v^2)*s^2) ⋏
  eqn (a*(s^2*u^2*v)) (b*(r^2*v^3-s^2*u^3)) ⋏
  heightGate u v (c 8) ⋏ heightGate a b (c 9)

def unpackStep (c : Fin 10 → ℤ) : Step := ⟨c 0,c 1,c 2,c 3,c 4,c 5⟩

def StepSpec (c : Fin 10 → ℤ) : Prop :=
  let w := unpackStep c
  0 < c 1 ∧ 0 < c 3 ∧ 0 < c 5 ∧ c 0 ≠ 0 ∧
  c 1 ∣ 1-c 0*c 6 ∧ c 5 ∣ 1-c 4*c 7 ∧
  (c 2^2+c 2*c 3)*c 1^3 = (c 0^3-c 0*c 1^2)*c 3^2 ∧
  c 4*(c 3^2*c 0^2*c 1) = c 5*(c 2^2*c 1^3-c 3^2*c 0^3) ∧
  c 8 = w.start ∧ c 9 = w.finish

theorem stepGate_iff (x : σ → ℤ) (c : Fin 10 → Poly σ) :
    (stepGate c).Holds x ↔ StepSpec (fun i => eval x (c i)) := by
  simp only [stepGate, StepSpec, unpackStep, Step.start, Step.finish, Formula.Holds,
    holds_less, holds_eqn, heightGate_iff, map_sub, map_mul, map_pow, map_add, map_zero, map_one]
  rw [show (0 < eval x (c 0) ∨ eval x (c 0) < 0) ↔ eval x (c 0) ≠ 0 by omega]

theorem decode_step {c : Fin 10 → ℤ} (hc : StepSpec c) :
    (unpackStep c).Valid ∧ c 8 = (unpackStep c).start ∧ c 9 = (unpackStep c).finish := by
  obtain ⟨hv,hs,hb,hu,hi,hj,he,hf,hh,hn⟩ := hc
  exact ⟨⟨hv,hs,hb,hu,primitive_of_inverse hi,primitive_of_inverse hj,he,hf⟩,hh,hn⟩

/-- Includes all six raw coordinates and the magnitudes of both heights. -/
def stepSize (w : Step) := max (max w.start w.finish) (max w.yNum.natAbs w.yDen.natAbs)

theorem encode_step (w : Step) (hw : w.Valid) :
    ∃ c : Fin 10 → ℤ, StepSpec c ∧ unpackStep c = w ∧ ∀ i, (c i).natAbs ≤ stepSize w := by
  obtain ⟨hv,hs,hb,hu,hcop,hcop',he,hf⟩ := hw
  obtain ⟨k,hk,hk'⟩ := bounded_inverse hv hcop
  obtain ⟨l,hl,hl'⟩ := bounded_inverse hb hcop'
  let c : Fin 10 → ℤ := ![w.xNum,w.xDen,w.yNum,w.yDen,w.nextNum,w.nextDen,k,l,(w.start:ℤ),w.finish]
  have hw' : unpackStep c = w := rfl
  refine ⟨c, ⟨hv,hs,hb,hu,hk,hl,he,hf,rfl,rfl⟩, hw', ?_⟩
  intro i
  have A := le_max_left (max w.start w.finish) (max w.yNum.natAbs w.yDen.natAbs)
  have B := le_max_right (max w.start w.finish) (max w.yNum.natAbs w.yDen.natAbs)
  have A₁ := (le_max_left w.start w.finish).trans A
  have A₂ := (le_max_right w.start w.finish).trans A
  fin_cases i
  · exact (le_max_left ..).trans A₁
  · exact (le_max_right ..).trans A₁
  · exact (le_max_left ..).trans B
  · exact (le_max_right ..).trans B
  · exact (le_max_left ..).trans A₂
  · exact (le_max_right ..).trans A₂
  · exact (hk'.trans (le_max_right ..)).trans A₁
  · exact (hl'.trans (le_max_right ..)).trans A₂
  · exact A₁
  · exact A₂

end
end DiophantineNP.PowerPolynomial
