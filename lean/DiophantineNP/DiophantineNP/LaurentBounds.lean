import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Integral numerator expansions for rational Laurent expressions

We keep repeated exponents as separate summands. Their absolute coefficient
sum bounds the coefficient norm even before cancellation. The syntax below
acts on an arbitrary fixed finite set of coordinates, including signed
monomials, powers, the binomial tail and cyclic projection in one coordinate.
-/

namespace DiophantineNP.LaurentBounds

open Finset

variable {d : ℕ}

structure Raw (d : ℕ) where
  terms : Type
  [finiteTerms : Fintype terms]
  coeff : terms → ℤ
  exponent : terms → Fin d → ℤ

attribute [instance] Raw.finiteTerms

noncomputable section

namespace Raw

def atom (a : ℤ) (v : Fin d → ℤ) : Raw d := ⟨Unit, fun _ => a, fun _ => v⟩

def plus (P Q : Raw d) : Raw d :=
  ⟨P.terms ⊕ Q.terms, Sum.elim P.coeff Q.coeff, Sum.elim P.exponent Q.exponent⟩

def scale (a : ℤ) (P : Raw d) : Raw d :=
  ⟨P.terms, fun t => a * P.coeff t, P.exponent⟩

def mul (P Q : Raw d) : Raw d :=
  ⟨P.terms × Q.terms, fun t => P.coeff t.1 * Q.coeff t.2,
    fun t j => P.exponent t.1 j + Q.exponent t.2 j⟩

def pow (P : Raw d) : ℕ → Raw d
  | 0 => atom 1 (fun _ => 0)
  | n+1 => (P.pow n).mul P

/-- Orthogonality keeps terms with divisible exponent and evaluates their
coordinate at one. Other coordinates keep their exponents. -/
def project (P : Raw d) (j : Fin d) (m : ℕ) : Raw d :=
  ⟨P.terms, fun t => if (m : ℤ) ∣ P.exponent t j then P.coeff t else 0,
    fun t k => if k = j then 0 else P.exponent t k⟩

/-- Binomial numerator on `P`, with `D` its common denominator. -/
def tailTerm (P : Raw d) (D n i : ℕ) : Raw d :=
  let C := atom (D : ℤ) (fun _ => 0)
  let A := C.plus P
  let B := C.plus (P.scale (-1))
  (A.pow i).mul (B.pow (n-i))

def tail (P : Raw d) (D n k : ℕ) : Raw d :=
  let T := fun i : Fin (n+1) => tailTerm P D n i
  ⟨(i : Fin (n+1)) × (T i).terms,
    fun t => if k ≤ t.1.val then n.choose t.1.val * (T t.1).coeff t.2 else 0,
    fun t => (T t.1).exponent t.2⟩

/-- Negative stride in the selected Fourier coordinate. -/
def step (coordinate : Fin d) (stride : ℕ) : Fin d → ℤ :=
  fun j => if j = coordinate then -(stride : ℤ) else 0

/-- `∑_{i<J} 2^i w^{-stride*i}` with one summand for every kernel digit. -/
def geometric (coordinate : Fin d) (stride J : ℕ) : Raw d :=
  ⟨Fin J, fun i => (2 : ℤ)^i.val, fun i => i.val • step coordinate stride⟩

def mass (P : Raw d) : ℕ := ∑ i, (P.coeff i).natAbs

/-- Absolute coefficient budget and coordinatewise exponent budget. -/
def Safe (P : Raw d) (H G : ℕ) : Prop :=
  P.mass ≤ H ∧ ∀ t j, (P.exponent t j).natAbs ≤ G

lemma safe_atom {a : ℤ} {v : Fin d → ℤ} {H G : ℕ}
    (ha : a.natAbs ≤ H) (hv : ∀ j, (v j).natAbs ≤ G) : (atom a v).Safe H G := by
  exact ⟨by simpa [mass, atom] using ha, fun _ j => hv j⟩

lemma safe_scale {P : Raw d} {H G : ℕ} (h : P.Safe H G) (a : ℤ) :
    (P.scale a).Safe (a.natAbs * H) G := by
  refine ⟨?_, h.2⟩
  simpa [mass, scale, Int.natAbs_mul, Finset.mul_sum] using Nat.mul_le_mul_left a.natAbs h.1

lemma safe_plus {P Q : Raw d} {h g h' g' : ℕ} (hp : P.Safe h g) (hq : Q.Safe h' g') :
    (P.plus Q).Safe (h+h') (max g g') := by
  constructor
  · simpa [mass, plus, Fintype.sum_sum_type] using Nat.add_le_add hp.1 hq.1
  · rintro (t | t) j
    · exact (hp.2 t j).trans (le_max_left ..)
    · exact (hq.2 t j).trans (le_max_right ..)

lemma safe_mul {P Q : Raw d} {h g h' g' : ℕ} (hp : P.Safe h g) (hq : Q.Safe h' g') :
    (P.mul Q).Safe (h*h') (g+g') := by
  constructor
  · calc
      (P.mul Q).mass = P.mass * Q.mass := by
        simp only [mass, mul, Fintype.sum_prod_type, Int.natAbs_mul]
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum]
      _ ≤ _ := Nat.mul_le_mul hp.1 hq.1
  · intro t j
    exact (Int.natAbs_add_le ..).trans (Nat.add_le_add (hp.2 t.1 j) (hq.2 t.2 j))

lemma safe_pow {P : Raw d} {h g : ℕ} (hp : P.Safe h g) (n : ℕ) :
    (P.pow n).Safe (h^n) (n*g) := by
  induction n with
  | zero => exact safe_atom (by simp) (by simp)
  | succ n ih => simpa [pow, pow_succ, Nat.succ_mul] using safe_mul ih hp

lemma safe_project {P : Raw d} {H G : ℕ} (hp : P.Safe H G) (j : Fin d) (m : ℕ) :
    (P.project j m).Safe H G := by
  constructor
  · refine le_trans (b := P.mass) ?_ hp.1
    apply Finset.sum_le_sum
    intro t _
    change (if (m : ℤ) ∣ P.exponent t j then P.coeff t else 0).natAbs ≤ _
    split <;> simp
  · intro t k
    change (if k = j then 0 else P.exponent t k).natAbs ≤ _
    split <;> simp [hp.2]

lemma safe_tailTerm {P : Raw d} {H G : ℕ} (hp : P.Safe H G) (D n : ℕ)
    (i : Fin (n+1)) : (P.tailTerm D n i).Safe ((D+H)^n) (n*G) := by
  have hc : (atom (D : ℤ) (fun _ : Fin d => 0)).Safe D 0 := safe_atom (by simp) (by simp)
  have hp' : (P.scale (-1)).Safe H G := by simpa using safe_scale hp (-1)
  have ha := safe_pow (safe_plus hc hp) i.val
  have hb := safe_pow (safe_plus hc hp') (n-i.val)
  have hi : i.val + (n-i.val) = n := by have := i.isLt; omega
  simpa [tailTerm, ← pow_add, ← Nat.add_mul, hi] using safe_mul ha hb

lemma safe_tail {P : Raw d} {H G : ℕ} (hp : P.Safe H G) (D n k : ℕ) :
    (P.tail D n k).Safe ((2*(D+H))^n) (n*G) := by
  constructor
  · let T := fun i : Fin (n+1) => P.tailTerm D n i
    change (∑ t : (i : Fin (n+1)) × (T i).terms,
      (if k ≤ t.1.val then (n.choose t.1.val : ℤ) * (T t.1).coeff t.2 else 0).natAbs) ≤ _
    rw [Fintype.sum_sigma]
    calc
      _ ≤ ∑ i : Fin (n+1), n.choose i.val * (D+H)^n := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : k ≤ i.val
        · simpa [hi, Int.natAbs_mul, Finset.mul_sum, mass, T] using
            Nat.mul_le_mul_left (n.choose i.val) (safe_tailTerm hp D n i).1
        · simp [hi]
      _ = _ := by rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range, Nat.sum_range_choose, mul_pow]
  · intro t j
    exact (safe_tailTerm hp D n t.1).2 t.2 j

lemma safe_geometric (j : Fin d) (stride J : ℕ) :
    (geometric j stride J).Safe (max 1 (2^J-1)) ((J-1)*stride) := by
  constructor
  · have hs : ∀ n, (∑ i ∈ range n, (2 : ℕ)^i) + 1 = 2^n := by
      intro n
      induction n with
      | zero => simp
      | succ n h => rw [sum_range_succ, pow_succ]; omega
    simp only [mass, geometric, Int.natAbs_pow, Fin.sum_univ_eq_sum_range]
    change (∑ i ∈ range J, (2 : ℕ)^i) ≤ max 1 (2^J-1)
    have := hs J
    omega
  · intro i k
    by_cases hk : k = j
    · simpa [geometric, Pi.smul_apply, step, hk, nsmul_eq_mul, Int.natAbs_mul] using
        Nat.mul_le_mul_right stride (show i.val ≤ J-1 by have := i.isLt; omega)
    · simp [geometric, Pi.smul_apply, step, hk]

end Raw

/-- A fixed tree. Exponents, periods and threshold parameters are numerical inputs to nodes. -/
inductive Expr (d : ℕ) where
  | scalar (p : ℤ) (q : ℕ+)   -- numerator and positive denominator
  | monomial (v : Fin d → ℤ)
  | geometric (coordinate : Fin d) (stride J : ℕ)
  | add (f g : Expr d)
  | neg (f : Expr d)
  | mul (f g : Expr d)
  | pow (f : Expr d) (n : ℕ)
  | threshold (f : Expr d) (n k : ℕ)
  | project (f : Expr d) (coordinate : Fin d) (period : ℕ+)

structure Bounds where
  denominator : ℕ
  height : ℕ
  radius : ℕ

/-- The manuscript's triple, computed without enumerating any coefficients. -/
def Expr.bounds : Expr d → Bounds
  | .scalar p q => ⟨q, max 1 p.natAbs, 0⟩
  | .monomial v => ⟨1, 1, Finset.univ.sup fun j => (v j).natAbs⟩
  | .geometric _ stride J => ⟨1, max 1 (2^J-1), (J-1)*stride⟩
  | .neg f | .project f _ _ => f.bounds
  | .add f g => ⟨f.bounds.denominator * g.bounds.denominator,
      g.bounds.denominator * f.bounds.height + f.bounds.denominator * g.bounds.height,
      max f.bounds.radius g.bounds.radius⟩
  | .mul f g => ⟨f.bounds.denominator * g.bounds.denominator,
      f.bounds.height * g.bounds.height, f.bounds.radius + g.bounds.radius⟩
  | .pow f n => ⟨f.bounds.denominator^n, f.bounds.height^n, n*f.bounds.radius⟩
  | .threshold f n _ => ⟨(2*f.bounds.denominator)^n,
      (2*(f.bounds.denominator + f.bounds.height))^n, n*f.bounds.radius⟩

/-- Integral numerator expansion for that denominator. -/
def Expr.expand : Expr d → Raw d
  | .scalar p _ => .atom p (fun _ => 0)
  | .monomial v => .atom 1 v
  | .geometric j stride J => Raw.geometric j stride J
  | .neg f => f.expand.scale (-1)
  | .project f i m => f.expand.project i m
  | .add f g => (f.expand.scale g.bounds.denominator).plus (g.expand.scale f.bounds.denominator)
  | .mul f g => f.expand.mul g.expand
  | .pow f n => f.expand.pow n
  | .threshold f n k => f.expand.tail f.bounds.denominator n k

/-- The expression tree's bound controls every term and the full sum of absolute coefficients. -/
theorem Expr.bounds_sound (f : Expr d) : f.expand.Safe f.bounds.height f.bounds.radius := by
  induction f with
  | scalar p q => exact Raw.safe_atom (le_max_right ..) (by simp)
  | monomial v => exact Raw.safe_atom (by simp [bounds]) (fun j => Finset.le_sup (f := fun j => (v j).natAbs) (Finset.mem_univ j))
  | geometric j stride J => exact Raw.safe_geometric j stride J
  | neg f h => simpa [expand,bounds] using Raw.safe_scale h (-1)
  | project f i m h => exact Raw.safe_project h i m
  | add f g hf hg =>
    simpa [expand,bounds] using Raw.safe_plus (Raw.safe_scale hf (g.bounds.denominator : ℤ))
      (Raw.safe_scale hg (f.bounds.denominator : ℤ))
  | mul f g hf hg => exact Raw.safe_mul hf hg
  | pow f n h => exact Raw.safe_pow h n
  | threshold f n k h => exact Raw.safe_tail h f.bounds.denominator n k

/-- Every denominator used in the expansion is positive. -/
theorem Expr.denominator_pos (f : Expr d) : 0 < f.bounds.denominator := by
  induction f <;> simp_all [bounds]

end
end DiophantineNP.LaurentBounds
