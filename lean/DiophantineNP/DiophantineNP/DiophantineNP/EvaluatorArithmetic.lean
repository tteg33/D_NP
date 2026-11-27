import DiophantineNP.EvaluatorGrowth

/-! # Certified arithmetic operations on scalar terms -/

namespace DiophantineNP.Blueprint
open LaurentBounds ScalarProgram ScalarProjection FormulaLaurent
open scoped BigOperators
noncomputable section

namespace Arith
open MvPolynomial
variable {I : Type}

@[simp] theorem run_lit (a : ℤ) (ι : I → ℤ) : (Term.literal a).run ι = a := rfl
@[simp] theorem run_input (i : I) (ι : I → ℤ) : (Term.input i).run ι = ι i := rfl

def add (x y : Term I) : Term I := .app (ofPolynomial (X false + X true)) x y

@[simp] theorem run_add (x y : Term I) (ι : I → ℤ) :
    (add x y).run ι = x.run ι + y.run ι := by
  simp [add, Term.run, ofPolynomial]

theorem small_add {x y : Term I} (hx : SmallTerm x) (hy : SmallTerm y) : SmallTerm (add x y) :=
  .app (valueTame_ofPolynomial _) hx hy

theorem tame_add {x y : Term I} (hx : TameTerm x) (hy : TameTerm y) : TameTerm (add x y) :=
  .app (bitTame_ofPolynomial _) hx hy

def sub (x y : Term I) : Term I := .app (ofPolynomial (X false - X true)) x y

@[simp] theorem run_sub (x y : Term I) (ι : I → ℤ) :
    (sub x y).run ι = x.run ι - y.run ι := by
  simp [sub, Term.run, ofPolynomial]

theorem small_sub {x y : Term I} (hx : SmallTerm x) (hy : SmallTerm y) : SmallTerm (sub x y) :=
  .app (valueTame_ofPolynomial _) hx hy

theorem tame_sub {x y : Term I} (hx : TameTerm x) (hy : TameTerm y) : TameTerm (sub x y) :=
  .app (bitTame_ofPolynomial _) hx hy

def mul (x y : Term I) : Term I := .app (ofPolynomial (X false * X true)) x y

@[simp] theorem run_mul (x y : Term I) (ι : I → ℤ) :
    (mul x y).run ι = x.run ι * y.run ι := by
  simp [mul, Term.run, ofPolynomial]

theorem small_mul {x y : Term I} (hx : SmallTerm x) (hy : SmallTerm y) : SmallTerm (mul x y) :=
  .app (valueTame_ofPolynomial _) hx hy

theorem tame_mul {x y : Term I} (hx : TameTerm x) (hy : TameTerm y) : TameTerm (mul x y) :=
  .app (bitTame_ofPolynomial _) hx hy

def div (x y : Term I) : Term I := .app divisionOperation x y

@[simp] theorem run_div (x y : Term I) (ι : I → ℤ) :
    (div x y).run ι = positiveDiv (x.run ι) (y.run ι) := rfl

theorem small_div {x y : Term I} (hx : SmallTerm x) (hy : SmallTerm y) : SmallTerm (div x y) :=
  .app valueTame_division hx hy

theorem tame_div {x y : Term I} (hx : TameTerm x) (hy : TameTerm y) : TameTerm (div x y) :=
  .app bitTame_division hx hy

def pow (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (x n : Term I) : Term I :=
  .app (signedPower hc hq) x n

@[simp] theorem run_pow (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (x n : Term I) (ι : I → ℤ) :
    (pow hc hq x n).run ι = x.run ι ^ (n.run ι).toNat := rfl

theorem tame_pow (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {x n : Term I} (hx : TameTerm x) (hn : SmallTerm n) : TameTerm (pow hc hq x n) :=
  .power (powerTame_signedPower hc hq) hx hn

/-- A product indexed by a fixed set of coordinates unrolls into multiplications. -/
def prod : {d : ℕ} → (Fin d → Term I) → Term I
  | 0, _ => .literal 1
  | d+1, x => mul (x 0) (prod (fun i : Fin d => x i.succ))

@[simp] theorem run_prod {d : ℕ} (x : Fin d → Term I) (ι : I → ℤ) :
    (prod x).run ι = ∏ i, (x i).run ι := by
  induction d with
  | zero => simp [prod]
  | succ d ih => rw [prod, run_mul, ih, Fin.prod_univ_succ]

theorem tame_prod {d : ℕ} {x : Fin d → Term I} (h : ∀ i, TameTerm (x i)) : TameTerm (prod x) := by
  induction d with
  | zero => exact .small (.literal 1)
  | succ d ih => exact tame_mul (h 0) (ih (fun i => h i.succ))

theorem small_prod {d : ℕ} {x : Fin d → Term I} (h : ∀ i, SmallTerm (x i)) : SmallTerm (prod x) := by
  induction d with
  | zero => exact .literal 1
  | succ d ih => exact small_mul (h 0) (ih (fun i => h i.succ))

/-- A fixed natural exponent can be evaluated using only polynomial operations. -/
def fixedPow (x : Term I) : ℕ → Term I
  | 0 => .literal 1
  | n+1 => mul (fixedPow x n) x

@[simp] theorem run_fixedPow (x : Term I) (n : ℕ) (ι : I → ℤ) :
    (fixedPow x n).run ι = x.run ι ^ n := by
  induction n with
  | zero => simp [fixedPow]
  | succ n ih => simp [fixedPow, ih, pow_succ]

theorem tame_fixedPow {x : Term I} (hx : TameTerm x) (n : ℕ) : TameTerm (fixedPow x n) := by
  induction n with
  | zero => exact .small (.literal 1)
  | succ n ih => exact tame_mul ih hx

theorem small_fixedPow {x : Term I} (hx : SmallTerm x) (n : ℕ) : SmallTerm (fixedPow x n) := by
  induction n with
  | zero => exact .literal 1
  | succ n ih => exact small_mul ih hx

end Arith

end
end DiophantineNP.Blueprint
