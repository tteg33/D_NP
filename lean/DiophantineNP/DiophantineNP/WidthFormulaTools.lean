import DiophantineNP.PrimeFormula

/-! Syntax and semantics for the finite-arithmetic primitives of §2.1.
The iterator operates on a formula for its input relation; each operation
produces a formula before the finite universe or its parameter values are given. -/
namespace DiophantineNP.WidthFormula
open Counting PrimeFormula WidthData

def productPrefix (f : ℕ → ℕ) (s : ℕ) := ((List.range s).map f).prod

theorem product_succ (f : ℕ → ℕ) (s : ℕ) : productPrefix f (s+1) = productPrefix f s * f s := by
  simp [productPrefix, List.range_succ]

/-- Both private bound variables precede the parameter environment. Slot zero
is the bit-position query, slot one the index of the input word. -/
abbrev extend {k U : ℕ} (j t : Fin U) (env : Fin k → Fin U) : Fin (k+2) → Fin U :=
  Fin.cases j (Fin.cases t env)

/-- Operations used by the prime, factor, modulus and individual summand formulas. -/
structure ProductArithmetic where
  bit {k : ℕ} : Fin k → Fin k → Formula k
  bit_spec {k U : ℕ} (x j : Fin k) (env : Fin k → Fin U) :
    (bit x j).eval env = (env x).val.testBit (env j).val
  product {k : ℕ} (j : Fin k) (input : Formula (k+2)) : Formula k
  product_spec {k U : ℕ} (j : Fin k) (input : Formula (k+2)) (env : Fin k → Fin U) (f : ℕ → ℕ)
    (fits : ∀ t < U, f t < 2^U)
    (correct : ∀ b t : Fin U, input.eval (extend b t env) = (f t.val).testBit b.val) :
    (product j input).eval env = (productPrefix f U).testBit (env j).val

/-- Native finite-arithmetic BIT and the low-output-bit versions of the
uniform iterated sum and product theorems of Hesse–Allender–Barrington.
Only input words must fit in U bits. The result itself may be larger. -/
structure Arithmetic where
  bit {k : ℕ} : Fin k → Fin k → Formula k
  bit_spec {k U : ℕ} (x j : Fin k) (env : Fin k → Fin U) :
    (bit x j).eval env = (env x).val.testBit (env j).val
  product {k : ℕ} (j : Fin k) (input : Formula (k+2)) : Formula k
  sum {k : ℕ} (j : Fin k) (input : Formula (k+2)) : Formula k
  product_spec {k U : ℕ} (j : Fin k) (input : Formula (k+2)) (env : Fin k → Fin U) (f : ℕ → ℕ)
    (fits : ∀ t < U, f t < 2^U)
    (correct : ∀ b t : Fin U, input.eval (extend b t env) = (f t.val).testBit b.val) :
    (product j input).eval env = (productPrefix f U).testBit (env j).val
  sum_spec {k U : ℕ} (j : Fin k) (input : Formula (k+2)) (env : Fin k → Fin U) (f : ℕ → ℕ)
    (fits : ∀ t < U, f t < 2^U)
    (correct : ∀ b t : Fin U, input.eval (extend b t env) = (f t.val).testBit b.val) :
    (sum j input).eval env = (Readout.prefixSum f U).testBit (env j).val

/-- Forget the unrestricted sum operation when only bit and product are needed. -/
def Arithmetic.toProductArithmetic (A : Arithmetic) : ProductArithmetic where
  bit := A.bit
  bit_spec := A.bit_spec
  product := A.product
  product_spec := A.product_spec

instance : Coe Arithmetic ProductArithmetic := ⟨Arithmetic.toProductArithmetic⟩

abbrev up2 {k : ℕ} (i : Fin k) := i.succ.succ
abbrev up3 {k : ℕ} (i : Fin k) := i.succ.succ.succ
abbrev up4 {k : ℕ} (i : Fin k) := i.succ.succ.succ.succ

def andF {k : ℕ} (a b : Formula k) := Formula.conj a b
def addF {k : ℕ} (a b c : Fin k) := Formula.atom (Atom.add a b c)
def mulF {k : ℕ} (a b c : Fin k) := Formula.atom (Atom.mul a b c)
def eqF {k : ℕ} (a b : Fin k) := Formula.atom (Atom.eqv a b)
def notF {k : ℕ} (a : Formula k) := Formula.neg a

theorem andF_spec {k U : ℕ} (a b : Formula k) (env : Fin k → Fin U) :
    (andF a b).eval env = true ↔ a.eval env = true ∧ b.eval env = true := by simp [andF, Formula.eval]
theorem addF_spec {k U : ℕ} (a b c : Fin k) (env : Fin k → Fin U) :
    (addF a b c).eval env = true ↔ (env a).val+(env b).val=(env c).val := by simp [addF, Formula.eval, Atom.eval]
theorem mulF_spec {k U : ℕ} (a b c : Fin k) (env : Fin k → Fin U) :
    (mulF a b c).eval env = true ↔ (env a).val*(env b).val=(env c).val := by simp [mulF, Formula.eval, Atom.eval]
theorem eqF_spec {k U : ℕ} (a b : Fin k) (env : Fin k → Fin U) :
    (eqF a b).eval env = true ↔ (env a).val=(env b).val := by simp [eqF, Formula.eval, Atom.eval, Fin.ext_iff]
theorem notF_spec {k U : ℕ} (a : Formula k) (env : Fin k → Fin U) :
    (notF a).eval env = true ↔ ¬a.eval env = true := by simp [notF, Formula.eval]

def isNat {k : ℕ} (r : ℕ) (x : Fin k) : Formula k := andF (atLeast r x) (notF (atLeast (r+1) x))

theorem isNat_spec {k U : ℕ} (r : ℕ) (x : Fin k) (env : Fin k → Fin U) :
    (isNat r x).eval env = true ↔ (env x).val = r := by
  simp only [isNat, andF_spec, notF_spec, atLeast_true]; omega

def branch {k : ℕ} (p a b : Formula k) : Formula k := .disj (.conj p a) (.conj (.neg p) b)
theorem branch_eval {k U : ℕ} (p a b : Formula k) (env : Fin k → Fin U) :
    (branch p a b).eval env = if p.eval env then a.eval env else b.eval env := by
  cases he : p.eval env <;> simp [branch, Formula.eval, he]

def zeroBit {k : ℕ} (j : Fin k) : Formula k := notF (eqF j j)
def oneBit {k : ℕ} (j : Fin k) : Formula k := isNat 0 j

theorem zeroBit_spec {k U} (j : Fin k) (env : Fin k → Fin U) : (zeroBit j).eval env = (0:ℕ).testBit (env j).val := by
  simp [zeroBit, notF, eqF, Formula.eval, Atom.eval]
theorem oneBit_spec {k U} (j : Fin k) (env : Fin k → Fin U) : (oneBit j).eval env = (1:ℕ).testBit (env j).val := by
  apply Bool.eq_iff_iff.mpr
  rw [oneBit, isNat_spec]
  change _ ↔ (2^0 : ℕ).testBit (env j).val = true
  rw [Nat.testBit_two_pow, decide_eq_true_eq]; exact eq_comm

theorem exponent_fits (n : ℕ) : 4*n+10 < universeSize n := by
  have h : 2 ≤ n+2 := by omega
  have e : (n+2)^4 ≤ universeSize n := Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith [Nat.zero_le (n^4), Nat.zero_le (n^3), Nat.zero_le (n^2)]

/-- For the padded inner product, slots below 4n+10 contain the prime. -/
def belowExp {k : ℕ} (t n : Fin k) : Formula k :=
  .ex (.ex (.ex (.ex (andF (isNat 4 (up3 (0:Fin (k+1))))
    (andF (isNat 10 (up2 (0:Fin (k+2))))
    (andF (mulF (up3 (0:Fin (k+1))) (up4 n) (0:Fin (k+3)).succ)
    (andF (addF (0:Fin (k+3)).succ (up2 (0:Fin (k+2))) 0) (ltF (up4 t) 0))))))))

theorem belowExp_spec {k n : ℕ} (t x : Fin k) (env : Fin k → Fin (universeSize n))
    (hn : (env x).val = n) : (belowExp t x).eval env = true ↔ (env t).val < 4*n+10 := by
  simp only [belowExp, exists_true, andF_spec, isNat_spec, mulF_spec, addF_spec, ltF_true,
    up2, up3, up4, Fin.cases_zero, Fin.cases_succ, hn]
  constructor
  · rintro ⟨a,b,c,d,ha,hb,hc,hd,ht⟩; rw [ha] at hc; omega
  · intro ht
    have h := exponent_fits n
    exact ⟨⟨4, by omega⟩,⟨10, by omega⟩,⟨4*n, by omega⟩,⟨4*n+10,h⟩,rfl,rfl,rfl,rfl,ht⟩

/-- An iterator may be padded past its last active slot by its neutral element. -/
theorem product_pad (f : ℕ → ℕ) {s U : ℕ} (hs : s ≤ U) :
    productPrefix (fun t => if t<s then f t else 1) U = productPrefix f s := by
  induction U, hs using Nat.le_induction with
  | base =>
    unfold productPrefix
    congr 1
    apply List.map_congr_left
    intro t ht; simp [List.mem_range.mp ht]
  | succ U h ih => simp [product_succ, ih, Nat.not_lt.mpr h]

theorem sum_pad (f : ℕ → ℕ) {s U : ℕ} (hs : s ≤ U) :
    Readout.prefixSum (fun t => if t<s then f t else 0) U = Readout.prefixSum f s := by
  have aux {v : ℕ} (hv : v ≤ s) :
      Readout.prefixSum (fun t => if t<s then f t else 0) v = Readout.prefixSum f v := by
    induction v with
    | zero => rfl
    | succ v ih => simp [Readout.prefixSum, ih (by omega), show v<s by omega]
  induction U, hs using Nat.le_induction with
  | base => exact aux (by omega)
  | succ U h ih => simp [Readout.prefixSum, ih, Nat.not_lt.mpr h]

theorem product_constant (b e : ℕ) : productPrefix (fun _ => b) e = b^e := by
  induction e with
  | zero => rfl
  | succ e ih => rw [product_succ, ih, pow_succ]

theorem omitted_product {i n : ℕ} (hi : i<n) (f : ℕ → ℕ) :
    productPrefix (fun t => if t=i then 1 else f t) n * f i = productPrefix f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [product_succ, product_succ]
    by_cases h : n=i
    · subst i
      have prev : productPrefix (fun t => if t=n then 1 else f t) n = productPrefix f n := by
        unfold productPrefix
        congr 1
        apply List.map_congr_left
        intro t ht; simp [Nat.ne_of_lt (List.mem_range.mp ht)]
      simp [prev]
    · rw [if_neg h, Nat.mul_right_comm, ih (by omega)]

end DiophantineNP.WidthFormula
