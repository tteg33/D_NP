import DiophantineNP.HABBoundedProduct
import DiophantineNP.HABProductEquivalence

/-! # Full product bits for polynomially bounded numerical products

There is a single source formula for each fixed exponent d. The number of
factors and their widths may grow without bound. The promise applies to
the numerical value of their complete product.
-/
namespace DiophantineNP.HABPolynomialProduct
open HAB Counting WidthFormula FiniteArithmeticGap HABPairInterpretation HABProductPadding

private abbrev total {U} (A : Matrix U) := ∏ r : Fin U, rowWord (A r)

private def Works (d : ℕ) (f : Form 1) := ∀ {U : ℕ}, 2≤U → ∀ (A : Matrix U) (j : Fin U),
  total A < U^d → (f.Holds A (fun _=>j) ↔ (total A).testBit j.val=true)

private noncomputable def square (f : Form 1) : Form 2 :=
  toSource (compile @cell f (fun _ => 0) (fun _ => 1))

private theorem square_correct {d} {f : Form 1} (hf : Works d f) {U : ℕ} (hU : 2≤U)
    (A : Matrix U) (hi lo : Fin U) (hp : total A<U^(d+d)) :
    (square f).Holds A (pairEnv hi lo) ↔ (total A).testBit (hi.val*U+lo.val)=true := by
  let B : Matrix (U*U) := fun r j => (factor A r.val).testBit j.val
  have rows (i : Fin (U*U)) : rowWord (B i)=factor A i.val := rowWord_natural (factor_fits hU A _)
  have fin_prod (n : ℕ) (g : ℕ→ℕ) : (∏ r : Fin n, g r.val)=productPrefix g n := by
    induction n with
    | zero => simp [productPrefix]
    | succ n ih => rw [Fin.prod_univ_castSucc,product_succ,←ih]; rfl
  have eq : total B=total A := by
    unfold total
    simp_rw [rows]
    exact (fin_prod _ _).trans (product_factor hU A)
  have fit : total B < (U*U)^d := by simpa [eq,mul_pow,pow_add] using hp
  have e := hf (by nlinarith : 2≤U*U) B (code hi lo) fit
  rw [square,toSource_correct,compile_correct @cell _ _ _ A B _ (fun rh rl ch cl s => cell_spec rh rl ch cl A s)]
  have hj : (code hi lo).val = hi.val*U+lo.val := by change lo.val+U*hi.val=_; ring
  simpa only [eq,hj] using e

private def low (f : Form 2) : Form 1 := .ex (.conj (indexNat 0 0) f)

private theorem low_correct {U} (f : Form 2) (A : Matrix U) (j : Fin U) :
    (low f).Holds A (fun _=>j) ↔ f.Holds A (pairEnv ⟨0,j.pos⟩ j) := by
  simp only [low,Form.Holds,indexNat_correct,Fin.cases_zero]
  constructor
  · rintro ⟨z,h,hf⟩
    have eq : z=⟨0,j.pos⟩ := Fin.ext h
    subst z; exact hf
  · intro h; exact ⟨⟨0,j.pos⟩,rfl,h⟩

private theorem bounded (k : ℕ) : ∃ f : Form 1, Works (2^k) f := by
  induction k with
  | zero =>
    obtain ⟨f,h⟩ := HABBoundedProduct.productBit_when_index_sized
    exact ⟨f,fun _ A j hp => h A j (by simpa using hp)⟩
  | succ k ih =>
    obtain ⟨f,hf⟩ := ih
    refine ⟨low (square f),fun hU A j hp => ?_⟩
    rw [low_correct]
    have hpow := square_correct hf hU A (⟨0,j.pos⟩ : Fin _) j (by simpa [pow_succ,Nat.mul_two] using hp)
    simpa only [Nat.zero_mul,Nat.zero_add] using hpow

/-- Corollary 6.3's two-coordinate output specification under the promise
that the product value is polynomially bounded in the universe size. -/
theorem polynomial_value (d : ℕ) : ∃ f : Form 2,
    ∀ {U : ℕ}, 2≤U → ∀ (A : Matrix U) (hi lo : Fin U),
      (∏ r : Fin U, rowWord (A r)) < U^d →
      (f.Holds A (pairEnv hi lo) ↔
        (∏ r : Fin U, rowWord (A r)).testBit (hi.val*U+lo.val)=true) := by
  obtain ⟨f,hf⟩ := bounded d
  refine ⟨square f,fun hU A hi lo hp => square_correct hf hU A hi lo (hp.trans_le ?_)⟩
  apply Nat.pow_le_pow_right (by omega)
  have := Nat.lt_two_pow_self (n:=d)
  omega

end DiophantineNP.HABPolynomialProduct
