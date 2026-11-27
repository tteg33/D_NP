import DiophantineNP.PowerPolynomial
import DiophantineNP.ScalarCertified

/-! # A signed integer power primitive for fixed scalar programs

The operation returns `a^(b.toNat)` and hence returns one on a negative
exponent. On a nonnegative exponent it checks the square of the output using
the bounded 37a1 power polynomial, then selects its sign using parity.
-/

namespace DiophantineNP.ScalarProgram

open MvPolynomial PowerTests Compiler
open PowerPolynomial (less leq eqn)

noncomputable section

private abbrev U := Option Bool ⊕ PowerPolynomial.Witness
private abbrev ZP := MvPolynomial U ℤ
local infixr:35 " ⋏ " => Compiler.Formula.both
local infixr:30 " ⋎ " => Compiler.Formula.either

private def baseP : ZP := X (.inl (some false))
private def expP : ZP := X (.inl (some true))
private def outP : ZP := X (.inl none)

private def squarePower : ZP :=
  bind₁ (Sum.elim ![baseP^2,expP,outP^2] (fun i => X (.inr i))) PowerPolynomial.polynomial

private def signTest : Compiler.Formula U :=
  ((leq 0 baseP ⋎ .divides 2 expP) ⋏ leq 0 outP) ⋎
    (less baseP 0 ⋏ .divides 2 (expP-1) ⋏ leq outP 0)

private def signedFormula : Compiler.Formula U :=
  (less expP 0 ⋏ eqn outP 1) ⋎ (.zero squarePower ⋏ signTest)

private theorem squarePower_value (a b y : ℤ) (w : PowerPolynomial.Witness → ℤ) :
    eval (Sum.elim (opInputs a b y) w) squarePower = PowerPolynomial.value (a^2) b (y^2) w := by
  change eval₂Hom (RingHom.id ℤ) _ _ = _
  rw [squarePower,eval₂Hom_bind₁]
  change eval _ _ = eval _ _
  congr 2
  funext i
  rcases i with i|i
  · fin_cases i <;> simp [baseP,expP,outP,opInputs]
  · simp

private def Signs (a b y : ℤ) : Prop :=
  ((0 ≤ a ∨ 2 ∣ b) ∧ 0 ≤ y) ∨ (a < 0 ∧ 2 ∣ b-1 ∧ y ≤ 0)

private theorem signedFormula_iff (a b y : ℤ) (w : PowerPolynomial.Witness → ℤ) :
    signedFormula.Holds (Sum.elim (opInputs a b y) w) ↔
      (b<0 ∧ y=1) ∨ (PowerPolynomial.value (a^2) b (y^2) w = 0 ∧ Signs a b y) := by
  simp [signedFormula,signTest,Formula.Holds,squarePower_value,Signs,expP,baseP,outP,opInputs]

private theorem correct_sign (a : ℤ) (n : ℕ) : Signs a n (a^n) := by
  by_cases ha : 0 ≤ a
  · exact Or.inl ⟨Or.inl ha,pow_nonneg ha n⟩
  rcases Nat.even_or_odd n with hn | hn
  · have hdiv := even_iff_two_dvd.mp hn
    exact Or.inl ⟨Or.inr (by exact_mod_cast hdiv),hn.pow_nonneg _⟩
  · obtain ⟨k,hk⟩ := hn
    exact Or.inr ⟨by omega,⟨k,by omega⟩,(show Odd n from ⟨k,hk⟩).pow_nonpos (by omega)⟩

private theorem sign_unique {a y : ℤ} {n : ℕ} (hs : Signs a n y)
    (hh : y^2 = (a^2)^n) : y = a^n := by
  have heq : y^2 = (a^n)^2 := by simpa only [← pow_mul, Nat.mul_comm 2 n] using hh
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ heq with h | h
  · exact h
  · rcases hs with ⟨ha|hn,hy⟩ | ⟨ha,hn,hy⟩
    · have := pow_nonneg ha n; omega
    · have hEven : Even n := Nat.even_iff.mpr (by rcases hn with ⟨k,hk⟩; omega)
      have := hEven.pow_nonneg a; omega
    · have hOdd : Odd n := Nat.odd_iff.mpr (by rcases hn with ⟨k,hk⟩; omega)
      have := hOdd.pow_nonpos ha.le; omega

private theorem signed_sound (hc : Cyclic) (hq : Quadratic) (a b y : ℤ) (w : PowerPolynomial.Witness → ℤ)
    (h : signedFormula.Holds (Sum.elim (opInputs a b y) w)) : y=a^b.toNat := by
  rcases (signedFormula_iff ..).1 h with ⟨hb,rfl⟩ | ⟨hp,hs⟩
  · simp [Int.toNat_of_nonpos hb.le]
  · obtain ⟨g,n,hg,rfl,hy⟩ := (PowerPolynomial.exact_over_integers hc hq _ _ _).1 ⟨w,hp⟩
    simp only [Int.toNat_natCast]
    apply sign_unique hs
    rw [hg, hy, Nat.cast_pow]

private def lengthBudget (a b y : ℤ) := signedBits a + signedBits b + signedBits y + 2

private lemma input_bound (a b : ℤ) (n : ℕ) (hb : b=(n:ℤ)) :
    inputBits (a.natAbs^2) n ((a.natAbs^2)^n) ≤ 5*lengthBudget a b (a^n) := by
  subst b
  let L := lengthBudget a (n:ℤ) (a^n)
  have hL : 1 ≤ L := by dsimp [L,lengthBudget]; omega
  have hmag (z : ℤ) (hz : signedBits z ≤ L) : z.natAbs ≤ 2^L :=
    Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (by dsimp [signedBits,bits] at hz; omega))
  have ha := hmag a (by dsimp [L,lengthBudget]; omega)
  have he := hmag n (by dsimp [L,lengthBudget]; omega)
  have hy := hmag (a^n) (by dsimp [L,lengthBudget]; omega)
  have hsq (z : ℕ) (hz : z ≤ 2^L) : z^2 ≤ 2^(2*L) := by
    simpa only [Nat.mul_comm 2 L,pow_mul] using Nat.pow_le_pow_left hz 2
  have hp : (a.natAbs^2)^n = ((a^n).natAbs)^2 := by
    simp only [Int.natAbs_pow, ← pow_mul, Nat.mul_comm 2 n]
  have hd : n ≤ 2^(2*L) :=
    he.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have ht : 2 ≤ (2:ℕ)^(2*L) := by simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) (show 1≤2*L by omega))
  have hsum : 2 + a.natAbs^2 + n + (a.natAbs^2)^n ≤ 2^(2*L+2) := by
    rw [hp,pow_add]
    have hw := hsq _ ha
    have hv := hsq _ hy
    omega
  have hlog : (2+a.natAbs^2+n+(a.natAbs^2)^n).log2 ≤ 2*L+2 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp <|
      (Nat.log2_self_le (by omega)).trans hsum
  change _ + 1 ≤ 5*L
  omega

private theorem primary_complete (hc : Cyclic) (hq : Quadratic) :
    ∃ K : ℕ, ∀ a b : ℤ, ∃ w : PowerPolynomial.Witness → ℤ,
      intCost w ≤ K*(lengthBudget a b (a^b.toNat))^4 ∧
      signedFormula.Holds (Sum.elim (opInputs a b (a^b.toNat)) w) := by
  obtain ⟨C,hC⟩ := PowerPolynomial.complete_quartic hc hq
  refine ⟨C*625+2*Fintype.card PowerPolynomial.Witness,fun a b => ?_⟩
  let n := b.toNat
  let L := lengthBudget a b (a^n)
  have hL : 1 ≤ L := by dsimp [L,lengthBudget]; omega
  have hp : 1 ≤ L^4 := Nat.one_le_pow _ _ hL
  by_cases hb : b < 0
  · refine ⟨fun _ => 0,?_,(signedFormula_iff ..).2 (Or.inl ⟨hb,by simp [Int.toNat_of_nonpos hb.le]⟩)⟩
    have hc0 : intCost (fun _ : PowerPolynomial.Witness => (0:ℤ)) = Fintype.card PowerPolynomial.Witness*2 := by
      simp [intCost,bits]
    rw [hc0]
    change _ ≤ _ * L^4
    exact (by omega : Fintype.card PowerPolynomial.Witness*2 ≤ C*625+2*Fintype.card PowerPolynomial.Witness).trans
      (Nat.le_mul_of_pos_right _ hp)
  have he : b = (n:ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  obtain ⟨w,hw,hcost⟩ := hC (a.natAbs^2) n
  refine ⟨w,?_,(signedFormula_iff ..).2 (Or.inr ⟨?_,?_⟩)⟩
  · have hh := Nat.pow_le_pow_left (input_bound a b n he) 4
    change _ ≤ _*L^4
    calc
      _ ≤ C*(inputBits (a.natAbs^2) n ((a.natAbs^2)^n))^4 := hcost
      _ ≤ C*(5*L)^4 := Nat.mul_le_mul_left C hh
      _ ≤ _ := by rw [mul_pow]; norm_num; nlinarith
  · have hs (z : ℤ) : ((z.natAbs^2 : ℕ):ℤ) = z^2 := by simp
    have hpow : (((a.natAbs^2)^n:ℕ):ℤ) = (a^n)^2 := by
      rw [Nat.cast_pow,hs,←pow_mul,←pow_mul,Nat.mul_comm 2 n]
    simpa only [hs,hpow,←he] using hw
  · rw [he]; exact correct_sign a n

/-- The signed power operation required by the integer evaluators. -/
def signedPower (hc : Cyclic) (hq : Quadratic) : Operation :=
  Operation.ofShortFormula (fun a b => a^b.toNat) signedFormula (signed_sound hc hq)
    (by obtain ⟨K,hK⟩ := primary_complete hc hq; exact ⟨K,4,hK⟩)

@[simp] theorem signedPower_apply (hc : Cyclic) (hq : Quadratic) (a b : ℤ) :
    (signedPower hc hq).apply a b = a^b.toNat := rfl

end
end DiophantineNP.ScalarProgram
