import DiophantineNP.HABPolylogProduct
import DiophantineNP.HABShortProducts
import DiophantineNP.HABLargePrimeProduct

/-! # Closing the short modular-product premise in the original language

The geometric quotient calculation requires polylogarithmic bits only at
one fixed exponent, 60. The lower-scale CRT construction supplies those
bits independently of prime powering.
-/
namespace DiophantineNP.HABModularArithmetic

noncomputable def shortProducts : HABPowerReduction.ShortProducts :=
  HABShortProducts.ofPolylogProduct (HABPolylogProduct.threshold 60) (HABPolylogProduct.formula 60)
    (fun large f fits hp j => HABPolylogProduct.formula_correct 60 large f fits hp j)

/-- One finite order/BIT/majority formula for modular powers at all represented primes. -/
theorem prime_power :
    ∃ φ : HAB.Form 4, ∀ {U : ℕ} (A : HAB.Matrix U) (a r b p : Fin U),
      p.val.Prime → (φ.Holds A ![a,r,b,p] ↔ a.val^r.val ≡ b.val [MOD p.val]) :=
  ⟨HABPowerReduction.primePOW shortProducts,
    fun A a r b p hp => HABPowerReduction.primePOW_correct shortProducts A a r b p hp⟩

end DiophantineNP.HABModularArithmetic
