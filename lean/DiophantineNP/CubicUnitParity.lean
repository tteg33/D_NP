import DiophantineNP.CubicField
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-! # At most eight unit square classes in the cubic field

Dirichlet's unit theorem writes an integral unit as a root of unity times powers
of the fundamental units. Odd field degree reduces the torsion unit to a sign.
Dividing each integral exponent by two leaves at most two free parity bits. -/
namespace DiophantineNP.Curve37.Kummer

open NumberField NumberField.InfinitePlace
open scoped NumberField BigOperators
noncomputable section

abbrev Parity := Bool × (Fin (NumberField.Units.rank L) → Bool)

theorem unit_rank_le_two : NumberField.Units.rank L ≤ 2 := by
  have h := card_add_two_mul_card_eq_rank L
  rw [field_degree] at h
  rw [NumberField.Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

theorem card_parity_le_eight : Fintype.card Parity ≤ 8 := by
  have h := unit_rank_le_two
  change Fintype.card (Bool × (Fin (NumberField.Units.rank L) → Bool)) ≤ 8
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, Fintype.card_fin]
  have h' : 2 ^ NumberField.Units.rank L ≤ (2:ℕ)^2 := Nat.pow_le_pow_right (by decide) h
  omega

/-- A unit with the selected torsion sign and fundamental-unit parities. -/
def representative (p : Parity) : (𝓞 L)ˣ :=
  (if p.1 then -1 else 1) * ∏ i, if p.2 i then NumberField.Units.fundSystem L i else 1

theorem unit_eq_representative_mul_square (u : (𝓞 L)ˣ) :
    ∃ (p : Parity) (w : (𝓞 L)ˣ), u = representative p * w * w := by
  classical
  obtain ⟨⟨ζ,e⟩,hu,_⟩ := NumberField.Units.exist_unique_eq_mul_prod L u
  have hodd : Odd (Module.finrank ℚ L) := by rw [field_degree]; decide
  obtain ⟨b,hb⟩ : ∃ b : Bool, (ζ : (𝓞 L)ˣ) = if b then -1 else 1 := by
    rcases NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank hodd ζ with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  let bits := fun i => decide (e i % 2 = 1)
  let f := NumberField.Units.fundSystem L
  let w := ∏ i, (f i)^(e i/2)
  have he (i) : (f i)^(e i) = (if bits i then f i else 1) * (f i)^(e i/2) * (f i)^(e i/2) := by
    calc
      (f i)^(e i) = (f i)^((if e i % 2=1 then (1:ℤ) else 0) + e i/2 + e i/2) := by
        congr 1; split <;> omega
      _ = _ := by rw [zpow_add,zpow_add]; by_cases h : e i % 2=1 <;> simp [h,bits]
  refine ⟨(b,bits),w,?_⟩
  change u = (ζ : (𝓞 L)ˣ) * ∏ i, f i^(e i) at hu
  rw [hu,hb]
  simp_rw [he]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  simp only [representative,w,f,mul_assoc]

end
end DiophantineNP.Curve37.Kummer
