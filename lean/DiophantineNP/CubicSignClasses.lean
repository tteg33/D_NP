import DiophantineNP.CubicUnitParity
import Mathlib.Data.Fintype.EquivFin

/-! # Unit square classes detected by the three real signs

Dirichlet parity gives at most eight representatives. A surjective three-sign
map forces each sign pattern to occur on exactly one representative. Matching
signs then identify the square class of an integral unit in the field.
-/
namespace DiophantineNP.Curve37.Kummer
open NumberField
open scoped NumberField
noncomputable section

private def unitValue (u : (𝓞 L)ˣ) : L := (u : 𝓞 L)

private theorem unit_ne_zero (u : (𝓞 L)ˣ) : unitValue u ≠ 0 :=
  (u.isUnit.map (algebraMap (𝓞 L) L)).ne_zero

private theorem unitValue_decomp {u a z : (𝓞 L)ˣ} (e : u=a*z*z) :
    unitValue u = unitValue a * (unitValue z)^2 := by
  rw [e]; simp [unitValue,pow_two,mul_assoc]

/-- All eight sign patterns occur on distinct torsion/fundamental-unit
parity representatives as soon as they occur on some integral units. -/
theorem bijective_unit_representative_signs (sign : L → Fin 3 → Bool)
    (stable : ∀ x z : L, z ≠ 0 → sign (x*z^2) = sign x)
    (onto : Function.Surjective (fun u : (𝓞 L)ˣ => sign ((u : 𝓞 L) : L))) :
    Function.Bijective (fun p : Parity => sign (((representative p : (𝓞 L)ˣ) : 𝓞 L) : L)) := by
  let f (p : Parity) := sign (unitValue (representative p))
  have surj : Function.Surjective f := by
    intro s
    obtain ⟨u,hu⟩ := onto s
    obtain ⟨p,w,he⟩ := unit_eq_representative_mul_square u
    change sign (unitValue u)=s at hu
    rw [unitValue_decomp he,stable _ _ (unit_ne_zero w)] at hu
    exact ⟨p,hu⟩
  have upper : Fintype.card Parity ≤ Fintype.card (Fin 3 → Bool) := by
    simpa [Fintype.card_fun] using card_parity_le_eight
  exact (Fintype.bijective_iff_surjective_and_card f).mpr
    ⟨surj, Nat.le_antisymm upper (Fintype.card_le_of_surjective f surj)⟩

/-- Two integral units with matching real signatures have a square quotient
in the field. The square root is itself the quotient of two integral units. -/
theorem unit_square_ratio_of_signs (sign : L → Fin 3 → Bool)
    (stable : ∀ x z : L, z ≠ 0 → sign (x*z^2) = sign x)
    (onto : Function.Surjective (fun u : (𝓞 L)ˣ => sign ((u : 𝓞 L) : L)))
    (u v : (𝓞 L)ˣ) (e : sign ((u : 𝓞 L) : L) = sign ((v : 𝓞 L) : L)) :
    IsSquare (((u : 𝓞 L) : L) / ((v : 𝓞 L) : L)) := by
  obtain ⟨p,a,ha⟩ := unit_eq_representative_mul_square u
  obtain ⟨q,b,hb⟩ := unit_eq_representative_mul_square v
  have hA := unitValue_decomp ha
  have hB := unitValue_decomp hb
  change sign (unitValue u) = sign (unitValue v) at e
  rw [hA,hB,stable _ _ (unit_ne_zero a),stable _ _ (unit_ne_zero b)] at e
  obtain rfl : p=q := (bijective_unit_representative_signs sign stable onto).1 e
  change IsSquare (unitValue u / unitValue v)
  refine (isSquare_iff_exists_sq _).mpr ⟨unitValue a / unitValue b,?_⟩
  rw [hA,hB,div_pow]
  field_simp [unit_ne_zero]

/-- The three real signs classify the square classes of integral units. -/
theorem unit_square_ratio_iff_signs (sign : L → Fin 3 → Bool)
    (stable : ∀ x z : L, z ≠ 0 → sign (x*z^2) = sign x)
    (onto : Function.Surjective (fun u : (𝓞 L)ˣ => sign ((u : 𝓞 L) : L)))
    (u v : (𝓞 L)ˣ) : IsSquare (((u : 𝓞 L) : L) / ((v : 𝓞 L) : L)) ↔
      sign ((u : 𝓞 L) : L) = sign ((v : 𝓞 L) : L) := by
  refine ⟨?_, unit_square_ratio_of_signs sign stable onto u v⟩
  intro h
  obtain ⟨z,hz⟩ := h.exists_sq
  change unitValue u / unitValue v = z^2 at hz
  have hn : z ≠ 0 := by
    rintro rfl
    have hpos := div_ne_zero (unit_ne_zero u) (unit_ne_zero v)
    exact hpos (by simpa using hz)
  have e : unitValue u = unitValue v*z^2 := by
    rw [←hz]; field_simp [unit_ne_zero]
  change sign (unitValue u) = sign (unitValue v)
  rw [e, stable _ _ hn]

end
end DiophantineNP.Curve37.Kummer
