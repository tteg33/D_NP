import DiophantineNP.CubicUnitSigns
import DiophantineNP.CubicSignClasses
import DiophantineNP.VerifiedCompilers

/-! # Descent from integral-unit square classes to the class equality -/
namespace DiophantineNP.Curve37.Kummer
open NumberField
open scoped NumberField

/-- A local arithmetic condition on each Kummer image. Every prime ideal
valuation is even if the image is a unit times a square. -/
def UnitTimesSquare (x : L) : Prop := ∃ (u : (𝓞 L)ˣ) (z : L), x = (u:L)*z^2

private theorem ratio_square {x y : L} (hx : x ≠ 0) (hy : y ≠ 0)
    (ux : UnitTimesSquare x) (uy : UnitTimesSquare y) (h : signs x = signs y) :
    IsSquare (x/y) := by
  obtain ⟨u,z,rfl⟩ := ux
  obtain ⟨v,w,rfl⟩ := uy
  have hz : z ≠ 0 := by rintro rfl; simp at hx
  have hw : w ≠ 0 := by rintro rfl; simp at hy
  rw [signs_sq_mul _ _ hz,signs_sq_mul _ _ hw] at h
  obtain ⟨q,hq⟩ := (unit_square_ratio_of_signs signs signs_sq_mul unit_signs_surjective u v h).exists_sq
  apply (isSquare_iff_exists_sq _).2
  refine ⟨q*(z/w),?_⟩
  rw [mul_pow,←hq,div_pow]
  ring

/-- The global part of rank-one descent. After local prime-ideal parity is supplied,
the computed real embeddings and Dirichlet's unit theorem determine the image mod squares. -/
theorem cyclic_of_unitTimesSquare (h : ∀ Q : E.Point, UnitTimesSquare (image Q)) : PowerTests.Cyclic := by
  apply cyclic_of_image_classes
  intro Q
  rcases point_signs Q with e|e
  · left
    have square := ratio_square (image_ne_zero Q) (one_ne_zero : (1:L)≠0) (h Q)
      (show UnitTimesSquare 1 from ⟨1,1,by simp⟩)
      (show signs (image Q) = signs 1 by rw [e]; funext i; simp [signs])
    simpa using square
  · right
    obtain ⟨z,hz⟩ := (ratio_square (image_ne_zero Q) (image_ne_zero P) (h Q) (h P) e).exists_sq
    refine (isSquare_iff_exists_sq _).2 ⟨z*image P,?_⟩
    rw [mul_pow,←hz]
    field_simp [image_ne_zero]

end DiophantineNP.Curve37.Kummer
