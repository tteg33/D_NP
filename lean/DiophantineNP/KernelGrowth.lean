import DiophantineNP.KernelEvaluation

/-! # Polynomial Laurent bounds for the complete Fourier scalar -/
namespace DiophantineNP.FormulaLaurent
open Counting ConcreteGrid LaurentBounds
noncomputable section

private theorem polyJ : Poly J := ((poly_const 2).mul polyRadius).add (poly_const 1)
private theorem polyStride : Poly stride :=
  (poly_const 4).mul (polyFixedPow (((poly_const 2).mul polyRadius).add (poly_const 2)) 30)

private theorem mono_adm {d : ℕ} (j : Fin d) (v : ℤ) : Admissible (fun _ => mono j v) :=
  .monomial _ (poly_const _)

private theorem centered_adm {d : ℕ} (j : Fin d) :
    Admissible (fun u => centeredExpr (u+1) j) :=
  adm_sub (shifted (xLeaf_admissible j)) (shifted (RatBits.natCast (polyToBits polyRadius)).admissible)

private theorem l_adm {d : ℕ} (z w u v : Fin d) : Admissible (fun n => LExpr (n+1) z w u v) := by
  apply adm_tail
  apply adm_normalize
  apply adm_sub (adm_const (1/4))
  apply Admissible.pow _ _ (poly_const 2)
  apply adm_sub _ (centered_adm v)
  apply adm_sub (.mul (shifted (xLeaf_admissible z)) (centered_adm w))
  exact .mul (shifted (RatBits.natCast (polyToBits polyJ)).admissible) (centered_adm u)

private theorem s_adm {d : ℕ} (w v : Fin d) : Admissible (fun n => SExpr (n+1) w v) :=
  adm_tail (.mul (.mul (adm_sub (mono_adm w 1) (mono_adm w (-1)))
    (adm_sub (mono_adm v 1) (mono_adm v (-1)))) (adm_const (-1/16)))

private theorem carrier_adm {d : ℕ} (w v : Fin d) : Admissible (fun n => carrierExpr (n+1) w v) :=
  shifted (.mul (.pow (mono_adm v 1) stride polyStride) (.geometric w stride J polyStride polyJ))

theorem kernelExpr_admissible {k : ℕ} (φ : Formula (k+1)) (t : ∀ n, Fin k → Fin (n+1)) :
    Admissible (fun n => kernelExpr φ (t n)) := by
  have win (j : Fin (4+depth φ)) : Admissible (fun n => tail (n+1) (yLeaf (n+1) j)) :=
    adm_tail (shifted (yLeaf_admissible j))
  exact .mul (.mul (.mul (.mul (.mul (.mul (.mul (truthExpr_admissible φ t) (win _))
    (win _)) (win _)) (win _)) (l_adm _ _ _ _)) (s_adm _ _)) (carrier_adm _ _)

theorem packedExpr_admissible {k : ℕ} (φ : Formula (k+1)) (t : ∀ n, Fin k → Fin (n+1)) :
    Admissible (fun n => packedExpr φ (t n)) := by
  have ratio := ((RatBits.natCast (polyToBits polySize)).pow (poly_const 4)).div
     ((RatBits.const 8).mul (RatBits.natCast (polyToBits polyJ)))
  exact .mul (shifted ratio.admissible) (.project (.project (.project
    (.project (kernelExpr_admissible φ t) _ _) _ _) _ _) _ _)

/-- The exponent depends only on the formula. The denominator and height are
bounded in binary length, while the exponent radius is bounded in value. -/
theorem packedExpr_uniform_size {k : ℕ} (φ : Formula (k+1)) :
    ∃ c : ℕ, ∀ U : ℕ, 0 < U → ∀ t : Fin k → Fin U,
      let b := (packedExpr φ t).bounds
      b.radius + (b.denominator.log2+1) + (b.height.log2+1) ≤ (U+1)^c := by
  let cost (u : ℕ) (t : Fin k → Fin (u+1)) :=
    let b := (packedExpr φ t).bounds
    b.radius + (b.denominator.log2+1) + (b.height.log2+1)
  obtain ⟨c, h⟩ := uniform_bound cost (fun t => (packedExpr_admissible φ t).total_size)
  refine ⟨c, ?_⟩
  rintro (_ | u) hu t
  · omega
  · exact h u t

end
end DiophantineNP.FormulaLaurent
