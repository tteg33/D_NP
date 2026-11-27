import DiophantineNP.CubicField
import DiophantineNP.CubicRealPlaces

/-! # Signatures of explicit integral units in the cubic field -/
namespace DiophantineNP.Curve37.Kummer
open NumberField
open scoped NumberField
noncomputable section

private def u : (𝓞 L)ˣ where
  val := generatorInteger-1
  inv := generatorInteger^2+generatorInteger-3
  val_inv := by linear_combination cubic_integral
  inv_val := by linear_combination cubic_integral

private def v : (𝓞 L)ˣ where
  val := generatorInteger^2-3
  inv := 1-2*generatorInteger-generatorInteger^2
  val_inv := by linear_combination (-generatorInteger-2)*cubic_integral
  inv_val := by linear_combination (-generatorInteger-2)*cubic_integral

private def unitSigns (z : (𝓞 L)ˣ) : SignPattern := signs (z : L)

private theorem sign_mul (z w : (𝓞 L)ˣ) (i : Fin 3) :
    unitSigns (z*w) i = xor (unitSigns z i) (unitSigns w i) := by
  have hz : roots.emb i (z : L) ≠ 0 := (_root_.map_ne_zero _).mpr (NumberField.Units.coe_ne_zero z)
  have hw : roots.emb i (w : L) ≠ 0 := (_root_.map_ne_zero _).mpr (NumberField.Units.coe_ne_zero w)
  change decide (roots.emb i ((z:L)*(w:L))<0) = _
  rw [map_mul]
  simp only [unitSigns,signs]
  rcases lt_or_gt_of_ne hz with h | h <;> rcases lt_or_gt_of_ne hw with k | k
  all_goals simp [h,k,h.not_gt,k.not_gt,mul_neg_iff,lt_asymm h,lt_asymm k]

private theorem signs_one : unitSigns 1 = fun _ => false := by funext i; simp [unitSigns,signs]
private theorem signs_neg : unitSigns (-1) = fun _ => true := by funext i; simp [unitSigns,signs]

private theorem signs_u : unitSigns u = ![true,true,false] := by
  funext i
  change decide (roots.emb i (θ-1) < 0) = _
  simp only [map_sub,map_one,RealRoots.emb_theta]
  fin_cases i <;> dsimp [RealRoots.root] <;> first
  | exact decide_eq_true (by linarith [roots.ha.2,roots.hb.2])
  | exact decide_eq_false (by linarith [roots.hc.1])

private theorem signs_v : unitSigns v = ![false,true,true] := by
  funext i
  change decide (roots.emb i (θ^2-3) < 0) = _
  simp only [map_sub,map_pow,map_ofNat,RealRoots.emb_theta]
  fin_cases i <;> dsimp [RealRoots.root] <;> first
  | exact decide_eq_false (by nlinarith [roots.ha.2,sq_nonneg (roots.a+2)])
  | exact decide_eq_true (by nlinarith [roots.hb.1,roots.hb.2,mul_nonneg (show 0≤roots.b+3/4 by linarith [roots.hb.1]) (sub_nonneg.mpr roots.hb.2)])
  | exact decide_eq_true (by nlinarith [roots.hc.1,roots.hc.2,mul_nonneg (show 0≤roots.c+17/10 by linarith [roots.hc.1]) (sub_nonneg.mpr roots.hc.2)])

private def takeUnit (u : (𝓞 L)ˣ) (b : Bool) : (𝓞 L)ˣ := if b then u else 1

private theorem signs_take (w : (𝓞 L)ˣ) (b : Bool) (i : Fin 3) :
    unitSigns (takeUnit w b) i = (b && unitSigns w i) := by cases b <;> simp [takeUnit,signs_one]

/-- The three displayed integral units give every signature, in the fixed root order. -/
theorem unit_signs_surjective :
    Function.Surjective (fun z : (𝓞 L)ˣ => signs (z:L)) := by
  intro t
  let b := t 0
  let c := t 1
  let d := t 2
  refine ⟨takeUnit (-1) (xor b (xor c d)) * takeUnit u (xor c d) * takeUnit v (xor b c), ?_⟩
  funext i
  change unitSigns _ i = t i
  simp only [sign_mul,signs_take,signs_neg,signs_u,signs_v]
  fin_cases i <;> dsimp <;> dsimp [b,c,d] <;> cases t 0 <;> cases t 1 <;> cases t 2 <;> rfl

end
end DiophantineNP.Curve37.Kummer
