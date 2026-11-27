import DiophantineNP.CubicIdeals
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Rat.Lemmas

/-! # Primitive integral numerator and square denominator of the Kummer image

For X=A/B in lowest terms the elliptic equation implies that
(A³−16AB²+16B³)B is an integer square. Coprimality makes the absolute
norm of the integral numerator a square; positivity does the same for B. -/
namespace DiophantineNP.Curve37.Kummer

open NumberField WeierstrassCurve
open scoped NumberField
noncomputable section

private def normForm (a b : ℤ) : ℤ := a^3-16*a*b^2+16*b^3

private theorem primitive_norm_coprime {a b : ℤ} (h : IsCoprime a b) : IsCoprime (normForm a b) b := by
  rw [show normForm a b = a^3 + (-16*a*b+16*b^2)*b by unfold normForm; ring]
  exact (h.pow_left (m:=3)).add_mul_right_left _

theorem norm_linearInteger (a b : ℤ) : Algebra.norm ℤ (linearInteger a b) = a^3-16*a*b^2+16*b^3 := by
  apply Int.cast_injective (α:=ℚ)
  rw [Algebra.coe_norm_int]
  have represent : ((linearInteger a b : 𝓞 L) : L) = triple (a:ℚ) (-2*(b:ℚ)) 0 := by
    simp [linearInteger,triple,generatorInteger]
    rw [show (algebraMap (𝓞 L) L) 2 = (2:L) by exact map_ofNat _ _]
    ring
  rw [represent,norm_triple]
  push_cast
  ring

private theorem primitive (X : ℚ) : IsCoprime X.num (X.den:ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  exact X.reduced

private theorem num_relation (X : ℚ) : (X.num : ℚ) = X*(X.den:ℚ) :=
  (div_eq_iff (by exact_mod_cast X.den_ne_zero)).1 X.num_div_den

theorem square_norm_and_den {X Y : ℚ} (h : Y^2=X^3-16*X+16) :
    IsSquare (Ideal.absNorm (Ideal.span {linearInteger X.num (X.den:ℤ)})) ∧
    ∃ d : ℤ, (X.den:ℤ)=d^2 := by
  let F := normForm X.num (X.den:ℤ)
  let B : ℤ := X.den
  have hs : IsSquare (F*B) := by
    apply Rat.isSquare_intCast_iff.mp
    refine ⟨Y*(X.den:ℚ)^2,?_⟩
    dsimp [F,B,normForm]
    push_cast
    rw [num_relation X]
    linear_combination -(X.den:ℚ)^4 * h
  obtain ⟨c,hc⟩ := hs
  rw [←sq] at hc
  have hcop : IsCoprime F B := primitive_norm_coprime (primitive X)
  obtain ⟨n,hn⟩ := Int.sq_of_isCoprime hcop hc
  obtain ⟨d,hd⟩ := Int.sq_of_isCoprime hcop.symm (by rw [mul_comm]; exact hc)
  have hpos : 0 < B := by dsimp [B]; exact_mod_cast X.den_pos
  constructor
  · rw [Ideal.absNorm_span_singleton,norm_linearInteger]
    change IsSquare F.natAbs
    refine ⟨n.natAbs,?_⟩
    rcases hn with hn | hn <;> simp [hn,pow_two,Int.natAbs_mul]
  · exact ⟨d,hd.resolve_right (by intro he; nlinarith [sq_nonneg d])⟩

private theorem denominator_times_triple (X : ℚ) :
    (X.den:L) * triple X (-2) 0 = (linearInteger X.num (X.den:ℤ) : L) := by
  have hq : ((X.num:ℤ):L) = (X:L)*(X.den:L) := by exact_mod_cast num_relation X
  simp [linearInteger,triple,generatorInteger]
  rw [show (algebraMap (𝓞 L) L) 2 = (2:L) by exact map_ofNat _ _]
  linear_combination -hq

/-- After factoring the primitive integral numerator, its square denominator
is absorbed into the square factor in the cubic field. -/
theorem image_unit_square_of_linear
    (linear_square : ∀ {a b : ℤ}, IsCoprime a b →
      IsSquare (Ideal.absNorm (Ideal.span {linearInteger a b})) →
      ∃ (u : (𝓞 L)ˣ) (v : 𝓞 L), linearInteger a b = (u : 𝓞 L)*v^2)
    (Q : E.Point) : ∃ (u : (𝓞 L)ˣ) (z : L), image Q = (u : 𝓞 L)*z^2 := by
  cases Q with
  | zero => exact ⟨1,1,by simp [image]⟩
  | @some x y hp =>
    let X := 4*x
    let Y := 8*y+4
    have h : Y^2=X^3-16*X+16 := by dsimp [Y,X]; linear_combination 64 * curve_eq hp
    obtain ⟨hn,d,hd⟩ := square_norm_and_den h
    obtain ⟨u,v,hv⟩ := linear_square (primitive X) hn
    have hD : (X.den:L)=(d:L)^2 := by exact_mod_cast hd
    have hdne : (d:L) ≠ 0 := by
      intro hh; rw [hh,zero_pow (by decide)] at hD
      exact (Nat.cast_ne_zero.mpr X.den_ne_zero) hD
    refine ⟨u,(v:L)/(d:L),?_⟩
    have hc := denominator_times_triple X
    rw [hv,hD] at hc
    change (d:L)^2 * triple X (-2) 0 = ((u:𝓞 L):L)*(v:L)^2 at hc
    change triple X (-2) 0 = ((u:𝓞 L):L)*((v:L)/(d:L))^2
    field_simp
    linear_combination hc

/-- Every rational point has Kummer image an integral unit times a square. -/
theorem image_eq_unit_mul_square (Q : E.Point) :
    ∃ (u : (𝓞 L)ˣ) (z : L), image Q = (u : 𝓞 L)*z^2 :=
  image_unit_square_of_linear (fun hc hn => linear_unit_square hc hn) Q

end
end DiophantineNP.Curve37.Kummer
