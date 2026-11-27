import DiophantineNP.CurveKummer
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! # Arithmetic of the cubic field used in the descent on 37a1 -/
namespace DiophantineNP.Curve37.Kummer

noncomputable section
open Polynomial NumberField WeierstrassCurve
open scoped Matrix NumberField

instance : NumberField L := {to_finiteDimensional := Module.Finite.of_basis basis}

theorem field_degree : Module.finrank ℚ L=3 := by
  rw [Module.finrank_eq_card_basis basis]; rfl

private theorem coords (a b c : ℚ) (i : Fin 3) :
    basis.repr (triple a b c) i = ![a,b,c] i := by
  rw [repr_triple]
  simp only [map_sum,map_smul,Module.Basis.repr_self,Finset.sum_apply',Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem mul_matrix (a b c : ℚ) :
    Algebra.leftMulMatrix basis (triple a b c) =
      !![a,-2*c,-2*b; b,a+4*c,4*b-2*c; c,b,a+4*c] := by
  have h₁ : triple a b c*θ=triple (-2*c) (a+4*c) b := by
    dsimp [triple]; push_cast; linear_combination (c:L)*theta_cube
  have h₂ : triple a b c*θ^2=triple (-2*b) (4*b-2*c) (a+4*c) := by
    dsimp [triple]; push_cast; linear_combination ((b:L)+(c:L)*θ)*theta_cube
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul,basis_apply]
  fin_cases j <;> simp only [Fin.reduceFinMk,pow_zero,mul_one,pow_one] <;>
    first | rw [h₁,coords] | rw [h₂,coords] | rw [coords]
  all_goals fin_cases i <;> rfl

theorem norm_triple (a b c : ℚ) : Algebra.norm ℚ (triple a b c) =
    a^3+8*a^2*c-4*a*b^2+6*a*b*c+16*a*c^2-2*b^3+8*b*c^2+4*c^3 := by
  rw [Algebra.norm_eq_matrix_det basis,mul_matrix,Matrix.det_fin_three]
  simp; ring

theorem trace_triple (a b c : ℚ) : Algebra.trace ℚ L (triple a b c) = 3*a+8*c := by
  rw [Algebra.trace_eq_matrix_trace basis,mul_matrix,Matrix.trace,Fin.sum_univ_three]
  simp; ring

theorem norm_image {x y : ℚ} (hp : E.Nonsingular x y) :
    Algebra.norm ℚ (image (Affine.Point.some hp))=(8*y+4)^2 := by
  rw [image,norm_triple]; linear_combination -64 * curve_eq hp

def generatorInteger : 𝓞 L :=
  ⟨θ, ⟨(X^3-4*X+2 : ℤ[X]), by monicity <;> decide, by simp⟩⟩

private theorem theta_norm : Algebra.norm ℤ generatorInteger = -2 := by
  apply Int.cast_injective (α:=ℚ)
  rw [Algebra.coe_norm_int]
  have he : (generatorInteger:L) = triple 0 1 0 := by simp [generatorInteger,triple]
  rw [he,norm_triple]; norm_num

theorem norm_generator_ideal :
    Ideal.absNorm (Ideal.span ({generatorInteger} : Set (𝓞 L))) = 2 := by
  rw [Ideal.absNorm_span_singleton,theta_norm]; decide

theorem cubic_integral : generatorInteger^3=4*generatorInteger-2 := by
  apply Subtype.ext; change θ^3=4*θ-2; exact theta_cube

private def powerFamily (j : Fin 3) : 𝓞 L := generatorInteger^j.val

private theorem tr_pow (n : Fin 5) :
    Algebra.trace ℚ L (θ^n.val) = ![3,0,8,-6,32] n := by
  have h0 : (1:L) = triple 1 0 0 := by simp [triple]
  have h1 : θ = triple 0 1 0 := by simp [triple]
  have h2 : θ^2 = triple 0 0 1 := by simp [triple]
  have h3 : θ^3 = triple (-2) 4 0 := by simp [triple]; ring
  have h4 : θ^4 = triple 0 (-2) 4 := by
    dsimp [triple]; push_cast; linear_combination θ*theta_cube
  fin_cases n <;> simp only [Fin.reduceFinMk,pow_zero,pow_one]
  all_goals first | rw [h0,trace_triple] | rw [h1,trace_triple] | rw [h2,trace_triple] |
    rw [h3,trace_triple] | rw [h4,trace_triple]
  all_goals norm_num <;> rfl

theorem power_discriminant : Algebra.discr ℤ powerFamily=148 := by
  have hm : Algebra.traceMatrix ℤ powerFamily = !![3,0,8; 0,8,-6; 8,-6,32] := by
    ext i j
    rw [Algebra.traceMatrix_apply,Algebra.traceForm_apply]
    apply Int.cast_injective (α:=ℚ)
    rw [Algebra.coe_trace_int]
    change Algebra.trace ℚ L (θ^i.val*θ^j.val) = _
    rw [←pow_add]
    let k : Fin 5 := ⟨i.val+j.val,by omega⟩
    have h := tr_pow k
    change Algebra.trace ℚ L (θ^(i.val+j.val))=_ at h
    rw [h]
    fin_cases i <;> fin_cases j <;> norm_num [k]
  rw [Algebra.discr_def,hm,Matrix.det_fin_three]; decide

theorem index_discriminant : ∃ d : ℤ, 148=d^2*NumberField.discr L := by
  let b := (RingOfIntegers.basis L).reindex ((NumberField.integralBasis L).indexEquiv basis)
  refine ⟨(b.toMatrix powerFamily).det,?_⟩
  rw [←NumberField.discr_eq_discr L b,←Algebra.discr_of_matrix_vecMul,
    Module.Basis.toMatrix_map_vecMul,power_discriminant]

theorem abs_discriminant_bound : |NumberField.discr L| ≤ 148 := by
  obtain ⟨d,hd⟩ := index_discriminant
  have hdiv : NumberField.discr L ∣ 148 := ⟨d^2,by rw [hd,mul_comm]⟩
  exact Int.le_of_dvd (by decide) ((abs_dvd _ _).2 hdiv)

theorem norm_two_unique (I : Ideal (𝓞 L)) (hi : Ideal.absNorm I=2) :
    Ideal.span {generatorInteger}=I := by
  have primeI := Ideal.isPrime_of_irreducible_absNorm (I:=I) (hi ▸ Nat.prime_two)
  have primeθ := Ideal.isPrime_of_irreducible_absNorm (I:=Ideal.span {generatorInteger})
    (norm_generator_ideal ▸ Nat.prime_two)
  have nt := norm_generator_ideal
  apply (primeθ.isMaximal (by intro h; rw [h,Ideal.absNorm_bot] at nt; contradiction)).eq_of_le primeI.ne_top
  apply (Ideal.span_singleton_le_iff_mem _).2
  apply primeI.mem_of_pow_mem 3
  have h2 := Ideal.absNorm_mem I
  rw [hi] at h2
  rw [cubic_integral,show 4*generatorInteger-2 = (2*generatorInteger-1)*2 by ring]
  exact I.mul_mem_left _ h2

/-- The cubic has no root over the field of three elements. -/
theorem norm_three_impossible (I : Ideal (𝓞 L)) (hi : Ideal.absNorm I=3) : False := by
  classical
  have hp : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hi]; exact Nat.prime_three)
  haveI : I.IsMaximal := hp.isMaximal (by intro h; rw [h,Ideal.absNorm_bot] at hi; contradiction)
  letI := Ideal.Quotient.field I
  haveI : Finite (𝓞 L ⧸ I) := (Ideal.absNorm_ne_zero_iff I).mp (hi ▸ by decide)
  letI := Fintype.ofFinite (𝓞 L ⧸ I)
  have hc : Fintype.card (𝓞 L ⧸ I)=3 := by rw [←Nat.card_eq_fintype_card]; exact hi
  let t := Ideal.Quotient.mk I generatorInteger
  have hf : t^3=t := by simpa only [hc] using FiniteField.pow_card t
  have he : t^3=4*t-2 := by
    simpa only [map_pow,map_sub,map_mul,map_ofNat,t] using congrArg (Ideal.Quotient.mk I) cubic_integral
  have hz : (3 : 𝓞 L ⧸ I)=0 := by
    have hm := Ideal.absNorm_mem I
    rw [hi] at hm
    simpa only [map_ofNat] using (Ideal.Quotient.eq_zero_iff_mem).mpr hm
  have h2 : (2 : 𝓞 L ⧸ I)=0 := by linear_combination he - hf + t*hz
  exact one_ne_zero (show (1 : 𝓞 L ⧸ I)=0 by linear_combination hz-h2)

/-- Minkowski's class bound is below four even using only the general bound
of one complex place for a cubic. The only possible proper ideal norms are
two and three, which the preceding two lemmas settle. -/
theorem integers_principal : IsPrincipalIdealRing (𝓞 L) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le
  intro I hI
  rw [field_degree] at hI
  have hc := InfinitePlace.card_add_two_mul_card_eq_rank L
  rw [field_degree] at hc
  have hcomplex : InfinitePlace.nrComplexPlaces L ≤ 1 := by omega
  have hpow : (4/Real.pi)^InfinitePlace.nrComplexPlaces L ≤ 4/3 := by
    have hp := Real.pi_gt_three
    interval_cases h : InfinitePlace.nrComplexPlaces L
    · norm_num
    · rw [pow_one]
      rw [div_le_div_iff₀ Real.pi_pos (by norm_num : (0:ℝ)<3)]
      linarith
  have hdisc : |(NumberField.discr L : ℝ)| ≤ 148 := by exact_mod_cast abs_discriminant_bound
  have hs : Real.sqrt |(NumberField.discr L : ℝ)| < 13 := (Real.sqrt_lt' (by norm_num)).2 (by linarith)
  have hb : (Ideal.absNorm (I:Ideal (𝓞 L)) : ℝ) < 4 := by
    have hx := mul_le_mul_of_nonneg_right hpow
      (show 0 ≤ (6 / 27 : ℝ)*Real.sqrt |(NumberField.discr L : ℝ)| by positivity)
    norm_num [Nat.factorial] at hI
    nlinarith only [hI,hx,hs]
  have hn : Ideal.absNorm (I:Ideal (𝓞 L))<4 := by exact_mod_cast hb
  have hpos := Ideal.absNorm_ne_zero_of_nonZeroDivisors I
  interval_cases h : Ideal.absNorm (I:Ideal (𝓞 L))
  · contradiction
  · rw [Ideal.absNorm_eq_one_iff.mp h]; infer_instance
  · rw [←norm_two_unique _ h]; exact ⟨⟨_,rfl⟩⟩
  · exact (norm_three_impossible _ h).elim

theorem class_number_one : NumberField.classNumber L=1 :=
  NumberField.classNumber_eq_one_iff.mpr integers_principal

/-- Twice any algebraic integer lies in the order generated by θ. Thus at
every odd prime this order computes the full ring of integers. -/
theorem two_mul_coordinates (z : 𝓞 L) :
    ∃ a b c : ℤ, 2*z = a+(b:𝓞 L)*generatorInteger+(c:𝓞 L)*generatorInteger^2 := by
  classical
  let B := (RingOfIntegers.basis L).reindex ((NumberField.integralBasis L).indexEquiv basis)
  let A := B.toMatrix powerFamily
  have hd : 148=A.det^2*NumberField.discr L := by
    rw [←NumberField.discr_eq_discr L B]
    change 148=(B.toMatrix powerFamily).det^2*Algebra.discr ℤ B
    rw [←Algebra.discr_of_matrix_vecMul,Module.Basis.toMatrix_map_vecMul,power_discriminant]
  have hdv : A.det^2 ∣ 148 := ⟨_,hd⟩
  have hb : A.det^2 ≤ 148 := Int.le_of_dvd (by decide) hdv
  have hlow : -12 ≤ A.det := by nlinarith [sq_nonneg (A.det+13)]
  have hupp : A.det ≤ 12 := by nlinarith [sq_nonneg (A.det-13)]
  have hf : A.det ∣ 2 := by
    revert hdv
    interval_cases h : A.det <;> decide
  obtain ⟨k,hk⟩ := hf
  let w := A.cramer (B.repr z)
  have hw : ∑ j : Fin 3, w j • powerFamily j = A.det • z := by
    apply B.repr.injective
    ext i
    have hc := congrFun (Matrix.mulVec_cramer A (B.repr z)) i
    simp only [map_sum,map_smul,Finset.sum_apply',Finsupp.smul_apply,smul_eq_mul]
    simpa only [Matrix.mulVec, dotProduct,A,Module.Basis.toMatrix_apply,Pi.smul_apply,
      smul_eq_mul,mul_comm,w] using hc
  rw [Fin.sum_univ_three] at hw
  change w 0 • generatorInteger^0 + w 1 • generatorInteger^1 + w 2 • generatorInteger^2 = _ at hw
  simp only [pow_zero,pow_one,zsmul_eq_mul, mul_one] at hw
  refine ⟨k * w 0,k * w 1,k * w 2,?_⟩
  have he : (2:𝓞 L)=(A.det:𝓞 L)*(k:𝓞 L) := by exact_mod_cast hk
  push_cast
  rw [he]
  linear_combination -(k:𝓞 L)*hw

end
end DiophantineNP.Curve37.Kummer
