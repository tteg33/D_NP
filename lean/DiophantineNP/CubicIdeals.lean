import DiophantineNP.CubicFactorParity

/-! # Prime ideal factors of a primitive linear expression in θ -/
namespace DiophantineNP.Curve37.Kummer
open NumberField
open scoped NumberField
noncomputable section

def linearInteger (a b : ℤ) : 𝓞 L := a-2*(b:𝓞 L)*generatorInteger

private def residue (p : ℕ) [Fact p.Prime] (a b c d e : ℤ) : ZMod p :=
  let t : ZMod p := a/(2*b)
  (c+d*t+e*t^2)/2

private theorem residue_formula {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hodd : p≠2) (φ : 𝓞 L →+* F) {a b : ℤ} (hcop : IsCoprime a b)
    (hzero : φ (linearInteger a b)=0)
    {z : 𝓞 L} {c d e : ℤ} (hz : 2*z=c+(d:𝓞 L)*generatorInteger+(e:𝓞 L)*generatorInteger^2) :
    φ z = ZMod.castHom (dvd_refl p) F (residue p a b c d e) := by
  let t := φ generatorInteger
  have h : (a:F) - 2*(b:F)*t=0 := by simpa only [t,linearInteger,map_sub,map_ofNat,map_mul,map_intCast] using hzero
  have h2 : (2:F)≠0 := by
    intro he
    apply hodd
    have hd := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast he)
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (Fact.out : p.Prime).ne_one
  have hb : (b:F)≠0 := by
    intro he
    rw [he] at h
    simp only [mul_zero,zero_mul,sub_zero] at h
    obtain ⟨m,n,hh⟩ := hcop
    have hh' : (m:F)*(a:F)+(n:F)*(b:F)=1 := by simpa only [Int.cast_add,Int.cast_mul,Int.cast_one] using congrArg (fun z : ℤ => (z:F)) hh
    rw [he,h] at hh'
    simp at hh'
  have ht : t=(a:F)/(2*b) := (eq_div_iff (mul_ne_zero h2 hb)).2 (by linear_combination -h)
  have hh := congrArg φ hz
  simp only [map_mul,map_ofNat,map_add,map_pow,map_intCast] at hh
  dsimp only [residue]
  simp only [map_div₀,map_intCast,map_add,map_pow,map_mul,map_ofNat]
  apply (eq_div_iff h2).2
  change 2*φ z=(c:F)+(d:F)*t+(e:F)*t^2 at hh
  rw [←ht]
  linear_combination hh

private theorem quotient_charP {I : Ideal (𝓞 L)} [I.IsMaximal] {p : ℕ} (hp : p.Prime)
    (h : (p:𝓞 L) ∈ I) : CharP (𝓞 L ⧸ I) p :=
  (CharP.charP_iff_prime_eq_zero hp).2 (by simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr h))

private theorem odd_prime_norm {I : Ideal (𝓞 L)} [I.IsMaximal] {a b : ℤ}
    (hc : IsCoprime a b) (hl : linearInteger a b ∈ I) {p : ℕ} (hp : p.Prime)
    (hodd : p≠2) (hpi : (p:𝓞 L) ∈ I) : Ideal.absNorm I=p := by
  haveI := quotient_charP hp hpi
  haveI : Fact p.Prime := ⟨hp⟩
  letI := Ideal.Quotient.field I
  let F := 𝓞 L ⧸ I
  let φ := ZMod.castHom (dvd_refl p) F
  have hs : Function.Surjective φ := by
    intro v
    obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective v
    obtain ⟨c,d,e,h⟩ := two_mul_coordinates z
    exact ⟨_,(residue_formula hodd _ hc (Ideal.Quotient.eq_zero_iff_mem.mpr hl) h).symm⟩
  let equiv := Equiv.ofBijective φ ⟨ZMod.castHom_injective F,hs⟩
  change Nat.card F=p
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [←Nat.card_congr equiv,Nat.card_eq_fintype_card,ZMod.card]

private theorem even_prime_unique {I : Ideal (𝓞 L)} (hI : I.IsPrime) (h2 : (2:𝓞 L) ∈ I) :
    Ideal.span {generatorInteger}=I := by
  have nt := norm_generator_ideal
  have hs := Ideal.isPrime_of_irreducible_absNorm (I:=Ideal.span {generatorInteger})
    (nt ▸ Nat.prime_two)
  apply (hs.isMaximal (by intro h; rw [h,Ideal.absNorm_bot] at nt; contradiction)).eq_of_le hI.ne_top
  apply (Ideal.span_singleton_le_iff_mem _).2
  apply hI.mem_of_pow_mem 3
  rw [cubic_integral,show 4*generatorInteger-2 = (2*generatorInteger-1)*2 by ring]
  exact I.mul_mem_left _ h2

/-- Every prime divisor of a primitive linear expression has residue degree one. -/
theorem prime_factor_norm {I : Ideal (𝓞 L)} (hi : I.IsPrime) (hn : I≠⊥)
    {a b : ℤ} (hc : IsCoprime a b) (hl : linearInteger a b ∈ I) :
    (Ideal.absNorm I).Prime := by
  haveI := hi.isMaximal hn
  letI := Ideal.Quotient.field I
  haveI : Finite (𝓞 L ⧸ I) := (Ideal.absNorm_ne_zero_iff I).mp (mt Ideal.absNorm_eq_zero_iff.mp hn)
  let p := ringChar (𝓞 L ⧸ I)
  have hp : p.Prime := CharP.prime_ringChar (𝓞 L ⧸ I)
  have hm : (p:𝓞 L) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (by simp [p])
  by_cases he : p=2
  · rw [he] at hm
    rw [←even_prime_unique hi (by simpa using hm),norm_generator_ideal]
    exact Nat.prime_two
  · rw [odd_prime_norm hc hl hp he hm]
    exact hp

/-- At most one prime divisor of a primitive linear expression lies over each rational prime. -/
theorem prime_factor_unique {I J : Ideal (𝓞 L)} (hi : I.IsPrime) (hj : J.IsPrime)
    {a b : ℤ} (hc : IsCoprime a b) (hI : linearInteger a b ∈ I) (hJ : linearInteger a b ∈ J)
    (hp : (Ideal.absNorm I).Prime) (he : Ideal.absNorm I=Ideal.absNorm J) : I=J := by
  let p := Ideal.absNorm I
  have hpi : (p:𝓞 L) ∈ I := Ideal.absNorm_mem _
  have hpj : (p:𝓞 L) ∈ J := by simpa only [p,he] using Ideal.absNorm_mem J
  by_cases h2 : p=2
  · rw [h2] at hpi hpj
    exact (even_prime_unique hi (by simpa using hpi)).symm.trans (even_prime_unique hj (by simpa using hpj))
  haveI := hi.isMaximal (by intro h; rw [h,Ideal.absNorm_bot] at hp; contradiction)
  haveI := hj.isMaximal (by intro h; rw [h,Ideal.absNorm_bot] at he; exact hp.ne_zero he)
  letI := Ideal.Quotient.field I
  letI := Ideal.Quotient.field J
  haveI := quotient_charP hp hpi
  haveI := quotient_charP hp hpj
  haveI : Fact p.Prime := ⟨hp⟩
  ext z
  obtain ⟨c,d,e,hz⟩ := two_mul_coordinates z
  have fI := residue_formula h2 (Ideal.Quotient.mk I) hc (Ideal.Quotient.eq_zero_iff_mem.mpr hI) hz
  have fJ := residue_formula h2 (Ideal.Quotient.mk J) hc (Ideal.Quotient.eq_zero_iff_mem.mpr hJ) hz
  rw [←Ideal.Quotient.eq_zero_iff_mem,←Ideal.Quotient.eq_zero_iff_mem,fI,fJ]
  simp only [map_eq_zero]

/-- A primitive linear expression of square ideal norm is a unit times a square. -/
theorem linear_unit_square {a b : ℤ} (hc : IsCoprime a b)
    (hn : IsSquare (Ideal.absNorm (Ideal.span {linearInteger a b}))) :
    ∃ (u : (𝓞 L)ˣ) (v : 𝓞 L), linearInteger a b=(u : 𝓞 L)*v^2 :=
  integer_unit_square_of_norm hn (fun _ hi hz hf => prime_factor_norm hi hz hc hf)
    (fun _ _ hi hj hI hJ => prime_factor_unique hi hj hc hI hJ)

end
end DiophantineNP.Curve37.Kummer
