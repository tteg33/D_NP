import DiophantineNP.CubicField
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-! # Extracting a square from a primitive principal ideal of square norm

If the prime factors of an ideal have distinct rational prime norms, the
factor multiset of the ideal can be recovered from the factor multiset of its
norm. Even norm multiplicities therefore give a square ideal. Principalizing
its square root recovers a unit times a square in the ring of integers.
-/
namespace DiophantineNP.Curve37.Kummer
open NumberField UniqueFactorizationMonoid
open scoped NumberField
noncomputable section

/-- The prime-by-prime hypotheses suffice to lift a square absolute norm to
an actual square ideal, with no choice of generators for its prime factors. -/
theorem ideal_square_of_norm {I : Ideal (𝓞 L)} (hI : I ≠ ⊥) (hs : IsSquare (Ideal.absNorm I))
    (hp : ∀ P : Ideal (𝓞 L), P.IsPrime → P ≠ ⊥ → I ≤ P → (Ideal.absNorm P).Prime)
    (hu : ∀ P Q : Ideal (𝓞 L), P.IsPrime → Q.IsPrime → I ≤ P → I ≤ Q →
      (Ideal.absNorm P).Prime → Ideal.absNorm P = Ideal.absNorm Q → P = Q) :
    IsSquare I := by
  classical
  let F := normalizedFactors I
  let N := (Ideal.absNorm : Ideal (𝓞 L) →*₀ ℕ)
  have exactProd : F.prod = I := prod_normalizedFactors_eq_self hI
  have pr (P) (h : P ∈ F) : Prime P := prime_of_normalized_factor _ h
  have le (P) (h : P ∈ F) : I ≤ P := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors h)
  have primeNorm (P) (h : P ∈ F) : (N P).Prime := hp P (Ideal.isPrime_of_prime (pr P h)) (pr P h).ne_zero (le P h)
  have inject : Set.InjOn N {P | P ∈ F} := by
    intro P hP Q hQ h
    exact hu P Q (Ideal.isPrime_of_prime (pr P hP)) (Ideal.isPrime_of_prime (pr Q hQ))
      (le _ hP) (le _ hQ) (primeNorm _ hP) h
  let back := Function.invFunOn N {P | P ∈ F}
  have retract : (F.map N).map back = F := by
    rw [Multiset.map_map]
    exact (Multiset.map_congr rfl (fun P hP => inject.leftInvOn_invFunOn hP)).trans (Multiset.map_id F)
  have mapPr : ∀ p ∈ F.map N, Prime p := by
    intro p h
    obtain ⟨P,hP,rfl⟩ := Multiset.mem_map.mp h
    exact Nat.prime_iff.mp (primeNorm _ hP)
  have cert : normalizedFactors (N I) = F.map N := by
    rw [←exactProd,map_multiset_prod]
    exact normalizedFactors_prod_of_prime mapPr
  obtain ⟨a,ha⟩ := hs.exists_sq
  change N I = a^2 at ha
  rw [ha,normalizedFactors_pow] at cert
  let G := (normalizedFactors a).map back
  have twice : 2 • G = F := by simpa only [Multiset.map_nsmul] using (congrArg (Multiset.map back) cert).trans retract
  refine ⟨G.prod,?_⟩
  rw [←exactProd,←twice,two_nsmul,Multiset.prod_add]

/-- In the cubic integer ring, a number with square norm and the stated
support property is an integral unit times an integral square. -/
theorem integer_unit_square_of_norm {z : 𝓞 L} (hs : IsSquare (Ideal.absNorm (Ideal.span {z})))
    (hp : ∀ I : Ideal (𝓞 L), I.IsPrime → I ≠ ⊥ → z ∈ I → (Ideal.absNorm I).Prime)
    (hu : ∀ I J : Ideal (𝓞 L), I.IsPrime → J.IsPrime → z ∈ I → z ∈ J →
      (Ideal.absNorm I).Prime → Ideal.absNorm I = Ideal.absNorm J → I=J) :
    ∃ (u : (𝓞 L)ˣ) (v : 𝓞 L), z = (u : 𝓞 L)*v^2 := by
  by_cases hz : z=0
  · exact ⟨1,0,by simp [hz]⟩
  letI := integers_principal
  obtain ⟨J,hJ⟩ := (ideal_square_of_norm (I:=Ideal.span {z})
    (mt Ideal.span_singleton_eq_bot.mp hz) hs
    (fun I hi hn h => hp I hi hn ((Ideal.span_singleton_le_iff_mem ..).mp h))
    (fun I J hi hj h₁ h₂ => hu I J hi hj ((Ideal.span_singleton_le_iff_mem ..).mp h₁)
      ((Ideal.span_singleton_le_iff_mem ..).mp h₂))).exists_sq
  let v := Submodule.IsPrincipal.generator J
  have assoc : Associated (v^2) z := Ideal.span_singleton_eq_span_singleton.mp (by
    rw [← Ideal.span_singleton_pow,show Ideal.span {v}=J from Ideal.span_singleton_generator J,hJ])
  obtain ⟨u,h⟩ := assoc
  exact ⟨u,v,h.symm.trans (mul_comm _ _)⟩

end
end DiophantineNP.Curve37.Kummer
