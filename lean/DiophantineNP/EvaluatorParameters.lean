import DiophantineNP.EvaluatorFamilies

/-! # Fixed programs for grid parameters and the Wallis rational -/

namespace DiophantineNP.Blueprint
open LaurentBounds ScalarProgram ScalarProjection FormulaLaurent
open scoped BigOperators
noncomputable section

namespace NatCode

variable {k : ℕ} {a b : (U : ℕ) → (Fin k → Fin U) → ℕ}

theorem const (n : ℕ) : NatCode k (fun _ _ => n) :=
  ⟨.literal n,.literal _,fun _ _ _ => rfl⟩

theorem «universe» : NatCode k (fun U _ => U) :=
  ⟨.input none,.input _,fun _ _ _ => rfl⟩

theorem param (i : Fin k) : NatCode k (fun _ t => (t i).val) :=
  ⟨.input (some i),.input _,fun _ _ _ => rfl⟩

theorem add (ha : NatCode k a) (hb : NatCode k b) : NatCode k (fun U t => a U t + b U t) := by
  obtain ⟨p,hp,hep⟩ := ha
  obtain ⟨q,hq,heq⟩ := hb
  exact ⟨Arith.add p q, Arith.small_add hp hq,fun U t h => by simp [hep U t h,heq U t h]⟩

theorem mul (ha : NatCode k a) (hb : NatCode k b) : NatCode k (fun U t => a U t * b U t) := by
  obtain ⟨p,hp,hep⟩ := ha
  obtain ⟨q,hq,heq⟩ := hb
  exact ⟨Arith.mul p q, Arith.small_mul hp hq,fun U t h => by simp [hep U t h,heq U t h]⟩

theorem pow (ha : NatCode k a) (n : ℕ) : NatCode k (fun U t => (a U t)^n) := by
  obtain ⟨p,hp,hep⟩ := ha
  exact ⟨Arith.fixedPow p n, Arith.small_fixedPow hp n,fun U t h => by simp [hep U t h]⟩

theorem div (ha : NatCode k a) (hb : NatCode k b) : NatCode k (fun U t => a U t / b U t) := by
  obtain ⟨p,hp,hep⟩ := ha
  obtain ⟨q,hq,heq⟩ := hb
  refine ⟨Arith.div p q,Arith.small_div hp hq,fun U t h => ?_⟩
  rw [Arith.run_div, hep U t h,heq U t h]
  by_cases hy : b U t = 0
  · simp [positiveDiv,hy]
  · have hpos : 0 < (b U t : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hy
    rw [positiveDiv,if_pos hpos,Int.natCast_ediv]

theorem log2 (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (ha : NatCode k a) :
    NatCode k (fun U t => (a U t).log2) := by
  obtain ⟨p,hp,hep⟩ := ha
  obtain ⟨op,hop,hv⟩ := exists_log2Operation hc hq
  refine ⟨.app op p (.literal 0),.app hv hp (.literal _),fun U t h => ?_⟩
  simp [Term.run,hop,hep U t h]

private theorem congr_valid (ha : NatCode k a) (eqn : ∀ U t, 0 < U → a U t = b U t) :
    NatCode k b := by
  obtain ⟨p,hp,hep⟩ := ha
  exact ⟨p,hp,fun U t h => (hep U t h).trans (by rw [eqn U t h])⟩

theorem radius : NatCode k (fun U _ => ConcreteGrid.radius U) := by
  apply congr_valid (add «universe» (div (const 1) «universe»))
  intro U t hU
  simp only [ConcreteGrid.radius]
  by_cases hu : U = 1
  · simp [hu]
  · have h2 : 2 ≤ U := by omega
    simp [Nat.div_eq_of_lt (by omega : 1 < U), max_eq_right h2]

theorem gridJ : NatCode k (fun U _ => 2*ConcreteGrid.radius U+1) :=
  add (mul (const 2) radius) (const 1)

theorem stride : NatCode k (fun U _ => FormulaLaurent.stride U) :=
  mul (const 4) (pow (add (mul (const 2) radius) (const 2)) 30)

theorem size : NatCode k (fun U _ => ConcreteGrid.size U) := by
  unfold ConcreteGrid.size Grid.period
  exact mul (mul (const 4) gridJ) (pow (add (mul (const 2) radius) (const 2)) 30)

theorem precision (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) :
    NatCode k (fun U _ => ConcreteGrid.precision U) :=
  mul (const 100) (add (add gridJ (mul (const 10) (add (log2 hc hq size) (const 1)))) (const 20))

theorem halfDegree (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) :
    NatCode k (fun U _ => FormulaLaurent.halfDegree U) :=
  mul (mul (const (2^15)) (pow size 8))
    (add (add (precision hc hq) (mul (const 20) (add (log2 hc hq size) (const 1)))) (const 100))

end NatCode

/-- The Wallis denominator needs a binomial coefficient. Its base-R digit can
be read by two positive divisions in a fixed term. -/
private def binomialTerm {I : Type} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (n k : Term I) : Term I :=
  let R := Arith.pow hc hq (.literal 2) (Arith.add n (.literal 1))
  let t := Arith.div (Arith.pow hc hq (Arith.add (.literal 1) R) n) (Arith.pow hc hq R k)
  Arith.sub t (Arith.mul R (Arith.div t R))

private theorem binomial_tame {I : Type} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {n k : Term I} (hn : SmallTerm n) (hk : SmallTerm k) :
    TameTerm (binomialTerm hc hq n k) := by
  unfold binomialTerm
  have hR := Arith.tame_pow hc hq (.small (.literal (I:=I) 2)) (Arith.small_add hn (.literal 1))
  have ht := Arith.tame_div (Arith.tame_pow hc hq (Arith.tame_add (.small (.literal 1)) hR) hn)
    (Arith.tame_pow hc hq hR hk)
  exact Arith.tame_sub ht (Arith.tame_mul hR (Arith.tame_div ht hR))

private theorem run_binomial {I : Type} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (n k : Term I) (x : I → ℤ) {N K : ℕ} (hn : n.run x = (N:ℤ)) (hk : k.run x = (K:ℤ))
    (h : K ≤ N) : (binomialTerm hc hq n k).run x = (N.choose K : ℤ) := by
  let R := (2:ℤ)^(N+1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hRK : 0 < R^K := pow_pos hR _
  have hN : ((N:ℤ)+1).toNat = N+1 := by omega
  change _ = _
  simp only [binomialTerm,Arith.run_sub,Arith.run_mul,Arith.run_div,Arith.run_pow,Arith.run_add,
    Arith.run_lit, hn,hk,Int.toNat_natCast,hN]
  change positiveDiv ((1+R)^N) (R^K) - R * positiveDiv (positiveDiv ((1+R)^N) (R^K)) R = _
  simp only [positiveDiv,if_pos hR,if_pos hRK,← Int.emod_def]
  exact TailRadix.choose_from_power N K h

theorem RatCode.piRational {k : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {a : (U : ℕ) → (Fin k → Fin U) → ℕ} (ha : NatCode k a)
    (hpos : ∀ U t, 0 < U → 0 < a U t) : RatCode k (fun U t => FormulaLaurent.piRational (a U t)) := by
  obtain ⟨n,hn,he⟩ := ha
  let twice := Arith.mul (.literal 2) n
  let c := binomialTerm hc hq twice n
  have hc' : TameTerm c := binomial_tame hc hq (Arith.small_mul (.literal _) hn) hn
  refine ⟨Arith.pow hc hq (.literal 16) n, Arith.mul n (Arith.fixedPow c 2),
    Arith.tame_pow hc hq (.small (.literal _)) hn,Arith.tame_mul (.small hn) (Arith.tame_fixedPow hc' 2),?_⟩
  intro U t hU
  let N := a U t
  have hN := hpos U t hU
  have htwice : twice.run (Packing.termInputs t) = ((2*N:ℕ):ℤ) := by simp [twice,N,he U t hU]
  have hchoose : c.run (Packing.termInputs t) = ((2*N).choose N:ℤ) :=
    run_binomial hc hq _ _ _ htwice (he U t hU) (by omega)
  have hC : 0 < (2*N).choose N := Nat.choose_pos (by omega)
  simp only [Arith.run_pow,Arith.run_mul,Arith.run_fixedPow,Arith.run_lit,he U t hU,Int.toNat_natCast,hchoose]
  constructor
  · positivity
  · simp [FormulaLaurent.piRational,N]

end
end DiophantineNP.Blueprint
