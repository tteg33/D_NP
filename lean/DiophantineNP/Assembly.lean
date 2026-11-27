import DiophantineNP.PackingBridge
import DiophantineNP.ModularVerifier
import DiophantineNP.ScaleFormula
import DiophantineNP.NaturalBridge
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Compiling the width certificates and the modular check together

The four head registers are a width predecessor, the modulus, the multiplier
and the scale. Their values are witnesses. Each of the four polynomial checks
uses a disjoint block of auxiliary slots.
-/
namespace DiophantineNP.Assembly

open MvPolynomial Packing WidthData

private abbrev Registers (r s t : ℕ) :=
  Fin 4 ⊕ (Fin 17 ⊕ ((Fin r ⊕ Fin r) ⊕ ((Fin s ⊕ Fin s) ⊕ (Fin t ⊕ Fin t))))

private def head {r s t : ℕ} (i : Fin 4) : Registers r s t := .inl i
private def modular {r s t : ℕ} (i : Fin 17) : Registers r s t := .inr (.inl i)
private def modulus {r s t : ℕ} (i : Fin r ⊕ Fin r) : Registers r s t := .inr (.inr (.inl i))
private def multiplier {r s t : ℕ} (i : Fin s ⊕ Fin s) : Registers r s t :=
  .inr (.inr (.inr (.inl i)))
private def scaling {r s t : ℕ} (i : Fin t ⊕ Fin t) : Registers r s t :=
  .inr (.inr (.inr (.inr i)))

private def modularSlot {r s t : ℕ} : Fin 5 ⊕ Fin 17 → Bool ⊕ Registers r s t :=
  Sum.elim (fun i => match i.val with
    | 0 => .inl false | 1 => .inl true | 2 => .inr (head 1) | 3 => .inr (head 2)
    | _ => .inr (head 3)) (fun i => .inr (modular i))

/-- Insert a natural width n=k+1 and a guessed output into a width graph. -/
private noncomputable def insertWidth {r s t h : ℕ} (P : Equation (Fin h))
    (slot : Fin 4) (loc : Fin h ⊕ Fin h → Registers r s t) : Equation (Registers r s t) :=
  bind₁ (Sum.elim (fun b : Bool => if b then X (.inr (head slot))
    else (X (.inr (head 0)) + 1 : Equation (Registers r s t))) (fun i => X (.inr (loc i))))
    (splitEquation P)

noncomputable def polynomial {r s t : ℕ}
    (p : Equation (Fin r)) (q : Equation (Fin s)) (z : Equation (Fin t)) :
    Equation (Registers r s t) :=
  (rename modularSlot ModularPolynomial.polynomial)^2 +
  (insertWidth p 1 modulus)^2 + (insertWidth q 2 multiplier)^2 + (insertWidth z 3 scaling)^2

private theorem eval_modular {r s t : ℕ} (a b : ℕ) (w : Registers r s t → ℕ) :
    value (rename modularSlot ModularPolynomial.polynomial) a b (fun i => (w i : ℤ)) =
    eval (ModularPolynomial.assignment a b (w (head 1)) (w (head 2)) (w (head 3))
      (w ∘ modular)) ModularPolynomial.polynomial := by
  change eval _ (rename _ _) = eval _ _
  rw [eval_rename]
  apply congrArg (fun f => eval f ModularPolynomial.polynomial)
  funext i
  rcases i with i | j
  · fin_cases i <;> rfl
  · rfl

private theorem eval_width {r s t h : ℕ} (P : Equation (Fin h)) (slot : Fin 4)
    (loc : Fin h ⊕ Fin h → Registers r s t) (a b : ℕ) (w : Registers r s t → ℕ) :
    value (insertWidth P slot loc) a b (fun i => (w i : ℤ)) =
    widthValue P (w (head 0) + 1) (w (head slot)) (decodeWitness (w ∘ loc)) := by
  change _ = value P (w (head 0)+1) (w (head slot)) (decodeWitness (w ∘ loc))
  rw [← value_split]
  unfold value insertWidth
  rw [aeval_bind₁]
  apply congrArg (fun f => aeval f (splitEquation P))
  funext i
  rcases i with b | j
  · cases b <;> simp [head]
  · simp

theorem polynomial_zero_iff {r s t : ℕ}
    (p : Equation (Fin r)) (q : Equation (Fin s)) (z : Equation (Fin t))
    (a b : ℕ) (w : Registers r s t → ℕ) :
    value (polynomial p q z) a b (fun i => (w i : ℤ)) = 0 ↔
    eval (ModularPolynomial.assignment a b (w (head 1)) (w (head 2)) (w (head 3))
      (w ∘ modular)) ModularPolynomial.polynomial = 0 ∧
    widthValue p (w (head 0)+1) (w (head 1)) (decodeWitness (w ∘ modulus)) = 0 ∧
    widthValue q (w (head 0)+1) (w (head 2)) (decodeWitness (w ∘ multiplier)) = 0 ∧
    widthValue z (w (head 0)+1) (w (head 3)) (decodeWitness (w ∘ scaling)) = 0 := by
  let V := fun e : Equation (Registers r s t) => value e a b (fun i => (w i : ℤ))
  change V _ = 0 ↔ _
  unfold polynomial V value
  simp only [map_add, map_pow]
  change (V (rename modularSlot ModularPolynomial.polynomial))^2 +
    (V (insertWidth p 1 modulus))^2 + (V (insertWidth q 2 multiplier))^2 +
    (V (insertWidth z 3 scaling))^2 = 0 ↔ _
  dsimp only [V]
  rw [eval_modular, eval_width, eval_width, eval_width]
  generalize eval (ModularPolynomial.assignment _ _ _ _ _ _) ModularPolynomial.polynomial = x
  generalize widthValue p _ _ _ = y
  generalize widthValue q _ _ _ = u
  generalize widthValue z _ _ _ = v
  constructor
  · intro h
    have hx := sq_nonneg x
    have hy := sq_nonneg y
    have hu := sq_nonneg u
    have hv := sq_nonneg v
    have hh : x^2=0 ∧ y^2=0 ∧ u^2=0 ∧ v^2=0 := by omega
    simpa using hh
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    norm_num

private noncomputable def heads (n : ℕ) : Fin 4 → ℕ := ![n-1, widthD n, widthJ n, scale n]

private noncomputable def combine {r s t : ℕ} (n : ℕ) (v : Fin 17 → ℕ)
    (d : Fin r → ℤ) (j : Fin s → ℤ) (m : Fin t → ℤ) : Registers r s t → ℕ :=
  Sum.elim (heads n) (Sum.elim v (Sum.elim (splitWitness d)
    (Sum.elim (splitWitness j) (splitWitness m))))

private theorem costSum {A B : Type} [Fintype A] [Fintype B] (f : A → ℕ) (g : B → ℕ) :
    natCost (Sum.elim f g) = natCost f + natCost g := by
  simp [natCost, Fintype.sum_sum_type]

private theorem costHeads {n : ℕ} (hn : 0 < n) : natCost (heads n) ≤ 4*(20*(n+2)^3+1) := by
  let h := 20*(n+2)^3
  have hsmall : n+2 ≤ h := by dsimp [h]; nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^2)]
  have hm : scale n ≤ 2^h := Nat.pow_le_pow_right (by decide) hsmall
  have hd : widthD n ≤ 2^h := widthD_bound n
  have hj := (widthJ_lt_D n hn).le.trans hd
  have hk : n-1 ≤ 2^h :=
    (show n-1 ≤ n+2 by omega).trans ((Nat.lt_two_pow_self (n := n+2)).le.trans hm)
  have hbit {a : ℕ} (ha : a ≤ 2^h) : bits a ≤ h+1 := by
    by_cases hz : a=0
    · simp [hz, bits]
    · have hl := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp ((Nat.log2_self_le hz).trans ha)
      exact Nat.succ_le_succ hl
  calc
    natCost (heads n) ≤ ∑ _ : Fin 4, (h+1) := by
      apply Finset.sum_le_sum
      intro i _
      apply hbit
      fin_cases i
      · exact hk
      · exact hd
      · exact hj
      · exact hm
    _ = _ := by simp [h, Nat.mul_comm]

private theorem budget {x c d e z : ℕ} (hx : 2 ≤ x)
    (hz : z ≤ 4*(20*x^3+1) + (17*(40*x^3+7) + (x^c + (x^d + x^e)))) :
    z ≤ x^(max 3 (max c (max d e)) + 10) := by
  let k := max 3 (max c (max d e))
  have h1 : 1 ≤ x := by omega
  have h3 : x^3 ≤ x^k := Nat.pow_le_pow_right h1 (le_max_left ..)
  have hc : x^c ≤ x^k := Nat.pow_le_pow_right h1 (by dsimp [k]; omega)
  have hd : x^d ≤ x^k := Nat.pow_le_pow_right h1 (by dsimp [k]; omega)
  have he : x^e ≤ x^k := Nat.pow_le_pow_right h1 (by dsimp [k]; omega)
  have hp : 0 < x^k := Nat.pow_pos (by omega : 0 < x)
  have hlarge : 1024 ≤ x^10 := Nat.pow_le_pow_left hx 10
  calc
    z ≤ x^k*1024 := by omega
    _ ≤ x^k*x^10 := Nat.mul_le_mul_left _ hlarge
    _ = _ := (pow_add _ _ _).symm

/-- Three honest, globally sound width graphs suffice for the full native certificate.
The 17 modular registers, all width registers, and all auxiliary slots are counted. -/
theorem strong_of_widthGraphs (hD : HasWidthGraph widthD)
    (hJ : HasWidthGraph widthJ) (hM : HasWidthGraph scale) : StrongNatVerifier := by
  obtain ⟨r, c, P, hP⟩ := hD
  obtain ⟨s, d, Q, hQ⟩ := hJ
  obtain ⟨t, e, Z, hZ⟩ := hM
  refine ⟨Registers r s t, inferInstance, max 3 (max c (max d e))+10, polynomial P Q Z, ?_⟩
  intro n a b hn ha hb
  constructor
  · intro yes
    obtain ⟨v, hv, hzero⟩ := ModularPolynomial.native_natural_complete hn ha hb yes
    obtain ⟨u, hu, hu0⟩ := (hP n hn).1
    obtain ⟨j, hj, hj0⟩ := (hQ n hn).1
    obtain ⟨m, hm, hm0⟩ := (hZ n hn).1
    refine ⟨combine n v u j m, ?_, ?_⟩
    · apply budget (by omega : 2 ≤ n+2)
      simp only [combine, costSum, cost_split]
      exact Nat.add_le_add (costHeads hn) (Nat.add_le_add hv
        (Nat.add_le_add hu (Nat.add_le_add hj hm)))
    · apply (polynomial_zero_iff ..).2
      change _ ∧ widthValue P (n-1+1) (widthD n) (decodeWitness (splitWitness u)) = 0 ∧
        widthValue Q (n-1+1) (widthJ n) (decodeWitness (splitWitness j)) = 0 ∧
        widthValue Z (n-1+1) (scale n) (decodeWitness (splitWitness m)) = 0
      rw [show n-1+1=n by omega, decode_split, decode_split, decode_split]
      exact ⟨hzero,hu0,hj0,hm0⟩
  · intro w hw
    obtain ⟨hmod, h₁, h₂, h₃⟩ := (polynomial_zero_iff ..).1 hw
    let N := w (head 0)+1
    have hN : 0 < N := Nat.zero_lt_succ _
    have ed := (hP N hN).2 _ _ h₁
    have ej := (hQ N hN).2 _ _ h₂
    have em := (hZ N hN).2 _ _ h₃
    rw [Int.ofNat_inj.mp ed, Int.ofNat_inj.mp ej, Int.ofNat_inj.mp em] at hmod
    exact ModularPolynomial.nat_root_implies_incl hN hmod

/-- Theorem 1.1 conditional on precisely the two uniform construction propositions. -/
theorem nativeVerifier_of_packing (pack : PackingClaim) (uniform : WidthDescriptions) :
    NativeVerifier := by
  obtain ⟨modulusGraph, multiplierGraph⟩ := widthGraphs pack uniform
  exact strongNatVerifier_implies_nativeVerifier
    (strong_of_widthGraphs modulusGraph multiplierGraph (scaleGraph pack))

end DiophantineNP.Assembly
