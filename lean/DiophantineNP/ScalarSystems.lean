import DiophantineNP.CertifiedRounding
import DiophantineNP.ConstraintCost

/-! # Compiling scalar evaluation registers into a bounded rational graph

A single fixed constraint system can refer to all scalar evaluation registers.
The honest size estimate for those registers is sufficient: the comparison,
divisibility, and Boolean gate witnesses introduced by the polynomial compiler
are bounded here. The rational denominator must be forced positive by the system.
-/
namespace DiophantineNP.Packing

open MvPolynomial

def ShortScalarSystem {k : ℕ} (f : Scalar k) : Prop :=
  ∃ (r C : ℕ) (S : Compiler.Formula (RatVar k ⊕ Fin r)), ∀ U, 0<U → ∀ t : Fin k → Fin U,
    (∃ (p q : ℤ) (w : Fin r → ℤ),
      intCost w + (bits p.natAbs+1) + (bits q.natAbs+1) ≤ (1+U)^C ∧
      S.Holds (Sum.elim (ratArguments t p q) w)) ∧
    (∀ (p q : ℤ) w, S.Holds (Sum.elim (ratArguments t p q) w) →
      0 < q ∧ (p : ℚ)/(q : ℚ) = f U t)

private theorem bit_le_cost {W : Type} [Fintype W] (w : W → ℤ) (i : W) :
    bits (w i).natAbs ≤ intCost w := by
  unfold intCost
  exact (Nat.le_succ _).trans (Finset.single_le_sum (f := fun j => bits (w j).natAbs+1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

private def flattenSlots {I W A : Type} [Fintype (W ⊕ A)]
    (e : W ⊕ A ≃ Fin (Fintype.card (W ⊕ A))) : (I ⊕ W) ⊕ A → I ⊕ Fin (Fintype.card (W ⊕ A))
  | .inl (.inl i) => .inl i
  | .inl (.inr w) => .inr (e (.inl w))
  | .inr a => .inr (e (.inr a))

theorem scalarSystem_to_graph {k : ℕ} {f : Scalar k} (s : ShortScalarSystem f) :
    ShortRationalGraph f := by
  classical
  obtain ⟨r,C,S,hs⟩ := s
  letI : Fintype S.Aux := Fintype.ofFinite _
  let E := Fintype.equivFin (Fin r ⊕ S.Aux)
  obtain ⟨K,hK⟩ := S.compile_linear_cost
  refine ⟨_,(C+1)+(3*K+2),rename (flattenSlots E) S.compile,?_⟩
  intro U hU t
  have ev (p q : ℤ) (v : Fin (Fintype.card (Fin r ⊕ S.Aux)) → ℤ) :
      aeval (Sum.elim (ratArguments t p q) v) (rename (flattenSlots E) S.compile) =
      eval (Sum.elim (Sum.elim (ratArguments t p q) (fun i => v (E (.inl i))))
        (fun i => v (E (.inr i)))) S.compile := by
    change eval _ (rename _ _) = _
    rw [eval_rename]
    apply congrArg (fun vals => eval vals S.compile)
    funext j; rcases j with (i|w)|a <;> rfl
  obtain ⟨honest,sound⟩ := hs U hU t
  constructor
  · obtain ⟨p,q,w,hsize,hholds⟩ := honest
    let B := 1+U
    have hB : 2 ≤ B := by dsimp [B]; omega
    have he : B^C ≤ B^(C+1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hbsmall : 1+U ≤ B^(C+1) := by
      simpa [B] using Nat.pow_le_pow_right (n := B) (by omega) (show 1 ≤ C+1 by omega)
    let h := B^(C+1)
    have hv (i : RatVar k ⊕ Fin r) :
        bits ((Sum.elim (ratArguments t p q) w i).natAbs) ≤ h := by
      change intCost w + _ + _ ≤ B^C at hsize
      rcases i with ((i|_)|i)
      · cases i with
        | universeSize => exact (Nat.succ_le_succ (Nat.log2_le_self U)).trans (by omega)
        | parameter i =>
          have hl := (t i).isLt
          exact (Nat.succ_le_succ (Nat.log2_le_self (t i).val)).trans (by omega)
        | output => change bits p.natAbs ≤ _; dsimp [h]; omega
      · change bits q.natAbs ≤ _; dsimp [h]; omega
      · exact (bit_le_cost w i).trans (by dsimp [h]; omega)
    obtain ⟨v,hz,vcost⟩ := hK h _ hv hholds
    let u := (Sum.elim w v) ∘ E.symm
    have hu : intCost u = intCost w + intCost v := by
      unfold intCost
      rw [show (∑ i, (bits (u i).natAbs+1)) =
        ∑ j : Fin r ⊕ S.Aux, (bits ((Sum.elim w v) j).natAbs+1) from
          E.symm.sum_comp (fun j => bits ((Sum.elim w v) j).natAbs+1)]
      simp [Fintype.sum_sum_type]
    refine ⟨p,q,u,?_,?_⟩
    · have hp : 1 ≤ h := Nat.pow_pos (by omega : 0<B)
      change intCost w + _ + _ ≤ B^C at hsize
      have hF : 3*K+2 ≤ B^(3*K+2) :=
        Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hB _)
      have h2 : h+1 ≤ 2*h := by omega
      have hK' := vcost.trans (Nat.mul_le_mul_left K h2)
      rw [hu]
      change _ ≤ B^((C+1)+(3*K+2))
      calc
        _ ≤ h*(3*K+2) := by dsimp [h] at *; nlinarith [Nat.zero_le (K*B^(C+1))]
        _ ≤ _ := by rw [pow_add]; exact Nat.mul_le_mul_left h hF
    · rw [ev]
      simpa [u, Function.comp_apply] using hz
  · intro p q v hzero
    rw [ev] at hzero
    exact sound p q _ ((S.compile_exact _).mp ⟨_, hzero⟩)

theorem packing_of_scalar_systems
    (construction : ∀ (k : ℕ) (φ : Counting.Formula (k+1)),
      ∃ f : Scalar k, ShortScalarSystem f ∧ RoundsTo f φ) : PackingClaim :=
  packing_of_rational_evaluators fun k φ => by
    obtain ⟨f,h,a⟩ := construction k φ
    exact ⟨f, scalarSystem_to_graph h, a⟩

end DiophantineNP.Packing
