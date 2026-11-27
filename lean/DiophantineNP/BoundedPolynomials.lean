import DiophantineNP.BoundedRelation

/-! # Polynomial substitutions in fixed, short natural relations -/
namespace DiophantineNP.BoundedRelation
open MvPolynomial

variable {σ τ : Type}

noncomputable def liftNat (p : MvPolynomial σ ℕ) : MvPolynomial σ ℤ := map (Nat.castRingHom ℤ) p

theorem eval_liftNat (x : Env σ) (p : MvPolynomial σ ℕ) :
    eval (ints x) (liftNat p) = (eval x p : ℤ) := by
  rw [liftNat,eval_map]
  exact (eval₂_comp (Nat.castRingHom ℤ) x p).symm

private theorem eval_bits (p : MvPolynomial σ ℕ) : ∃ A : ℕ, ∀ h x, Fits h x → bits (eval x p) ≤ A*(h+1)+1 := by
  obtain ⟨A,hA⟩ := Compiler.eval_magnitude_bound (liftNat p)
  refine ⟨A, fun h x hx => ?_⟩
  have b := hA h (ints x) (fun i => by simp only [ints,Int.natAbs_natCast]; exact Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (hx i)))
  rw [eval_liftNat,Int.natAbs_natCast] at b
  simpa [bits] using FourSquare.bits_mono b

/-- Substitute a fixed finite family of natural polynomials. Their bit
lengths are bounded uniformly, including constant and zero polynomials. -/
theorem Short.subst {R : Relation σ} [Fintype σ] (hr : Short R) (a : σ → MvPolynomial τ ℕ) :
    Short (fun x => R (fun i => eval x (a i))) := by
  classical
  obtain ⟨W,iw,p,P,hs,hc⟩ := hr
  choose A hA using fun i => eval_bits (a i)
  let c := ∑ i, A i
  let B : Polynomial ℕ := Polynomial.C c*(Polynomial.X+1)+1
  let g : σ⊕W → MvPolynomial (τ⊕W) ℤ := Sum.elim (fun i => rename Sum.inl (liftNat (a i))) (fun j => X (.inr j))
  have ev (x : Env τ) (w : Env W) : eval (Sum.elim (ints x) (ints w)) (bind₁ g P) =
      eval (Sum.elim (ints (fun i => eval x (a i))) (ints w)) P := by
    rw [show eval (Sum.elim (ints x) (ints w)) (bind₁ g P) = eval (fun i => eval (Sum.elim (ints x) (ints w)) (g i)) P from eval₂Hom_bind₁ ..]
    apply congrArg (fun y => eval y P)
    funext i; cases i with
    | inl i => simpa [g,eval_rename,Function.comp_def] using eval_liftNat x (a i)
    | inr j => simp [g]
  refine ⟨W,iw,p.comp B,bind₁ g P,fun x w e => hs _ _ ((ev ..).symm.trans e),?_⟩
  intro h x hx yes
  have good : Fits (B.eval h) (fun i => eval x (a i)) := by
    intro i
    have hi : A i ≤ c := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa [B] using (hA i h x hx).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hi) 1)
  simpa only [ev,Polynomial.eval_comp] using hc _ _ good yes

namespace Short

theorem eqPoly (a b : MvPolynomial σ ℕ) : Short (fun x => eval x a = eval x b) := by
  apply (formula (.zero (liftNat a-liftNat b))).congr
  intro x; simp [Compiler.Formula.Holds,eval_liftNat,sub_eq_zero]

theorem lePoly (a b : MvPolynomial σ ℕ) : Short (fun x => eval x a ≤ eval x b) := by
  apply (formula (.nonnegative (liftNat b-liftNat a))).congr
  intro x; simp [Compiler.Formula.Holds,eval_liftNat]

theorem ltPoly (a b : MvPolynomial σ ℕ) : Short (fun x => eval x a < eval x b) := by
  exact (lePoly (a+1) b).congr (fun x => by simp; omega)

theorem maskPoly (native : NativeVerifier) (a b : MvPolynomial σ ℕ) :
    Short (fun x => BitIncl (eval x a) (eval x b)) := by
  exact (mask native).subst (fun i => if i then b else a)

end Short
end DiophantineNP.BoundedRelation
