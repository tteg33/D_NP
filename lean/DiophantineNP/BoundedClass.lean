import DiophantineNP.BoundedRelation
import DiophantineNP.EvaluatorGrowth
import DiophantineNP.JonesLength

/-! # Scalar operations in globally sound bounded relations, and unary languages -/
namespace DiophantineNP.BoundedRelation
open MvPolynomial ScalarProgram

private theorem inputPolyBound {σ : Type} (p : MvPolynomial σ ℤ) :
    ∃ A : ℕ, ∀ h (x : Env σ), Fits h x → signedBits (eval (ints x) p) ≤ A*(h+1)+2 := by
  obtain ⟨A,hA⟩ := Compiler.eval_magnitude_bound p
  refine ⟨A,fun h x hx => ?_⟩
  have he := hA h (ints x) (fun i => by
    change x i ≤ 2^h
    exact Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (hx i)))
  have logle : (eval (ints x) p).natAbs.log2 ≤ A*(h+1) := by
    have hb := FourSquare.bits_mono he
    simpa [bits] using hb
  unfold signedBits bits
  omega

private noncomputable def opSub {σ : Type} (op : Operation) (a b y : MvPolynomial σ ℤ) :
    MvPolynomial (σ ⊕ (op.W ⊕ op.W)) ℤ :=
  bind₁ (Sum.elim (fun i : Option Bool => rename Sum.inl (match i with
    | none => y | some false => a | some true => b))
    (fun i => X (.inr (.inl i)) - X (.inr (.inr i)))) op.polynomial

private theorem opSub_eval {σ : Type} (op : Operation) (a b y : MvPolynomial σ ℤ)
    (x : Env σ) (w : Env (op.W ⊕ op.W)) :
    eval (Sum.elim (ints x) (ints w)) (opSub op a b y) =
      eval (Sum.elim (opInputs (eval (ints x) a) (eval (ints x) b) (eval (ints x) y))
        (decodeWitness w)) op.polynomial := by
  change eval₂Hom (RingHom.id ℤ) _ _ = _
  rw [opSub, eval₂Hom_bind₁]
  apply congrArg (fun g => eval g op.polynomial)
  funext i
  rcases i with ((_ | _ | _) | i) <;> simp [eval_rename,opInputs,decodeWitness,ints,Function.comp_def] <;> rfl

/-- A fixed scalar operation can be applied to arbitrary fixed polynomial
expressions, including signed expressions of natural input coordinates. -/
theorem Short.operation {σ : Type} (op : Operation) (a b y : MvPolynomial σ ℤ) :
    Short (fun x => eval (ints x) y = op.apply (eval (ints x) a) (eval (ints x) b)) := by
  obtain ⟨A,hA⟩ := inputPolyBound a
  obtain ⟨B,hB⟩ := inputPolyBound b
  obtain ⟨Y,hY⟩ := inputPolyBound y
  obtain ⟨d,hd⟩ := op.complete
  let p : Polynomial ℕ := (Polynomial.C (A+B+Y) * (Polynomial.X+1) + 8)^d
  refine ⟨op.W ⊕ op.W,inferInstance,p,opSub op a b y,?_,?_⟩
  · intro x w hw
    exact op.sound _ _ _ _ ((opSub_eval ..).symm.trans hw)
  · intro h x hx hy
    obtain ⟨w,hc,he⟩ := hd (eval (ints x) a) (eval (ints x) b)
    rw [← hy] at hc he
    refine ⟨splitWitness w,?_,by simpa only [opSub_eval,decode_split] using he⟩
    intro i
    have hi : bits (splitWitness w i) ≤ natCost (splitWitness w) :=
      Finset.single_le_sum (f := fun j => bits (splitWitness w j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    rw [cost_split] at hi
    refine (hi.trans hc).trans ?_
    simp only [p,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
    apply Nat.pow_le_pow_left
    have ha := hA h x hx
    have hb := hB h x hx
    have hy' := hY h x hx
    simp only [Nat.add_mul]
    omega

/-- Variable exponentiation on three natural coordinates. The output is
included among the free coordinates when charging the witness bit cost. -/
theorem Short.power {σ : Type} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (a b y : σ) : Short (fun x => x y = (x a)^(x b)) := by
  simpa only [eval_X,ints,signedPower_apply,Int.toNat_natCast,← Nat.cast_pow,Int.natCast_inj] using
    (Short.operation (signedPower hc hq) (X a) (X b) (X y))

/-- Binary length in the verifier's convention, including one bit for zero. -/
theorem Short.binaryLength {σ : Type} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (a l : σ) : Short (fun x => x l = bits (x a)) := by
  obtain ⟨op,hop,_⟩ := Blueprint.exists_log2Operation hc hq
  have eqR : (fun x : Env σ => eval (ints x) (X l - 1) = op.apply (eval (ints x) (X a))
      (eval (ints x) 0)) = (fun x => x l = bits (x a)) := by
    funext x
    apply propext
    simp [ints,hop,bits]
    omega
  rw [← eqR]
  exact Short.operation op (X a) 0 (X l-1)

/-- A globally sound short unary relation gives membership in the draft's
total-budget Diophantine class, with all witness fields charged. -/
theorem Short.mem_D {L : Classes.Language} (H : Short (fun x : Env Unit => x () ∈ L)) :
    L ∈ Classes.D := by
  classical
  obtain ⟨W,fw,p,P,hs,hc⟩ := H
  letI : Fintype W := fw
  let e := Fintype.equivFin W
  let f : Unit ⊕ W → Option (Fin (Fintype.card W)) := Sum.elim (fun _ => none) (some ∘ e)
  let Q := rename f P
  have val (a : ℕ) (w : Fin (Fintype.card W) → ℕ) :
      Classes.polyValue Q a w = eval (Sum.elim (ints (fun _ : Unit => a)) (ints (w ∘ e))) P := by
    unfold Classes.polyValue
    have agreement {T : Type} (u : T → ℤ) (q : MvPolynomial T ℤ) : aeval u q = eval u q :=
      DFunLike.congr_fun (coe_aeval_eq_eval u) q
    rw [agreement,show Q=rename f P from rfl,eval_rename]
    apply congrArg (fun g => eval g P)
    funext i
    cases i <;> rfl
  refine ⟨_,Polynomial.C (Fintype.card W)*p,Q,fun a => ⟨?_,?_⟩⟩
  · intro ha
    obtain ⟨w,hb,he⟩ := hc (bits a) (fun _ => a) (fun _ => le_rfl) ha
    refine ⟨w ∘ e.symm,?_,?_⟩
    · simpa [natCost,Polynomial.eval_mul] using (Finset.sum_le_sum
        (s := (Finset.univ : Finset (Fin (Fintype.card W)))) (fun i _ => hb (e.symm i)))
    · simpa [val,Function.comp_def] using he
  · rintro ⟨w,_,hz⟩
    exact hs (fun _ => a) (w ∘ e) ((val a w).symm.trans hz)

end DiophantineNP.BoundedRelation
