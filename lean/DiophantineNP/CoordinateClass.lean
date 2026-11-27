import DiophantineNP.CubicDescent
import DiophantineNP.CubicIntegralReduction
import DiophantineNP.RegisterFieldBudget

/-! # Coordinate and total certificate bounds

A polynomial can have long roots on a false input. To change the witness
convention we compile the original cutoff into the equation. -/
namespace DiophantineNP.Classes
open BoundedRelation MvPolynomial
noncomputable section

/-- The per-coordinate bit-length convention for natural certificates. -/
def Dcoord : Set Language := {L | ∃ (r : ℕ) (q : Polynomial ℕ)
  (P : MvPolynomial (Option (Fin r)) ℤ), ∀ x, x ∈ L ↔
    ∃ w : Fin r → ℕ, (∀ i, bits (w i) ≤ q.eval (bits x)) ∧ polyValue P x w = 0}

/-- The inclusive numerical cutoff in Pollett's definition, including equality
at the upper endpoint. -/
def Dpower : Set Language := {L | ∃ (r : ℕ) (q : Polynomial ℕ)
  (P : MvPolynomial (Option (Fin r)) ℤ), ∀ x, x ∈ L ↔
    ∃ w : Fin r → ℕ, (∀ i, w i ≤ 2^(q.eval (bits x))) ∧ polyValue P x w = 0}

private theorem curve_cyclic : PowerTests.Cyclic :=
  Curve37.Kummer.cyclic_of_unitTimesSquare Curve37.Kummer.image_eq_unit_mul_square

private theorem total_cut {σ : Type} (x : σ) {r : ℕ} (w : Fin r → σ) (p : Polynomial ℕ) :
    Short (fun z => natCost (z ∘ w) ≤ p.eval (bits (z x))) :=
  Jones.Machine.certCut_short curve_cyclic (Curve37.canonicalHeight_zsmul Curve37.P) x w p

private theorem one_cut {σ : Type} (x y : σ) (p : Polynomial ℕ) :
    Short (fun z => bits (z y) ≤ p.eval (bits (z x))) := by
  apply (total_cut x (fun _ : Fin 1 => y) p).congr
  intro z; simp [natCost]

private theorem poly_zero {r : ℕ} (P : MvPolynomial (Option (Fin r)) ℤ) :
    Short (fun z : Env (Unit ⊕ Fin r) => polyValue P (z (.inl ())) (z ∘ Sum.inr) = 0) := by
  let f : Option (Fin r) → Unit ⊕ Fin r := Option.elim' (.inl ()) Sum.inr
  apply (Short.formula (.zero (rename f P))).congr
  intro z
  change eval (ints z) (rename f P)=0 ↔ _
  rw [eval_rename]
  have agree {T : Type} (u : T → ℤ) (A : MvPolynomial T ℤ) : aeval u A=eval u A :=
    DFunLike.congr_fun (coe_aeval_eq_eval u) A
  rw [polyValue,agree]
  apply Iff.of_eq
  apply congrArg (fun k : ℤ => k=0)
  apply congrArg (fun g : Option (Fin r) → ℤ => eval g P)
  funext i; cases i <;> rfl

private theorem eval_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b h
  induction p using Polynomial.induction_on' with
  | monomial n c => simpa using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)
  | add p q hp hq => simpa using Nat.add_le_add hp hq

private theorem short_guarded {r : ℕ} {L : Language} (q : Polynomial ℕ)
    (P : MvPolynomial (Option (Fin r)) ℤ) (C : ℕ → (Fin r → ℕ) → Prop)
    (guard : Short (fun z : Env (Unit ⊕ Fin r) => C (z (.inl ())) (z ∘ Sum.inr)))
    (size : ∀ x w, C x w → Fits (q.eval (bits x)) w)
    (hl : ∀ x, x ∈ L ↔ ∃ w, C x w ∧ polyValue P x w=0) :
    Short (fun z : Env Unit => z () ∈ L) := by
  apply Short.exists_of _ (guard.and (poly_zero P)) q
  · intro z w hw
    exact (hl _).2 ⟨w,hw⟩
  · intro H z hz hL
    obtain ⟨w,hc,hp⟩ := (hl _).1 hL
    exact ⟨w,fun i => (size _ _ hc i).trans (eval_mono q (hz ())),hc,hp⟩

theorem short_of_mem_D {L : Language} (hl : L ∈ D) : Short (fun z : Env Unit => z () ∈ L) := by
  obtain ⟨r,q,P,h⟩ := hl
  apply short_guarded q P (fun x w => natCost w ≤ q.eval (bits x)) (total_cut (.inl ()) Sum.inr q) _ h
  intro x w hw i
  exact (Finset.single_le_sum (f:=fun j => bits (w j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hw

theorem short_of_mem_Dcoord {L : Language} (hl : L ∈ Dcoord) : Short (fun z : Env Unit => z () ∈ L) := by
  obtain ⟨r,q,P,h⟩ := hl
  apply short_guarded q P (fun x w => ∀ i, bits (w i) ≤ q.eval (bits x)) _ (fun _ _ e => e) h
  exact Short.all (fun i => one_cut (Sum.inl () : Unit ⊕ Fin r) (Sum.inr i) q)

private theorem coord_of_short {L : Language} (hs : Short (fun z : Env Unit => z () ∈ L)) :
    ∃ (r : ℕ) (q : Polynomial ℕ) (P : MvPolynomial (Option (Fin r)) ℤ),
      (∀ x w, polyValue P x w = 0 → x ∈ L) ∧
      ∀ x ∈ L, ∃ w, Fits (q.eval (bits x)) w ∧ polyValue P x w=0 := by
  classical
  obtain ⟨W,fw,q,Q,sound,complete⟩ := hs
  letI := fw
  let e := Fintype.equivFin W
  let f : Unit ⊕ W → Option (Fin (Fintype.card W)) := Sum.elim (fun _ => none) (some ∘ e)
  let P := rename f Q
  have hv x w : polyValue P x w = eval (Sum.elim (ints (fun _ : Unit => x)) (ints (w ∘ e))) Q := by
    have agree {T : Type} (u : T → ℤ) (A : MvPolynomial T ℤ) : aeval u A=eval u A :=
      DFunLike.congr_fun (coe_aeval_eq_eval u) A
    rw [polyValue,agree,show P=rename f Q from rfl,eval_rename]
    apply congrArg (fun g => eval g Q)
    funext i; cases i <;> rfl
  refine ⟨_,q,P,fun x w hw => sound (fun _ => x) (w ∘ e) ((hv _ _).symm.trans hw),?_⟩
  intro x hx
  obtain ⟨w,hw,he⟩ := complete (bits x) (fun _ => x) (fun _ => le_rfl) hx
  exact ⟨w ∘ e.symm,fun i => hw (e.symm i),by simpa [hv,Function.comp_def] using he⟩

theorem Dcoord_eq_D : Dcoord = D := by
  ext L; constructor
  · exact fun h => (short_of_mem_Dcoord h).mem_D
  · intro h
    obtain ⟨r,q,P,hs,hc⟩ := coord_of_short (short_of_mem_D h)
    exact ⟨r,q,P,fun x => ⟨hc x,fun ⟨w,_,hw⟩ => hs x w hw⟩⟩

private theorem power_cut_iff (w h : ℕ) :
    w ≤ 2^h ↔ w ≤ 1 ∨ ∃ v, bits v ≤ h ∧ v+1=w := by
  constructor
  · intro hw
    by_cases hsmall : w≤1
    · exact Or.inl hsmall
    · right
      let v := w-1
      have hp : v≠0 := by dsimp [v]; omega
      have hv : v<2^h := by dsimp [v]; omega
      exact ⟨v,Nat.succ_le_of_lt ((Nat.log2_lt hp).2 hv),by dsimp [v]; omega⟩
  · rintro (hw|⟨v,hv,rfl⟩)
    · exact hw.trans (Nat.one_le_two_pow)
    · exact (Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) hv))

private theorem power_cut {σ : Type} (x y : σ) (p : Polynomial ℕ) :
    Short (fun z : Env σ => z y ≤ 2^(p.eval (bits (z x)))) := by
  have small : Short (fun z : Env σ => z y ≤ 1) := by
    apply (Short.formula (.nonnegative (1-X y))).congr
    intro z; simp [Compiler.Formula.Holds,ints]
  let S : Relation (σ ⊕ Unit) := fun z =>
    bits (z (.inr ())) ≤ p.eval (bits (z (.inl x))) ∧ z (.inr ())+1=z (.inl y)
  have check : Short S := by
    apply Short.and (one_cut (Sum.inl x) (Sum.inr ()) p)
    apply (Short.formula (.zero (X (.inr ()) + 1 - X (.inl y)))).congr
    intro z
    simp only [Compiler.Formula.Holds,map_sub,map_add,map_one,eval_X,ints,sub_eq_zero]
    norm_cast
  have large : Short (fun z : Env σ => ∃ v, bits v ≤ p.eval (bits (z x)) ∧ v+1=z y) := by
    apply Short.exists_of S check Polynomial.X
    · exact fun _ w h => ⟨w (),h⟩
    · rintro h z hz ⟨v,hv,he⟩
      refine ⟨fun _ => v,fun _ => ?_,hv,he⟩
      simpa using (FourSquare.bits_mono (by omega : v≤z y)).trans (hz y)
  exact (small.either large).congr (fun z => (power_cut_iff _ _).symm)

theorem short_of_mem_Dpower {L : Language} (hl : L ∈ Dpower) : Short (fun z : Env Unit => z () ∈ L) := by
  obtain ⟨r,q,P,h⟩ := hl
  apply short_guarded (q+1) P (fun x w => ∀ i, w i ≤ 2^(q.eval (bits x))) _ _ h
  · exact Short.all (fun i => power_cut (Sum.inl () : Unit ⊕ Fin r) (Sum.inr i) q)
  · intro x w hc i
    simpa only [bits,Nat.log2_two_pow,Polynomial.eval_add,Polynomial.eval_one] using
      (FourSquare.bits_mono (hc i))

theorem Dpower_eq_D : Dpower = D := by
  ext L; constructor
  · exact fun h => (short_of_mem_Dpower h).mem_D
  · intro h
    obtain ⟨r,q,P,hs,hc⟩ := coord_of_short (short_of_mem_D h)
    refine ⟨r,q,P,fun x => ⟨?_,fun ⟨w,_,hw⟩ => hs x w hw⟩⟩
    intro hx
    obtain ⟨w,hw,he⟩ := hc x hx
    exact ⟨w,fun i => Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (hw i)),he⟩

end
end DiophantineNP.Classes
