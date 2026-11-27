import DiophantineNP.NaturalBridge
import DiophantineNP.ConstraintCost

/-! # Composing fixed, globally sound natural relations with short witnesses -/
namespace DiophantineNP.BoundedRelation
open MvPolynomial

abbrev Env (σ : Type) := σ → ℕ
abbrev Relation (σ : Type) := Env σ → Prop

def ints {σ : Type} (x : Env σ) : σ → ℤ := fun i => x i

def Fits {σ : Type} (h : ℕ) (x : Env σ) := ∀ i, bits (x i) ≤ h

/-- A single fixed integer polynomial works on all input tuples. An honest
assignment needs a polynomial number of bits per auxiliary coordinate. -/
def Short {σ : Type} (R : Relation σ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (p : Polynomial ℕ) (P : MvPolynomial (σ ⊕ W) ℤ),
    (∀ x w, eval (Sum.elim (ints x) (ints w)) P = 0 → R x) ∧
    ∀ h x, Fits h x → R x → ∃ w : Env W,
      Fits (p.eval h) w ∧ eval (Sum.elim (ints x) (ints w)) P = 0

variable {σ τ : Type} {R S : Relation σ}

namespace Short

theorem congr (h : Short R) (e : ∀ x, R x ↔ S x) : Short S := by
  obtain ⟨W,hw,p,P,hs,hc⟩ := h
  exact ⟨W,hw,p,P,fun x w eq => (e x).mp (hs x w eq),
    fun h x hx yes => hc h x hx ((e x).mpr yes)⟩

theorem reindex (h : Short R) (f : σ → τ) : Short (fun x => R (x ∘ f)) := by
  obtain ⟨W,hw,p,P,hs,hc⟩ := h
  let g : σ ⊕ W → τ ⊕ W := Sum.map f id
  have ev x w : eval (Sum.elim (ints x) (ints w)) (rename g P) =
      eval (Sum.elim (ints (x ∘ f)) (ints w)) P := by
    rw [eval_rename]; apply congrArg (fun y => eval y P); funext i; cases i <;> rfl
  exact ⟨W,hw,p,rename g P,fun x w e => hs _ _ ((ev _ _).symm.trans e),
    fun h x hx yes => by simpa only [ev] using hc h _ (fun i => hx (f i)) yes⟩

/-- A fixed finite conjunction uses a separate witness block for each index. -/
theorem all {ι : Type} [Fintype ι] {A : ι → Relation σ} (h : ∀ i, Short (A i)) :
    Short (fun x => ∀ i, A i x) := by
  classical
  choose W inst p P hs hc using h
  letI (i : ι) : Fintype (W i) := inst i
  let g (i : ι) : σ ⊕ W i → σ ⊕ Σ i, W i := Sum.map id (Sigma.mk i)
  let Q := ∑ i, (rename (g i) (P i))^2
  have ev (x : Env σ) (w : Env (Σ i, W i)) :
      eval (Sum.elim (ints x) (ints w)) Q=0 ↔
      ∀ i, eval (Sum.elim (ints x) (ints (w ∘ Sigma.mk i))) (P i)=0 := by
    have ei (i : ι) : eval (Sum.elim (ints x) (ints w)) (rename (g i) (P i)) =
        eval (Sum.elim (ints x) (ints (w ∘ Sigma.mk i))) (P i) := by
      rw [eval_rename]; apply congrArg (fun y => eval y (P i)); funext j; cases j <;> rfl
    simp [Q,pow_two,Finset.sum_mul_self_eq_zero_iff,ei]
  refine ⟨Σ i, W i,inferInstance,∑ i, p i,Q,fun x w eq i => hs i x _ ((ev x w).mp eq i),?_⟩
  intro h x hx yes
  choose w hw he using fun i => hc i h x hx (yes i)
  refine ⟨fun i => w i.1 i.2,?_,(ev _ _).mpr he⟩
  intro i
  simp only [Polynomial.eval_finset_sum]
  exact (hw i.1 i.2).trans (Finset.single_le_sum (f:=fun j => (p j).eval h) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i.1))

theorem and (hr : Short R) (hs : Short S) : Short (fun x => R x ∧ S x) := by
  let A : Bool → Relation σ := fun b => if b then S else R
  have hh (b : Bool) : Short (A b) := by cases b <;> simp_all [A]
  exact (all hh).congr (fun x => by simp [A,Bool.forall_bool])

theorem either (hr : Short R) (ht : Short S) : Short (fun x => R x ∨ S x) := by
  obtain ⟨U,iu,p,P,hs,hc⟩ := hr
  obtain ⟨V,iv,q,Q,js,jc⟩ := ht
  letI := iu
  letI := iv
  let f : σ ⊕ U → σ ⊕ (U ⊕ V) := Sum.map id Sum.inl
  let g : σ ⊕ V → σ ⊕ (U ⊕ V) := Sum.map id Sum.inr
  let F := rename f P * rename g Q
  have ev (x : Env σ) (w : Env (U⊕V)) : eval (Sum.elim (ints x) (ints w)) F = 0 ↔
      eval (Sum.elim (ints x) (ints (w ∘ Sum.inl))) P=0 ∨
      eval (Sum.elim (ints x) (ints (w ∘ Sum.inr))) Q=0 := by
    simp only [F,map_mul,mul_eq_zero,eval_rename]
    have H {A : Type} (k : A → U⊕V) : Sum.elim (ints x) (ints w) ∘ Sum.map id k = Sum.elim (ints x) (ints (w ∘ k)) := by funext i; cases i <;> rfl
    simp only [f,g,H]
  refine ⟨U⊕V,inferInstance,p+q+1,F,fun x w e => ((ev x w).mp e).imp (hs x _) (js x _),?_⟩
  intro h x hx yes
  rcases yes with a|a
  · obtain ⟨u,hu,eu⟩ := hc h x hx a
    refine ⟨Sum.elim u (fun _ => 0),?_,(ev _ _).mpr (Or.inl eu)⟩
    rintro (i|i)
    · simpa using (hu i).trans (show p.eval h ≤ p.eval h + q.eval h + 1 by omega)
    · simp [bits]
  · obtain ⟨v,hv,ev'⟩ := jc h x hx a
    refine ⟨Sum.elim (fun _ => 0) v,?_,(ev _ _).mpr (Or.inr ev')⟩
    rintro (i|i)
    · simp [bits]
    · simpa using (hv i).trans (show q.eval h ≤ p.eval h + q.eval h + 1 by omega)

/-- Existence can introduce any fixed finite tuple, provided true inputs have
short choices. Both the quantified tuple and its checking witnesses are paid. -/
theorem exists_of {R : Relation σ} [Fintype τ] (S : Relation (σ ⊕ τ)) (hS : Short S)
    (p : Polynomial ℕ) (hsound : ∀ x w, S (Sum.elim x w) → R x)
    (hyes : ∀ h x, Fits h x → R x → ∃ w, Fits (p.eval h) w ∧ S (Sum.elim x w)) : Short R := by
  obtain ⟨V,iv,q,Q,js,jc⟩ := hS
  letI := iv
  let g : (σ⊕τ)⊕V → σ⊕(τ⊕V) := (Equiv.sumAssoc σ τ V)
  have ev (x : Env σ) (a : Env (τ⊕V)) :
      eval (Sum.elim (ints x) (ints a)) (rename g Q) =
      eval (Sum.elim (ints (Sum.elim x (a ∘ Sum.inl))) (ints (a ∘ Sum.inr))) Q := by
    rw [eval_rename]; apply congrArg (fun y => eval y Q); funext j; rcases j with (j|j)|j <;> rfl
  let b := Polynomial.X + p
  refine ⟨τ⊕V,inferInstance,p+q.comp b,rename g Q,fun x a e => hsound _ _ (js _ _ ((ev x a).symm.trans e)),?_⟩
  intro h x hx yes
  obtain ⟨u,hu,eu⟩ := hyes h x hx yes
  have hu' : Fits (b.eval h) (Sum.elim x u) := by
    rintro (i|i) <;> simp [b] <;> first | exact (hx i).trans (Nat.le_add_right ..) | exact (hu i).trans (Nat.le_add_left ..)
  obtain ⟨v,hv,ev'⟩ := jc _ _ hu' eu
  refine ⟨Sum.elim u v,?_,(ev ..).trans ev'⟩
  rintro (i|i) <;> simp [Polynomial.eval_comp] <;> first | exact (hu i).trans (Nat.le_add_right ..) | exact (hv i).trans (Nat.le_add_left ..)

/-- A fixed relation may equivalently be certified by signed coordinates.
Positive/negative parts introduce exactly the sign bit already counted. -/
theorem of_signed {W : Type} [Fintype W] (P : MvPolynomial (σ⊕W) ℤ)
    (p : Polynomial ℕ) (hs : ∀ x w, eval (Sum.elim (ints x) w) P=0 → R x)
    (hc : ∀ h x, Fits h x → R x → ∃ w, intCost w ≤ p.eval h ∧ eval (Sum.elim (ints x) w) P=0) : Short R := by
  let g : σ⊕W → MvPolynomial (σ⊕(W⊕W)) ℤ := Sum.elim (fun i => X (.inl i))
    (fun j => X (.inr (.inl j)) - X (.inr (.inr j)))
  have ev x w : eval (Sum.elim (ints x) (ints w)) (bind₁ g P) = eval (Sum.elim (ints x) (decodeWitness w)) P := by
    rw [show eval (Sum.elim (ints x) (ints w)) (bind₁ g P) = eval (fun i => eval (Sum.elim (ints x) (ints w)) (g i)) P from eval₂Hom_bind₁ ..]
    apply congrArg (fun y => eval y P); funext i; cases i <;> simp [g,decodeWitness,ints]
  refine ⟨W⊕W,inferInstance,p,bind₁ g P,fun x w e => hs _ _ ((ev ..).symm.trans e),?_⟩
  intro h x hx yes
  obtain ⟨w,hw,he⟩ := hc h x hx yes
  refine ⟨splitWitness w,?_,by rw [ev,decode_split]; exact he⟩
  intro i
  exact (Finset.single_le_sum (f:=fun j => bits (splitWitness w j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans ((cost_split w).le.trans hw)

theorem formula (f : Compiler.Formula σ) : Short (fun x => f.Holds (ints x)) := by
  classical
  letI := Fintype.ofFinite f.Aux
  obtain ⟨K,hK⟩ := f.compile_linear_cost
  exact of_signed f.compile (Polynomial.C K*(Polynomial.X+1))
    (fun x w hw => (f.compile_exact _).mp ⟨w,hw⟩)
    (fun h x hx yes => by obtain ⟨w,he,hc⟩ := hK h (ints x) (fun i => by simpa [ints] using hx i) yes; exact ⟨w,by simpa using hc,he⟩)

theorem mask (native : NativeVerifier) : Short (fun x : Env Bool => BitIncl (x false) (x true)) := by
  obtain ⟨r,C,_,_,P,spec⟩ := native
  have ev (x : Env Bool) (w : Fin r → ℤ) : eval (Sum.elim (ints x) w) P = value P (x false) (x true) w := by
    have eqEval (f : Bool ⊕ Fin r → ℤ) : aeval f P = eval f P := DFunLike.congr_fun (coe_aeval_eq_eval f) P
    rw [value,eqEval]
    apply congrArg (fun v => eval v P); funext i; rcases i with (i|i)|i <;> rfl
  apply of_signed P ((Polynomial.X+2)^C)
  · intro x w e
    obtain ⟨hn,hf,ht⟩ := width_spec (x false) (x true)
    exact (spec _ _ _ hn hf ht).2 w ((ev ..).symm.trans e)
  · intro h x hx yes
    have pos : 1≤h := (by dsimp [bits]; omega : 1≤bits (x false)).trans (hx false)
    have H (i : Bool) : x i < 2^h := Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) (hx i))
    simpa [ev] using (spec h _ _ pos (H false) (H true)).1 yes

end Short

end DiophantineNP.BoundedRelation
