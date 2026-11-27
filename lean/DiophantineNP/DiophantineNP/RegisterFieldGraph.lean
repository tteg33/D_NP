import DiophantineNP.RegisterFieldPacking
import DiophantineNP.BoundedRelation
import DiophantineNP.TracePorts

/-! # Diophantine compilation of the native input framing

An accepting packed row table for a single field has low-order bit transitions
and a fixed delimiter. Its visible capacity and clock may be chosen with
polynomially many bits in the enclosing field's three numerical parameters.
Intermediate field boundaries fit in the original stack register.
-/
namespace DiophantineNP.Classes.Jones.Machine
open BoundedRelation MvPolynomial JMTableau
noncomputable section

private def wiring (M : VerifierMachine) : (fieldTable M).Port → (Fin 3 ⊕ Fin 4)
  | .first j => ![Sum.inl 0,Sum.inl 1] j
  | .last j => ![Sum.inr 0,Sum.inr 1] j
  | .capacity => .inr 2
  | .clock => .inr 3

private theorem wiring_spec (M : VerifierMachine) (z : Env (Fin 3 ⊕ Fin 4)) :
    (fieldTable M).Accepts (z ∘ wiring M) ↔ ∃ n v, z (.inr 2)=2^v ∧
      z (.inr 3)=2^(((fieldTable M).guard+v)*n) ∧
      (∀ j : Fin 2, pairRegs (z (.inl 0)) (z (.inl 1)) j < 2^v ∧
        pairRegs (z (.inr 0)) (z (.inr 1)) j < 2^v) ∧
      (fieldTable M).Run n v (pairRegs (z (.inl 0)) (z (.inl 1)))
        (pairRegs (z (.inr 0)) (z (.inr 1))) := by
  have f (j : Fin 2) : (z ∘ wiring M) (.first j) = pairRegs (z (.inl 0)) (z (.inl 1)) j := by
    fin_cases j <;> rfl
  have l (j : Fin 2) : (z ∘ wiring M) (.last j) = pairRegs (z (.inr 0)) (z (.inr 1)) j := by
    fin_cases j <;> rfl
  simp only [TraceTable.Accepts,f,l]; rfl

private def EndCheck (M : VerifierMachine) (z : Env (Fin 3 ⊕ Fin 4)) :=
  z (.inr 0) = 0 ∧ z (.inr 1) = inputDigit M none + radix M.tm * z (.inl 2)

private theorem short_end (M : VerifierMachine) : Short (EndCheck M) := by
  let p : MvPolynomial (Fin 3 ⊕ Fin 4) ℤ := X (.inr 1) -
    (C (inputDigit M none : ℤ) + C (radix M.tm : ℤ) * X (.inl 2))
  apply (Short.formula (.both (.zero (X (.inr 0))) (.zero p))).congr
  intro z
  simp only [Compiler.Formula.Holds,EndCheck,p,ints,eval_X,map_sub,map_add,map_mul,eval_C,sub_eq_zero]
  norm_cast

/-- The relation on three natural coordinates: field value, stack at its
start, and stack remaining after its delimiter. -/
def FieldGraph (M : VerifierMachine) (x : Env (Fin 3)) :=
  x 1 = prefixCode M (field (x 0)) (x 2)

/-- Discharge all input-specific budgets needed to project the packed-table
graph to three external field registers. -/
theorem fieldGraph_short_of_table (M : VerifierMachine) (ht : Short (fieldTable M).Accepts) :
    Short (FieldGraph M) := by
  let S : Relation (Fin 3 ⊕ Fin 4) := fun z => (fieldTable M).Accepts (z ∘ wiring M) ∧ EndCheck M z
  have hS : Short S := Short.and (ht.reindex (wiring M)) (short_end M)
  let G := (fieldTable M).guard
  let p : Polynomial ℕ := (Polynomial.C (G+3)+Polynomial.X)^2
  apply Short.exists_of S hS p
  · intro x u s
    obtain ⟨r,eq⟩ := s
    obtain ⟨n,v,_,_,bound,run⟩ := (wiring_spec ..).mp r
    change u 0 = 0 ∧ u 1 = inputDigit M none + radix M.tm * x 2 at eq
    change (fieldTable M).Run _ _ (pairRegs (x 0) (x 1)) (pairRegs (u 0) (u 1)) at run
    rw [eq.1,eq.2] at run
    exact ((fieldTable_iff M n v _ _ _ (bound 0).1 (bound 1).1).mp run).2
  · intro h x hx yes
    let n := (x 0).size
    let E := inputDigit M none + radix M.tm * x 2
    let u : Env (Fin 4) := ![0,E,2^h,2^((G+h)*n)]
    have hn : n ≤ h := (Nat.size_le.mpr Nat.lt_log2_self).trans (hx 0)
    have xb (j : Fin 3) : x j < 2^h := Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) (hx j))
    have ar := (fieldRows_iff M n (x 0) (x 1) (x 2)).mpr ⟨rfl,yes⟩
    obtain ⟨rows,h₀,h₁,step⟩ := ar
    have hrow := readerRows_bound M rows step (Fin.last n)
    rw [h₁,h₀] at hrow
    have eb : E ≤ x 1 := hrow.2
    have heBits := (FourSquare.bits_mono eb).trans (hx 1)
    have hclock : (G+h)*n ≤ (G+h)*h := Nat.mul_le_mul_left _ hn
    refine ⟨u,?_,(wiring_spec ..).mpr ⟨n,h,rfl,rfl,?_,?_⟩,rfl,rfl⟩
    · intro i
      fin_cases i <;> simp [u,bits,Nat.log2_two_pow,p] <;> dsimp [bits] at heBits <;> nlinarith
    · intro j; fin_cases j
      · exact ⟨xb 0,Nat.two_pow_pos _⟩
      · exact ⟨xb 1,eb.trans_lt (xb 1)⟩
    · exact (fieldTable_iff M n h _ _ _ (xb 0) (xb 1)).mpr ⟨rfl,yes⟩

private theorem tail_le (M : VerifierMachine) (s : List (Option Bool)) (t : ℕ) : t ≤ prefixCode M s t := by
  induction s with
  | nil => exact le_rfl
  | cons b s ih =>
    have hp : 0 < radix M.tm := by unfold radix; positivity
    exact ih.trans ((Nat.le_mul_of_pos_left _ hp).trans (Nat.le_add_left ..))

/-- Glue any fixed list of field readers with intermediate boundary registers.
Every guessed boundary is a suffix of the preceding input stack. -/
private theorem readChain_short {σ : Type} (M : VerifierMachine) (hf : Short (FieldGraph M)) (vs : List σ) :
    ∀ {τ : Type} (f : σ → τ) (a b : τ),
      Short (fun z : Env τ => ReadFields M (vs.map (fun i => z (f i))) (z a) (z b)) := by
  induction vs with
  | nil =>
    intro τ f a b
    apply (Short.formula (.zero (X a - X b))).congr
    intro z; simp [Compiler.Formula.Holds,ReadFields,ints,sub_eq_zero]
  | cons v vs ih =>
    intro τ f a b
    let g : Fin 3 → τ ⊕ Unit := ![Sum.inl (f v),Sum.inl a,Sum.inr ()]
    let S : Relation (τ ⊕ Unit) := fun z => FieldGraph M (z ∘ g) ∧
      ReadFields M (vs.map (fun i => z (.inl (f i)))) (z (.inr ())) (z (.inl b))
    have hS : Short S := Short.and (hf.reindex g) (ih (Sum.inl ∘ f) (.inr ()) (.inl b))
    apply Short.exists_of S hS Polynomial.X
    · intro z u h
      obtain ⟨e,t⟩ := h
      exact ⟨(z (f v)).size,u (),(fieldRows_iff M ..).mpr ⟨rfl,e⟩,t⟩
    · intro h z hz yes
      obtain ⟨n,mid,e,t⟩ := yes
      have eqn := ((fieldRows_iff M ..).mp e).2
      have hm : mid ≤ z a := eqn ▸ tail_le M _ _
      exact ⟨fun _ => mid,fun _ => by simpa using (FourSquare.bits_mono hm).trans (hz a),eqn,t⟩

/-- The native framed input has a globally sound, short-witness graph, after
compiling the one fixed field-reader table for the verifier alphabet. -/
theorem initialStack_short_of_table (M : VerifierMachine) (ht : Short (fieldTable M).Accepts)
    {σ : Type} (x : σ) {r : ℕ} (w : Fin r → σ) (s : σ) :
    Short (fun z : Env σ => z s = stackCode M.tm M.tm.k₀ (verifierInput M (tape (z x) (z ∘ w)))) := by
  let vs := x :: List.ofFn w
  let S : Relation (σ ⊕ Unit) := fun z =>
    ReadFields M (vs.map (fun i => z (.inl i))) (z (.inl s)) (z (.inr ())) ∧ z (.inr ()) = 0
  have zero : Short (fun z : Env (σ ⊕ Unit) => z (.inr ()) = 0) :=
    (Short.formula (.zero (X (.inr ())))).congr (fun z => by simp [Compiler.Formula.Holds,ints])
  have hS : Short S := Short.and (readChain_short M (fieldGraph_short_of_table M ht) vs Sum.inl (.inl s) (.inr ())) zero
  apply Short.exists_of S hS 1
  · intro z u h
    obtain ⟨hc,hz⟩ := h
    change u ()=0 at hz
    change ReadFields M (vs.map z) (z s) (u ()) at hc
    rw [hz] at hc
    apply (readTape_iff M (z x) (z ∘ w) _).mp
    simpa [vs,List.map_ofFn] using hc
  · intro h z hz he
    refine ⟨fun _ => 0,fun _ => by simp [bits],?_,rfl⟩
    change ReadFields M (vs.map z) (z s) 0
    simpa [vs,List.map_ofFn] using (readTape_iff M (z x) (z ∘ w) _).mpr he

end
end DiophantineNP.Classes.Jones.Machine
