import DiophantineNP.JonesMachine

/-! # An exact register presentation of a finite TM2 computation

Each reachable stack uses a fixed radix and one natural register. At a push the
new register is `digit + radix * old`, and at a pop the new register is
`old / radix`. The top symbol is a finite lookup on `old % radix`.
-/
namespace DiophantineNP.Classes.Jones.Machine
open Turing
open scoped Classical

noncomputable def digit (tm : FinTM2) (a : Symbol tm) : ℕ :=
  if h : a ∈ alphabet tm then (Fintype.equivFin ↥(alphabet tm) ⟨a,h⟩).val + 1 else 0

noncomputable def blockSize (tm : FinTM2) := bits (alphabet tm).card
noncomputable def radix (tm : FinTM2) := 2 ^ blockSize tm

private theorem radix_pos (tm : FinTM2) : 0 < radix tm := by unfold radix; positivity

theorem digit_pos (tm : FinTM2) {a : Symbol tm} (ha : a ∈ alphabet tm) : 0 < digit tm a := by
  simp [digit,ha]

theorem digit_lt (tm : FinTM2) (a : Symbol tm) : digit tm a < radix tm := by
  by_cases h : a ∈ alphabet tm
  · have hi := (Fintype.equivFin ↥(alphabet tm) ⟨a,h⟩).isLt
    have hc := Fintype.card_coe (alphabet tm)
    exact (show digit tm a ≤ (alphabet tm).card by simp only [digit,dif_pos h]; omega).trans_lt Nat.lt_log2_self
  · simpa [digit,h] using radix_pos tm

private theorem digit_inj (tm : FinTM2) {a b : Symbol tm} (ha : a ∈ alphabet tm)
    (hb : b ∈ alphabet tm) (h : digit tm a = digit tm b) : a = b := by
  simp only [digit,dif_pos ha,dif_pos hb,Nat.add_right_cancel_iff] at h
  exact congrArg Subtype.val ((Fintype.equivFin ↥(alphabet tm)).injective (Fin.ext h))

noncomputable def stackCode (tm : FinTM2) (k : tm.K) : List (tm.Γ k) → ℕ
  | [] => 0
  | a :: s => digit tm ⟨k,a⟩ + radix tm * stackCode tm k s

private theorem code_head (tm : FinTM2) (k : tm.K) (a : tm.Γ k) (s) :
    stackCode tm k (a :: s) % radix tm = digit tm ⟨k,a⟩ := by
  simp [stackCode, Nat.mod_eq_of_lt (digit_lt tm ⟨k,a⟩)]

private theorem code_tail (tm : FinTM2) (k : tm.K) (s : List (tm.Γ k)) :
    stackCode tm k s / radix tm = stackCode tm k s.tail := by
  cases s with
  | nil => simp [stackCode]
  | cons a l =>
    simp [stackCode, Nat.add_mul_div_left _ _ (radix_pos tm), Nat.div_eq_of_lt (digit_lt tm ⟨k,a⟩)]

theorem stackCode_lt (tm : FinTM2) (k : tm.K) (s : List (tm.Γ k)) :
    stackCode tm k s < radix tm ^ s.length := by
  induction s with
  | nil => simp [stackCode]
  | cons a s ih =>
    simp only [stackCode,List.length_cons, pow_succ]
    calc digit tm ⟨k,a⟩ + radix tm * stackCode tm k s < radix tm * (stackCode tm k s + 1) := by
            rw [Nat.mul_add,Nat.mul_one]; have := digit_lt tm ⟨k,a⟩; omega
      _ ≤ radix tm * radix tm ^ s.length := Nat.mul_le_mul_left _ ih
      _ = _ := Nat.mul_comm ..

theorem stackCode_size (tm : FinTM2) (k : tm.K) (s : List (tm.Γ k)) :
    (stackCode tm k s).size ≤ blockSize tm * s.length := by
  apply Nat.size_le.mpr
  rw [pow_mul]
  exact stackCode_lt tm k s

/-- Read a residue against the fixed finite alphabet of stack k. -/
noncomputable def peekValue (tm : FinTM2) (k : tm.K) (n : ℕ) : Option (tm.Γ k) :=
  if h : ∃ a : tm.Γ k, (⟨k,a⟩ : Symbol tm) ∈ alphabet tm ∧ digit tm ⟨k,a⟩ = n % radix tm
    then some (Classical.choose h) else none

private theorem peekValue_code (tm : FinTM2) (k : tm.K) (s : List (tm.Γ k))
    (hs : ∀ a ∈ s, (⟨k,a⟩ : Symbol tm) ∈ alphabet tm) :
    peekValue tm k (stackCode tm k s) = s.head? := by
  cases s with
  | nil =>
    simp only [peekValue,stackCode,Nat.zero_mod,List.head?_nil]
    split_ifs with ex
    · obtain ⟨a,ha,hz⟩ := ex; have := digit_pos tm ha; omega
    · rfl
  | cons a s =>
    simp only [peekValue,code_head,List.head?_cons]
    have ha := hs a (List.mem_cons_self)
    split_ifs with h
    · apply congrArg some
      obtain ⟨hh,hd⟩ := Classical.choose_spec h
      exact sigma_mk_injective (digit_inj tm hh ha hd)
    · exact (h ⟨a,ha,rfl⟩).elim

theorem stackCode_inj (tm : FinTM2) (k : tm.K) (s t : List (tm.Γ k))
    (hs : ∀ a ∈ s, (⟨k,a⟩ : Symbol tm) ∈ alphabet tm)
    (ht : ∀ a ∈ t, (⟨k,a⟩ : Symbol tm) ∈ alphabet tm)
    (he : stackCode tm k s = stackCode tm k t) : s = t := by
  induction s generalizing t with
  | nil =>
    have hh := (peekValue_code tm k [] hs).symm.trans
      ((congrArg (peekValue tm k) he).trans (peekValue_code tm k t ht))
    cases t <;> simp_all
  | cons a s ih =>
    have hh := (peekValue_code tm k (a :: s) hs).symm.trans
        ((congrArg (peekValue tm k) he).trans (peekValue_code tm k t ht))
    have htail := (code_tail tm k (a :: s)).symm.trans
        ((congrArg (fun v => v / radix tm) he).trans (code_tail tm k t))
    cases t with
    | nil => simp at hh
    | cons b t =>
      simp only [List.head?_cons,Option.some.injEq] at hh
      subst b
      exact congrArg (a :: ·) (ih t (fun i hi => hs i (List.mem_cons_of_mem _ hi))
        (fun i hi => ht i (List.mem_cons_of_mem _ hi)) htail)

/-- Finite control and one natural-number register per machine stack. -/
structure Registers (tm : FinTM2) where
  label : Option tm.Λ
  state : tm.σ
  stack : tm.K → ℕ

noncomputable def encode (tm : FinTM2) (c : tm.Cfg) : Registers tm :=
  ⟨c.l,c.var,fun k => stackCode tm k (c.stk k)⟩

theorem encode_inj_on (tm : FinTM2) {c d : tm.Cfg} (hc : Supported tm c.stk)
    (hd : Supported tm d.stk) (he : encode tm c = encode tm d) : c = d := by
  obtain ⟨l,s,S⟩ := c
  obtain ⟨m,t,T⟩ := d
  have hl : l = m := congrArg Registers.label he
  have hs : s = t := congrArg Registers.state he
  have hS : S = T := funext fun k => stackCode_inj tm k _ _ (hc k) (hd k)
    (congrArg (fun x : Registers tm => x.stack k) he)
  cases hl; cases hs; cases hS; rfl

/-- A linear storage bound in the input length and number of TM2 macrosteps. -/
theorem reachable_register_size (tm : FinTM2) (s : List (tm.Γ tm.k₀)) (n : ℕ) (c : tm.Cfg)
    (hr : (fun v : Option tm.Cfg => v.bind tm.step)^[n] (some (initList tm s)) = some c)
    (k : tm.K) : ((encode tm c).stack k).size ≤ blockSize tm * (s.length+n*perStep tm) :=
  (stackCode_size tm k (c.stk k)).trans (Nat.mul_le_mul_left _ ((reachable_stacks tm s n c hr).2 k))

/-- The register program follows the fixed syntax of a TM2 macroinstruction. -/
noncomputable def regAux (tm : FinTM2) : tm.Stmt → tm.σ → (tm.K → ℕ) → Registers tm
  | .push k f q, s, R => regAux tm q s (Function.update R k (digit tm ⟨k,f s⟩ + radix tm * R k))
  | .peek k f q, s, R => regAux tm q (f s (peekValue tm k (R k))) R
  | .pop k f q, s, R => regAux tm q (f s (peekValue tm k (R k))) (Function.update R k (R k / radix tm))
  | .load f q, s, R => regAux tm q (f s) R
  | .branch f q₁ q₂, s, R => cond (f s) (regAux tm q₁ s R) (regAux tm q₂ s R)
  | .goto f, s, R => ⟨some (f s),s,R⟩
  | .halt, s, R => ⟨none,s,R⟩

noncomputable def regStep (tm : FinTM2) : Registers tm → Option (Registers tm)
  | ⟨none,_,_⟩ => none
  | ⟨some l,s,R⟩ => some (regAux tm (tm.m l) s R)

private theorem codes_update (tm : FinTM2) (S : Stacks tm) (k : tm.K) (s : List (tm.Γ k)) :
    (fun j => stackCode tm j (Function.update S k s j)) =
      Function.update (fun j => stackCode tm j (S j)) k (stackCode tm k s) := by
  funext j
  by_cases h : j=k
  · subst j; simp
  · simp [Function.update_of_ne h]

theorem regAux_exact (tm : FinTM2) (q : tm.Stmt) (h : pushed tm q ⊆ alphabet tm)
    (s : tm.σ) (S : Stacks tm) (hs : Supported tm S) :
    regAux tm q s (fun j => stackCode tm j (S j)) = encode tm (TM2.stepAux q s S) := by
  induction q generalizing s S with
  | push k f q ih =>
    have h' : Supported tm (Function.update S k (f s :: S k)) := by
      apply support_update tm hs
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ht
      · exact support_push tm h s
      · exact hs k a ht
    have hh := ih (Finset.Subset.trans Finset.subset_union_right h) s _ h'
    rw [codes_update] at hh
    exact hh
  | peek k f q ih =>
    simp only [regAux,TM2.stepAux,peekValue_code tm _ _ (hs k)]
    exact ih h _ S hs
  | pop k f q ih =>
    have h' := support_update tm hs k (S k).tail (fun a ha => hs k a (List.mem_of_mem_tail ha))
    have hh := ih h (f s (S k).head?) _ h'
    simp only [regAux,TM2.stepAux,peekValue_code tm _ _ (hs k),code_tail]
    rwa [codes_update] at hh
  | load f q ih => exact ih h _ S hs
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases e : f s
    · simp only [regAux,TM2.stepAux,e,cond_false]
      exact ih₂ (Finset.Subset.trans Finset.subset_union_right h) s S hs
    · simp only [regAux,TM2.stepAux,e,cond_true]
      exact ih₁ (Finset.Subset.trans Finset.subset_union_left h) s S hs
  | goto f => rfl
  | halt => rfl

theorem regStep_exact (tm : FinTM2) (c : tm.Cfg) (hc : Supported tm c.stk) :
    regStep tm (encode tm c) = (tm.step c).map (encode tm) := by
  obtain ⟨l,s,S⟩ := c
  cases l with
  | none => rfl
  | some l => exact congrArg some (regAux_exact tm (tm.m l) (pushed_sub tm l) s S hc)

/-- Starting on an encoded input, the register program and original TM2
machine agree at every time, including past termination. -/
theorem regRun_exact (tm : FinTM2) (s : List (tm.Γ tm.k₀)) (n : ℕ) :
    (fun v : Option (Registers tm) => v.bind (regStep tm))^[n] (some (encode tm (initList tm s))) =
      ((fun v : Option tm.Cfg => v.bind tm.step)^[n] (some (initList tm s))).map (encode tm) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply',ih]
    cases he : (fun v : Option tm.Cfg => v.bind tm.step)^[n] (some (initList tm s)) with
    | none => rfl
    | some c => exact regStep_exact tm c (reachable_stacks tm s n c he).1

end DiophantineNP.Classes.Jones.Machine
