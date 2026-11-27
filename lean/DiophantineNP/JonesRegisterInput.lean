import DiophantineNP.JonesRegisterVerifier

/-! # Reading the framed verifier input with affine register equations

A transition consumes one low-order bit of a nonzero natural number and the
matching low-order symbol of a radix stack. Each field ends with a delimiter.
The fixed two bit branches are affine equations over naturals. Both registers
decrease weakly, and the number of transitions is the field's binary size.
-/
namespace DiophantineNP.Classes.Jones.Machine
open Turing Computability
noncomputable section

private def tag (M : VerifierMachine) (v : Option Bool) : ℕ :=
  digit M.tm ⟨M.tm.k₀,M.inputAlphabet.symm v⟩

/-- Encode a fixed prefix onto a tail register. -/
def prefixCode (M : VerifierMachine) : List (Option Bool) → ℕ → ℕ
  | [], tail => tail
  | b :: s, tail => tag M b + radix M.tm * prefixCode M s tail

private theorem prefix_append (M : VerifierMachine) (a b : List (Option Bool)) (tail : ℕ) :
    prefixCode M (a++b) tail = prefixCode M a (prefixCode M b tail) := by
  induction a with
  | nil => rfl
  | cons h t ih => simp only [List.cons_append,prefixCode,ih]

private theorem prefix_input (M : VerifierMachine) (s : List (Option Bool)) :
    prefixCode M s 0 = stackCode M.tm M.tm.k₀ (verifierInput M s) := by
  induction s with
  | nil => rfl
  | cons h s ih => change _ + _ * prefixCode M s 0 = _ + _ * stackCode M.tm M.tm.k₀ (verifierInput M s); rw [ih]; rfl

private theorem encode_pos (p : PosNum) : encodeNat (p:ℕ) = encodePosNum p := by
  rw [encodeNat,PosNum.of_to_nat]; rfl

private theorem encode_zero : encodeNat 0 = [] := by
  apply List.length_eq_zero_iff.mp
  rw [encodeNat_length,Nat.size_zero]

private theorem field_zero : field 0 = [none] := by
  change (encodeNat 0).map some ++ [(none : Option Bool)] = [(none : Option Bool)]
  rw [encode_zero]; rfl

private theorem encode_bit (n : ℕ) (b : Bool) (h : 0 < 2*n+b.toNat) :
    encodeNat (2*n+b.toNat) = b :: encodeNat n := by
  have e := Num.to_of_nat n
  generalize (n : Num) = t at e
  cases t with
  | zero =>
    change 0 = n at e
    subst n; cases b with
    | false => exact (Nat.lt_irrefl 0 h).elim
    | true =>
      change encodeNat (PosNum.one:ℕ) = true :: encodeNat 0
      rw [encode_pos,encode_zero]; rfl
  | pos p =>
    change (p : ℕ) = n at e
    subst n; cases b with
    | false =>
      have e : 2*(p:ℕ)+Bool.toNat false = (p.bit0:ℕ) := by rw [PosNum.cast_bit0]; simp; omega
      rw [e,encode_pos,encode_pos]; rfl
    | true =>
      have e : 2*(p:ℕ)+Bool.toNat true = (p.bit1:ℕ) := by rw [PosNum.cast_bit1]; simp; omega
      rw [e,encode_pos,encode_pos]; rfl

private theorem field_bit (n : ℕ) (b : Bool) (h : 0 < 2*n+b.toNat) :
    field (2*n+b.toNat) = some b :: field n := by
  change (encodeNat (2*n+b.toNat)).map some ++ [(none : Option Bool)] = some b :: ((encodeNat n).map some ++ [(none : Option Bool)])
  rw [encode_bit n b h]; rfl

private theorem size_bit (n : ℕ) (b : Bool) (h : 0 < 2*n+b.toNat) :
    (2*n+b.toNat).size = n.size + 1 := by
  rw [← encodeNat_length,encode_bit n b h,List.length_cons,encodeNat_length]

/-- Both alternatives require a nonzero remainder at the start of the row.
This excludes representations with redundant high zero bits. -/
def ReadBit (M : VerifierMachine) (old new : ℕ × ℕ) : Prop :=
  0 < old.1 ∧ ∃ b : Bool, old.1 = 2*new.1+b.toNat ∧
    old.2 = tag M (some b) + radix M.tm * new.2

/-- One trace of the two natural registers. -/
def ReaderRows (M : VerifierMachine) (n : ℕ) (a b : ℕ × ℕ) : Prop :=
  ∃ row : Fin (n+1) → ℕ × ℕ, row 0 = a ∧ row (Fin.last n) = b ∧
    ∀ i : Fin n, ReadBit M (row i.castSucc) (row i.succ)

private theorem rows_zero (M : VerifierMachine) (a b : ℕ × ℕ) : ReaderRows M 0 a b ↔ a=b := by
  constructor
  · rintro ⟨row,h₁,h₂,_⟩; exact h₁.symm.trans h₂
  · rintro rfl; exact ⟨fun _ => a,rfl,rfl,Fin.elim0⟩

private theorem rows_succ (M : VerifierMachine) (n : ℕ) (a b : ℕ × ℕ) :
    ReaderRows M (n+1) a b ↔ ∃ c, ReadBit M a c ∧ ReaderRows M n c b := by
  constructor
  · rintro ⟨row,h₁,h₂,h₃⟩
    refine ⟨row 1,?_,fun i => row i.succ,rfl,h₂,fun i => h₃ i.succ⟩
    rw [← h₁]; exact h₃ 0
  · rintro ⟨c,h,rows,h₁,h₂,h₃⟩
    refine ⟨Fin.cons a rows,rfl,?_,?_⟩
    · simpa only [Fin.cons_last] using h₂
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [h₁] using h
      · simpa only [← Fin.succ_castSucc,Fin.cons_succ] using h₃ j

/-- One field consumes its exact binary length and a final delimiter. -/
def FieldRows (M : VerifierMachine) (n value start tail : ℕ) : Prop :=
  ReaderRows M n (value,start) (0,tag M none + radix M.tm * tail)

theorem fieldRows_iff (M : VerifierMachine) (n value start tail : ℕ) :
    FieldRows M n value start tail ↔ n=value.size ∧ start=prefixCode M (field value) tail := by
  induction n generalizing value start with
  | zero =>
    rw [FieldRows,rows_zero,Prod.mk.injEq]
    constructor
    · rintro ⟨rfl,h⟩; rw [Nat.size_zero,field_zero]; exact ⟨rfl,h⟩
    · rintro ⟨hs,h⟩
      obtain rfl : value=0 := by by_contra hv; have := Nat.size_pos.mpr (Nat.pos_of_ne_zero hv); omega
      rw [field_zero] at h; exact ⟨rfl,h⟩
  | succ n ih =>
    rw [FieldRows,rows_succ]
    constructor
    · rintro ⟨⟨v,t⟩,⟨h,bit,he,hS⟩,rows⟩
      change value = 2*v+bit.toNat at he
      subst value
      obtain ⟨hn,ht⟩ := (ih v t).mp rows
      refine ⟨by rw [size_bit _ _ h,hn],?_⟩
      rw [field_bit _ _ h]; simpa [prefixCode,ht] using hS
    · rintro ⟨hn,hs⟩
      have hp : 0<value := Nat.size_pos.mp (by omega)
      let v := value/2
      let b := decide (value%2=1)
      have he : value=2*v+b.toNat := by by_cases hb : value%2=1 <;> simp [v,b,hb] <;> omega
      have hp' : 0<2*v+b.toNat := he ▸ hp
      refine ⟨(v,prefixCode M (field v) tail),⟨hp,b,he,?_⟩,(ih v _).mpr ⟨?_,rfl⟩⟩
      · rw [he,field_bit _ _ hp'] at hs; exact hs
      · rw [he,size_bit _ _ hp'] at hn; omega

/-- A fixed number of field readers can share their boundary registers. -/
def ReadFields (M : VerifierMachine) : List ℕ → ℕ → ℕ → Prop
  | [], start, tail => start=tail
  | v::vs, start, tail => ∃ n mid, FieldRows M n v start mid ∧ ReadFields M vs mid tail

theorem readFields_iff (M : VerifierMachine) (vs : List ℕ) (start tail : ℕ) :
    ReadFields M vs start tail ↔ start = prefixCode M ((vs.map field).flatten) tail := by
  induction vs generalizing start with
  | nil => rfl
  | cons v vs ih =>
    simp only [ReadFields,List.map_cons,List.flatten_cons,prefix_append,fieldRows_iff,ih]
    constructor
    · rintro ⟨_,_,⟨_,h⟩,rfl⟩; exact h
    · intro h; exact ⟨v.size,_,⟨rfl,h⟩,rfl⟩

/-- Exact consistency of the candidate initial stack and the native tuple of
numerical inputs, including zero fields and all delimiters. -/
theorem readTape_iff (M : VerifierMachine) {r : ℕ} (x : ℕ) (w : Fin r → ℕ) (s : ℕ) :
    ReadFields M (x :: List.ofFn w) s 0 ↔
      s = stackCode M.tm M.tm.k₀ (verifierInput M (tape x w)) := by
  rw [readFields_iff,← prefix_input]
  simp [tape,List.map_ofFn,Function.comp_def]

/-- The two registers in each field reader never exceed their initial values. -/
theorem readerRows_bound (M : VerifierMachine) {n : ℕ} (row : Fin (n+1) → ℕ×ℕ)
    (h : ∀ i : Fin n, ReadBit M (row i.castSucc) (row i.succ)) (j : Fin (n+1)) :
    (row j).1 ≤ (row 0).1 ∧ (row j).2 ≤ (row 0).2 := by
  induction j using Fin.induction with
  | zero => exact ⟨le_rfl,le_rfl⟩
  | succ i ih =>
    obtain ⟨_,b,hv,hs⟩ := h i
    have hp : 0 < radix M.tm := by unfold radix; positivity
    have le := Nat.le_mul_of_pos_left (row i.succ).2 hp
    exact ⟨(show (row i.succ).1 ≤ (row i.castSucc).1 by omega).trans ih.1,
      (show (row i.succ).2 ≤ (row i.castSucc).2 by omega).trans ih.2⟩

/-- Binary storage for the complete starting stack, uniformly in the input
and the honest certificate budget. -/
theorem reader_start_space (M : VerifierMachine) {r : ℕ} (x : ℕ) (w : Fin r → ℕ) :
    (stackCode M.tm M.tm.k₀ (verifierInput M (tape x w))).size ≤
      blockSize M.tm * (bits x+natCost w+(r+1)) := by
  have h := stackCode_size M.tm M.tm.k₀ (verifierInput M (tape x w))
  simp only [verifierInput,List.length_map] at h
  exact h.trans (Nat.mul_le_mul_left _ (tape_length_bounds x w).2)

/-- Arithmetic conditions on the first row of the register verifier. -/
def InitialFields (M : VerifierMachine) {r : ℕ} (x : ℕ) (w : Fin r → ℕ) (u : Registers M.tm) : Prop :=
  u.label = some M.tm.main ∧ u.state = M.tm.initialState ∧
    ReadFields M (x :: List.ofFn w) (u.stack M.tm.k₀) 0 ∧
    ∀ k, k ≠ M.tm.k₀ → u.stack k = 0

theorem initialFields_iff (M : VerifierMachine) {r : ℕ} (x : ℕ) (w : Fin r → ℕ) (u : Registers M.tm) :
    InitialFields M x w u ↔ u = encode M.tm (initList M.tm (verifierInput M (tape x w))) := by
  unfold InitialFields
  rw [readTape_iff]
  obtain ⟨l,s,R⟩ := u
  constructor
  · rintro ⟨rfl,rfl,hi,ho⟩
    have e : R = (encode M.tm (initList M.tm (verifierInput M (tape x w)))).stack := by
      funext k
      by_cases h : k=M.tm.k₀
      · subst k; simpa [encode,initList] using hi
      · simpa [encode,initList,h,stackCode] using ho k h
    rw [e]; rfl
  · intro eqn
    have el := congrArg Registers.label eqn
    have es := congrArg Registers.state eqn
    have eR := congrArg Registers.stack eqn
    refine ⟨el,es,?_,fun k h => ?_⟩
    · simpa [encode,initList] using congrFun eR M.tm.k₀
    · simpa [encode,initList,h,stackCode] using congrFun eR k

/-- Characterization of an accepting trace using the field readers directly
at its first row, so all references to the case-specific framed tape disappear. -/
theorem acceptingTrace_fields_iff (M : VerifierMachine) {r : ℕ} (x : ℕ) (w : Fin r → ℕ) (n B : ℕ) :
    AcceptingRegisterTrace M (tape x w) n B ↔
      Supported M.tm (verifierHalt M true).stk ∧ ∃ row : Fin (n+1) → Registers M.tm,
        InitialFields M x w (row 0) ∧ row (Fin.last n) = encode M.tm (verifierHalt M true) ∧
        IsTrace (regStep M.tm) row ∧ ∀ j k, ((row j).stack k).size ≤ B := by
  simp only [initialFields_iff,AcceptingRegisterTrace]

end
end DiophantineNP.Classes.Jones.Machine
