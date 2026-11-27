import DiophantineNP.ConcreteGrid
import DiophantineNP.BinaryKernel
import DiophantineNP.PackingBridge

/-! # The weighted sum over the four concrete root grids -/
namespace DiophantineNP.FourGrid
open ConcreteGrid Counting Finset
open scoped BigOperators
noncomputable section

abbrev Point (U : ℕ) := LabelGrid U (Invalid U) (Outside U)
abbrev Selected (U : ℕ) := (Fin U × Bool) ⊕ Invalid U

def stride (U : ℕ) := 4*(2*radius U+2)^30
private def quarter (U : ℕ) : ℤ := (2*(radius U:ℤ)+2)^30
private def sign (s : Bool) : ℤ := if s then -1 else 1
private instance (U : ℕ) : NeZero (size U) := ⟨by unfold size Grid.period; positivity⟩
private instance (U : ℕ) : NeZero (J U) := ⟨by unfold J; omega⟩

def rootCode {U : ℕ} (z : Point U) : ZMod (size U) := (roots U z).val

def carrier {U : ℕ} (w v : Point U) : ℂ := ∑ b : ZMod (J U),
  (ZMod.stdAddChar (rootCode v))^stride U * (2*((ZMod.stdAddChar (rootCode w))^stride U)⁻¹)^b.val

def marked {U : ℕ} (i : Fin (J U)) (s : Bool) : Point U := .inl ((selectedEquiv U).symm (i,s))

private theorem code_marked {U : ℕ} (i : Fin (J U)) (s : Bool) :
    rootCode (marked i s) = ((sign s*((J U:ℤ)*quarter U+centered i):ℤ):ZMod (size U)) := by
  have hQ : Q U = (J U:ℤ)*quarter U := by unfold J Q quarter; push_cast; rfl
  rw [rootCode, marked, roots_selected, Equiv.apply_symm_apply, ← Int.cast_natCast, arc_val, atArc]
  cases s
  · simp [sign, hQ]
  · simp only [↓reduceIte, sign, neg_one_mul]
    rw [fourQ U, hQ]
    simp

private def phase {U : ℕ} (a t : ℤ) (s : Bool) : ℂ := ∑ b : ZMod (J U),
  (2:ℂ)^b.val*ZMod.stdAddChar (if s then -((t-b.val*a : ℤ):ZMod (J U)) else ((t-b.val*a:ℤ):ZMod (J U)))

private theorem carrier_selected {U : ℕ} (k t : Fin (J U)) (s : Bool) :
    carrier (marked k s) (marked t s) = phase (U:=U) (centered k) (centered t) s := by
  have hm : size U = J U * stride U := by unfold J size Grid.period stride; ring
  unfold carrier phase
  apply sum_congr rfl
  intro b _
  rw [code_marked, code_marked, BinaryKernel.carrier_term hm]
  cases s <;> simp [sign]

def residues (n : ℕ) [NeZero n] : Fin n ≃ ZMod n where
  toFun i := (i.val:ZMod n)
  invFun b := ⟨b.val,b.val_lt⟩
  left_inv i := Fin.ext (ZMod.val_natCast_of_lt i.isLt)
  right_inv b := ZMod.natCast_zmod_val b

theorem carrier_bound {U : ℕ} (w v : Point U) : ‖carrier w v‖ ≤ (2:ℝ)^(J U) := by
  unfold carrier
  calc
    _ ≤ ∑ b : ZMod (J U), (2:ℝ)^b.val := by
      apply norm_sum_le_of_le
      intro b _
      simp [norm_pow,AddChar.norm_apply,norm_inv]
    _ = ∑ i : Fin (J U), (2:ℝ)^i.val := by
      rw [← (residues (J U)).sum_comp (fun b => (2:ℝ)^b.val)]
      apply sum_congr rfl
      intro i _
      simp [residues, ZMod.val_natCast_of_lt i.isLt]
    _ ≤ _ := by
      rw [Fin.sum_univ_eq_sum_range]
      have h (n : ℕ) : (∑ i ∈ range n, (2:ℝ)^i)+1=2^n := by
        induction n with
        | zero => simp
        | succ n ih => rw [sum_range_succ, pow_succ]; linarith
      linarith [h (J U)]

private def freq {U : ℕ} : Fin (J U) ≃ ZMod (J U) :=
  (residues (J U)).trans (Equiv.subRight (radius U:ZMod (J U)))

private theorem centered_freq {U : ℕ} (k : Fin (J U)) :
    BinaryKernel.centered (B:=radius U) (freq k) = centered k := by
  simp [BinaryKernel.centered, freq, residues, centered, ZMod.val_natCast_of_lt k.isLt]

private theorem sum_centered {U : ℕ} (f : ℤ → ℂ) :
    (∑ i : Fin (J U), f (centered i)) = ∑ j ∈ Icc (-(radius U:ℤ)) (radius U:ℤ), f j := by
  apply sum_bij (fun i _ => centered i)
  · intro i _; exact mem_Icc.mpr (abs_le.mp (c_bound i))
  · intro i _ i' _ e; apply Fin.ext; unfold centered at e; omega
  · intro j hj
    have h := mem_Icc.mp hj
    let i : Fin (J U) := ⟨(j+radius U).toNat, by unfold J; omega⟩
    exact ⟨i, mem_univ _, by unfold centered i; dsimp; omega⟩
  · intros; rfl

private theorem sum_selected {U : ℕ} (f : Point U → ℂ) (hoff : ∀ o, f (.inr o) = 0) :
    ∑ z, f z = ∑ k : Fin (J U), ∑ s : Bool, f (marked k s) := by
  rw [Fintype.sum_sum_type, (sum_eq_zero (fun i _ => hoff i)), add_zero]
  rw [← Fintype.sum_prod_type (fun p : Fin (J U) × Bool => f (marked p.1 p.2))]
  exact ((selectedEquiv U).symm.sum_comp (fun a => f (.inl a))).symm

/-- The exact selector vanishes whenever a coordinate misses its window, or
when the output position is outside the native universe. -/
def ideal {U : ℕ} (truth : Fin U → Bool) : Point U → Point U → Point U → Point U → Bool
  | .inl (.inl (i,_)), .inl w, .inl u, .inl v => truth i &&
      decide ((selectedEquiv U w).2=(selectedEquiv U v).2) &&
      decide ((i.val:ℤ)*centered (selectedEquiv U w).1=(J U:ℤ)*centered (selectedEquiv U u).1+centered (selectedEquiv U v).1)
  | _, _, _, _ => false

private def term {U : ℕ} (truth : Fin U → Bool) (z w u v : Point U) : ℂ :=
  if ideal truth z w u v then carrier w v else 0

private theorem last_sum {U : ℕ} (truth : Fin U → Bool) (i : Fin U) (hi : truth i = true)
    (b s d : Bool) (k q : Fin (J U)) :
    (∑ v, term truth (.inl (.inl (i,b))) (marked k s) (marked q d) v) =
    ∑ t : Fin (J U), if (i.val:ℤ)*centered k=(J U:ℤ)*centered q+centered t then
      phase (U:=U) (centered k) (centered t) s else 0 := by
  rw [sum_selected _ (by intro o; rfl)]
  apply sum_congr rfl
  intro t _
  rw [Fintype.sum_bool]
  rw [← carrier_selected]
  cases s <;> simp [term, ideal, marked, hi]

private theorem middle_sum {U : ℕ} (truth : Fin U → Bool) (i : Fin U) (hi : truth i = true)
    (b s : Bool) (k : Fin (J U)) :
    (∑ u, ∑ v, term truth (.inl (.inl (i,b))) (marked k s) u v) =
    2*BinaryKernel.arcTerm (B:=radius U) (i.val:ZMod (J U)) (freq k) s := by
  have hij : i.val < J U := by have := i.isLt; unfold J radius; omega
  rw [sum_selected _ (by intro o; apply sum_eq_zero; intro v _; rfl)]
  simp_rw [last_sum truth i hi b s]
  simp only [Fintype.sum_bool, ← two_mul, ← mul_sum]
  congr 1
  let f (q t : ℤ) : ℂ := if (i.val:ℤ)*centered k = (J U:ℤ)*q+t then phase (U:=U) (centered k) t s else 0
  change (∑ q : Fin (J U), ∑ t : Fin (J U), f (centered q) (centered t)) = _
  simp_rw [fun q : Fin (J U) => sum_centered (U:=U) (f (centered q))]
  rw [sum_centered (U:=U) (fun q => ∑ t ∈ Icc (-(radius U:ℤ)) (radius U:ℤ), f q t)]
  unfold BinaryKernel.arcTerm
  rw [centered_freq, ZMod.val_natCast_of_lt hij]
  rfl

private theorem fixed_sum {U : ℕ} (truth : Fin U → Bool) (i : Fin U) (b : Bool) :
    (∑ w, ∑ u, ∑ v, term truth (.inl (.inl (i,b))) w u v) =
    if truth i then 4*(J U:ℂ)*(2:ℂ)^i.val else 0 := by
  cases hi : truth i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply sum_eq_zero; intro w _
    apply sum_eq_zero; intro u _
    apply sum_eq_zero; intro v _
    cases w <;> cases u <;> cases v <;> simp [term,ideal,hi]
  | true =>
    simp only [↓reduceIte]
    rw [sum_selected _ (by intro o; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _; rfl)]
    simp_rw [middle_sum truth i hi b]
    rw [sum_comm]
    have hij : i.val < J U := by have := i.isLt; unfold J radius; omega
    have hv : (i.val:ZMod (J U)).val = i.val := ZMod.val_natCast_of_lt hij
    have hB : (i.val:ZMod (J U)).val ≤ radius U := by rw [hv]; have := i.isLt; unfold radius; omega
    have hsum (s : Bool) : (∑ x : Fin (J U), 2*BinaryKernel.arcTerm (B:=radius U) (i.val:ZMod (J U)) (freq x) s) =
        2*((J U:ℂ)*(2:ℂ)^i.val) := by
      rw [← mul_sum, (freq (U:=U)).sum_comp (fun k => BinaryKernel.arcTerm (B:=radius U) (i.val:ZMod (J U)) k s)]
      congr 1
      exact (BinaryKernel.sum_arcTerm (B:=radius U) (i.val:ZMod (J U)) hB s).trans (by rw [hv]; rfl)
    simp_rw [hsum]
    simp only [Fintype.sum_bool]
    ring

private theorem native_word {U k : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) :
    (∑ i : Fin U, if φ.eval (Fin.cases i t) then (2:ℂ)^i.val else 0) = (Packing.packed φ t:ℂ) := by
  let bits (j : ℕ) := if h : j < U then φ.eval (Fin.cases ⟨j,h⟩ t) else false
  have hw (n : ℕ) : (Readout.word bits n:ℂ) = ∑ j ∈ range n, if bits j then (2:ℂ)^j else 0 := by
    induction n with
    | zero => simp [Readout.word,Readout.prefixSum]
    | succ n ih =>
      change ((Readout.word bits n + (bits n).toNat * 2^n:ℕ):ℂ)=_
      rw [sum_range_succ,Nat.cast_add,ih]
      cases h : bits n <;> simp
  change _ = (Readout.word bits U:ℂ)
  rw [hw, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  simp [bits,i.isLt]

/-- Every valid output position contributes eight copies of the signed
frequency sum. The resulting integer is the manuscript's little-endian word. -/
theorem ideal_sum {U k : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) :
    (∑ z, ∑ w, ∑ u, ∑ v, if ideal (fun i => φ.eval (Fin.cases i t)) z w u v then carrier w v else 0) =
    (8*(J U:ℂ))*(Packing.packed φ t:ℂ) := by
  let truth (i : Fin U) := φ.eval (Fin.cases i t)
  change ∑ z, ∑ w, ∑ u, ∑ v, term truth z w u v = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have ho (o : Outside U) (w u v : Point U) : term truth (.inr o) w u v=0 := rfl
  have hi (o : Invalid U) (w u v : Point U) : term truth (.inl (.inr o)) w u v=0 := rfl
  simp only [ho,hi,sum_const_zero,add_zero]
  rw [Fintype.sum_prod_type]
  simp_rw [fixed_sum]
  rw [← native_word, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  change _ = 8*(J U:ℂ)*(if truth i then (2:ℂ)^i.val else 0)
  cases h : truth i <;> simp
  ring

end
end DiophantineNP.FourGrid
