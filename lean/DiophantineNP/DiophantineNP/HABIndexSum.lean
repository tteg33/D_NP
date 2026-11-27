import DiophantineNP.HABCRTDot

/-! Exact sums of parameterized rows when the resulting natural number is an index. -/
namespace DiophantineNP.HABIndexSum
open Counting WidthFormula FiniteArithmeticGap HAB Finset

private def same {k : ℕ} (a b : Template k) : Template k :=
  .disj (.conj a b) (.conj (.neg a) (.neg b))

private theorem same_spec {k U : ℕ} (a b : Template k) (A : Matrix U) (e : Fin k→Fin U) :
    (same a b).eval A e=true ↔ a.eval A e=b.eval A e := by
  cases ha : a.eval A e <;> cases hb : b.eval A e <;> simp [same,Template.eval,ha,hb]

/-- Compare each bit of the proposed index with the independent iterated sum. -/
noncomputable def formula {n : ℕ} (z : Fin n) (cells : Template (n+2)) : Template n :=
  .neg (.ex (.neg (same (.bit z.succ 0) (HABCRTDot.sumRows cells))))

theorem formula_correct {n U : ℕ} (z : Fin n) (cells : Template (n+2)) (A : Matrix U)
    (e : Fin n→Fin U) (f : ℕ→ℕ) (h : ∀ r c : Fin U,
      cells.eval A (extend c r e)=(f r.val).testBit c.val) (fits : ∑ i ∈ range U,f i < U) :
    (formula z cells).eval A e=true ↔ (e z).val=∑ i ∈ range U,f i := by
  simp only [formula,Template.eval.eq_4,Bool.not_eq_true',←Bool.not_eq_true,Tex_true,same_spec,not_exists,
    not_not,HABCRTDot.sumRows_correct cells A e f h]
  change (∀ j : Fin U,(e z).val.testBit j.val=(∑ i ∈ range U,f i).testBit j.val) ↔ _
  constructor
  · intro bits
    have tab := congrArg HAB.rowWord (funext bits)
    rw [rowWord_natural ((e z).isLt.trans Nat.lt_two_pow_self),
        rowWord_natural (fits.trans Nat.lt_two_pow_self)] at tab
    exact tab
  · intro h _; rw [h]

/-- Sum from a graph supplying one represented nonnegative value per row. -/
noncomputable def fromGraph {n : ℕ} (z : Fin n) (graph : Template (n+2)) : Template n :=
  formula z (HABCRTDot.graphBits graph)

theorem fromGraph_correct {n U : ℕ} (z : Fin n) (g : Template (n+2)) (A : Matrix U)
    (e : Fin n→Fin U) (f : ℕ→ℕ) (h : ∀ r b : Fin U,
      g.eval A (extend b r e)=true ↔ b.val=f r.val) (fits : ∑ i ∈ range U,f i < U) :
    (fromGraph z g).eval A e=true ↔ (e z).val=∑ i ∈ range U,f i := by
  apply formula_correct _ _ _ _ f _ fits
  intro r c
  have hr : f r.val < U := (Finset.single_le_sum (f:=f) (fun _ _ => Nat.zero_le _)
    (mem_range.mpr r.isLt)).trans_lt fits
  exact HABCRTDot.graphBits_correct g A e r c hr (h r)

end DiophantineNP.HABIndexSum
