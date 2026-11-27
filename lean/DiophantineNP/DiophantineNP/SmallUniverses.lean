import DiophantineNP.SmallSumTemplate

/-! # Supplying the finitely many small universes of a product template

For a fixed size, the input consists of a finite truth table and the output
position. An explicit finite disjunction recognizes each accepting table using
just order, equality and the binary input relation. Thus one formula correct
from a fixed threshold gives a uniform formula correct at every size.
-/
namespace DiophantineNP.FiniteArithmeticGap
open Counting WidthFormula
noncomputable section

private def yesT : Template 1 := .atom (.eqv 0 0)
private def noT : Template 1 := .neg yesT
private def orL (l : List (Template 1)) := l.foldr Template.disj noT
private def andL (l : List (Template 1)) := l.foldr Template.conj yesT

private theorem orL_true {U} (l : List (Template 1)) (f : Fin U → Fin U → Bool) (env : Fin 1 → Fin U) :
    (orL l).eval f env = true ↔ ∃ a ∈ l, a.eval f env = true := by
  induction l with
  | nil => simp [orL,noT,yesT,Template.eval,Atom.eval]
  | cons a l ih =>
    change (Template.disj a (orL l)).eval f env = true ↔ _
    rw [Tdisj_true,ih]; simp only [List.mem_cons]; aesop

private theorem andL_true {U} (l : List (Template 1)) (f : Fin U → Fin U → Bool) (env : Fin 1 → Fin U) :
    (andL l).eval f env = true ↔ ∀ a ∈ l, a.eval f env = true := by
  induction l with
  | nil => simp [andL,yesT,Template.eval,Atom.eval]
  | cons a l ih =>
    change (Template.conj a (andL l)).eval f env = true ↔ _
    rw [Tconj_true,ih]; simp only [List.mem_cons]; aesop

private def anyT {α : Type} [Fintype α] (s : α → Template 1) := orL (Finset.univ.toList.map s)
private def allT {α : Type} [Fintype α] (s : α → Template 1) := andL (Finset.univ.toList.map s)

private theorem anyT_true {α : Type} [Fintype α] {U} (s : α → Template 1) (f : Fin U → Fin U → Bool) (env : Fin 1 → Fin U) :
    (anyT s).eval f env = true ↔ ∃ i, (s i).eval f env = true := by simp [anyT,orL_true]

private theorem allT_true {α : Type} [Fintype α] {U} (s : α → Template 1) (f : Fin U → Fin U → Bool) (env : Fin 1 → Fin U) :
    (allT s).eval f env = true ↔ ∀ i, (s i).eval f env = true := by simp [allT,andL_true]

private def cell (r c : ℕ) : Template 1 := .ex (.ex (.conj (fromFormula (isNat r 1))
    (.conj (fromFormula (isNat c 0)) (.entry 1 0))))

private theorem cell_eval {U : ℕ} (i j : Fin U) (f : Fin U → Fin U → Bool) (env : Fin 1 → Fin U) :
    (cell i j).eval f env = f i j := by
  apply Bool.eq_iff_iff.mpr
  simp only [cell,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,Tentry_eval]
  change (∃ r c : Fin U, r.val=i.val ∧ c.val=j.val ∧ f r c=true) ↔ _
  constructor
  · rintro ⟨r,c,hr,hc,h⟩; rwa [Fin.ext hr,Fin.ext hc] at h
  · exact fun h => ⟨i,j,rfl,rfl,h⟩

private def literal (b : Bool) (a : Template 1) : Template 1 := if b then a else .neg a

private theorem literal_true {U} (b : Bool) (a : Template 1) (f : Fin U → Fin U → Bool) (env : Fin 1 → Fin U) :
    (literal b a).eval f env = true ↔ a.eval f env = b := by cases b <;> simp [literal,Template.eval]

/-- At fixed `u`, any Boolean query of the full input table and output index
has a first-order template. Its size may depend arbitrarily on this fixed u. -/
def fixedTable (u : ℕ) (out : (Fin u → Fin u → Bool) → Fin u → Bool) : Template 1 :=
  anyT fun f : Fin u → Fin u → Bool => anyT fun j : Fin u =>
    if out f j then .conj (fromFormula (isNat j (0:Fin 1)))
      (allT fun p : Fin u × Fin u => literal (f p.1 p.2) (cell p.1 p.2)) else noT

theorem fixedTable_eval (u : ℕ) (out : (Fin u → Fin u → Bool) → Fin u → Bool)
    (f : Fin u → Fin u → Bool) (j : Fin u) : (fixedTable u out).eval f (fun _ => j) = out f j := by
  apply Bool.eq_iff_iff.mpr
  simp only [fixedTable,anyT_true]
  constructor
  · rintro ⟨g,k,h⟩
    cases eq : out g k with
    | false => simp [eq,noT,yesT,Template.eval,Atom.eval] at h
    | true =>
      simp only [eq,ite_true,Tconj_true,fromFormula_eval,isNat_spec,allT_true,literal_true,cell_eval] at h
      obtain ⟨hk,hf⟩ := h
      have hg : f=g := funext fun i => funext fun b => hf (i,b)
      exact hg ▸ Fin.ext hk ▸ eq
  · intro h
    exact ⟨f,j,by simp [h,Tconj_true,isNat_spec,allT_true,literal_true,cell_eval]⟩

private def extendRow {u : ℕ} (g : Fin u → Fin (2^u)) (i : ℕ) := if h : i<u then (g ⟨i,h⟩).val else 0

/-- A finite truth function for the low product digits, with the rows decoded
by comparing their finitely many input bits to each bounded unsigned word. -/
private def productTable (u : ℕ) (e : Fin u → Fin u → Bool) (j : Fin u) : Bool :=
  decide (∃ g : Fin u → Fin (2^u), (∀ i c, (g i).val.testBit c.val = e i c) ∧
    (productPrefix (extendRow g) u).testBit j.val = true)

private theorem productTable_eval (u : ℕ) (f : ℕ → ℕ) (h : ∀ i<u, f i<2^u) (j : Fin u) :
    productTable u (fun i c => (f i.val).testBit c.val) j = (productPrefix f u).testBit j.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [productTable,decide_eq_true_eq]
  let g (i : Fin u) : Fin (2^u) := ⟨f i.val,h _ i.isLt⟩
  have prod_eq {a : Fin u → Fin (2^u)} (e : ∀ i : Fin u, (a i).val=f i.val) :
      productPrefix (extendRow a) u = productPrefix f u := by
    unfold productPrefix
    congr 1
    apply List.map_congr_left
    intro t ht; have lt := List.mem_range.mp ht; simp [extendRow,lt,e]
  constructor
  · rintro ⟨a,hb,bit⟩
    rw [prod_eq] at bit
    · exact bit
    · intro i; apply Nat.eq_of_testBit_eq; intro c
      by_cases hc : c<u
      · exact hb i ⟨c,hc⟩
      · have hp : 2^u ≤ 2^c := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.testBit_lt_two_pow ((a i).isLt.trans_le hp),Nat.testBit_lt_two_pow ((h i i.isLt).trans_le hp)]
  · intro bit; exact ⟨g,fun _ _ => rfl,(prod_eq (a:=g) (fun _ => rfl)).symm ▸ bit⟩

def above (n : ℕ) : Template 1 := .ex (fromFormula (isNat n 0))

theorem above_eval {u} (n : ℕ) (e : Fin u → Fin u → Bool) (env : Fin 1 → Fin u) :
    (above n).eval e env = decide (n<u) := by
  apply Bool.eq_iff_iff.mpr
  simp only [above,Tex_true,fromFormula_eval,isNat_spec,Fin.cases_zero,decide_eq_true_eq]
  exact ⟨fun ⟨i,eq⟩ => eq ▸ i.isLt,fun h => ⟨⟨n,h⟩,rfl⟩⟩

def branch (p a b : Template 1) : Template 1 := .disj (.conj p a) (.conj (.neg p) b)
theorem branch_eval {u} (p a b : Template 1) (e : Fin u → Fin u → Bool) (env : Fin 1 → Fin u) :
    (branch p a b).eval e env = if p.eval e env then a.eval e env else b.eval e env := by
  cases h : p.eval e env <;> simp [branch,Template.eval,h]

def ProductCorrectFrom (N : ℕ) (a : Template 1) : Prop := ∀ {u : ℕ}, N ≤ u → ∀ (f : ℕ → ℕ),
  (∀ i<u, f i<2^u) → ∀ j : Fin u, a.eval (fun r c => (f r.val).testBit c.val) (fun _ => j) = (productPrefix f u).testBit j.val

/-- One fixed formula correct on all sufficiently large finite structures
extends to a formula satisfying `ProductTemplate` at every universe size. -/
def ProductTemplate.ofEventuallyCorrect (N : ℕ) (a : Template 1) (ha : ProductCorrectFrom N a) : ProductTemplate := by
  induction N generalizing a with
  | zero => exact ⟨a,fun f h j => ha (Nat.zero_le _) f h j⟩
  | succ n ih =>
    refine ih (branch (above n) a (fixedTable n (productTable n))) (fun {u} hu f h j => ?_)
    rw [branch_eval,above_eval]
    by_cases gt : n<u
    · simpa [gt] using ha gt f h j
    · have un : u=n := by omega
      subst u
      simp [fixedTable_eval,productTable_eval n f h]

end
end DiophantineNP.FiniteArithmeticGap
