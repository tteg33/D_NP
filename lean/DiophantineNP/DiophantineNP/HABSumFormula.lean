import DiophantineNP.HABCounting
import DiophantineNP.HABBlockCells
import DiophantineNP.HABSumBlocks

/-! # A fixed formula for a weighted block of an iterated sum

The first unary count reads a bit of a column population. The second unary
count counts the coded triples in one output block. Both formulas are fixed
before the table or universe is supplied, including for a population equal
to the size of the universe. -/
namespace DiophantineNP.HABSumFormula
open Counting WidthFormula Finset ShortResidue HABCounting HABSumBlocks
open scoped Classical

private noncomputable def columnBit : Predicate :=
  countBitP 15 7 (Predicate.entry 15 10)

private theorem columnBit_spec (f : ℕ → ℕ) (U : ℕ) (d : ℕ → ℕ) :
    columnBit.holds U (fun r c => (f r).testBit c) d ↔
      (column f U (d 10)).testBit (d 7) = true := by
  simp only [columnBit,countBitP,cardP,column,Predicate.entry]
  simp [Function.update]

/-- The five inputs, in order, are the starting column, block width, diagonal
length, radix and proposed population of the coded contribution cells. -/
noncomputable def blockAt : Predicate :=
  countEqP 5 4 (cell columnBit)

theorem blockAt_iff (f : ℕ→ℕ) (U : ℕ) (e : ℕ→ℕ) (hk : e 1<U) (hL : e 2<U)
    (hB : e 3<U) (hbase : e 3=2^(e 1)) (hcap : e 1*e 2*e 3≤U) :
    blockAt.holds U (fun r c => (f r).testBit c) e ↔
      e 4 = block (column f U) U (e 2) (e 1) (e 0) := by
  let table := fun (r c : ℕ) => (f r).testBit c
  have same : (range U).filter (fun z => (cell columnBit).holds U table (Function.update e 5 z)) =
      (range U).filter (good (column f U) U (e 0) (e 1) (e 2) (e 3)) := by
    apply filter_congr
    intro z hz
    have he := cell_spec columnBit (column f U) U table (Function.update e 5 z)
      (columnBit_spec f U) hk hL hB hbase (by simpa using mem_range.mp hz)
    exact he
  change (e 4 = _) ↔ _
  rw [cardP,same,card_good _ _ _ _ _ _ hbase hcap]
  rfl

private def inputNames {a : ℕ} (start k L B count : Fin a) (i : ℕ) : Fin a :=
  if i=0 then start else if i=1 then k else if i=2 then L else if i=3 then B else count

noncomputable def blockAtFormula {a : ℕ} (start k L B count : Fin a) : Template a :=
  blockAt.syntaxF (inputNames start k L B count)

theorem blockAtFormula_spec {a U : ℕ} (start k L B count : Fin a) (f : ℕ→ℕ)
    (env : Fin a → Fin U) (hbase : (env B).val=2^(env k).val)
    (hcap : (env k).val*(env L).val*(env B).val ≤ U) :
    (blockAtFormula start k L B count).eval (fun r c => (f r.val).testBit c.val) env = true ↔
      (env count).val = block (column f U) U (env L).val (env k).val (env start).val := by
  let names := inputNames start k L B count
  let e : ℕ→ℕ := fun i => (env (names i)).val
  rw [blockAtFormula,Predicate.valid _ _ (fun r c => (f r).testBit c)]
  exact blockAt_iff f U e (env k).isLt (env L).isLt (env B).isLt hbase hcap

end DiophantineNP.HABSumFormula
