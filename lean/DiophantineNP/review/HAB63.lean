import DiophantineNP.HABCorollary63
import Lean.Util.CollectAxioms

/-! # Hesse–Allender–Barrington, Corollary 6.3

For every width `U ≥ 2`, the input consists of `U` natural numbers with at most
`U` bits each. Column zero holds the least significant bit. The product bit is
addressed by the pair `(hi, lo)` in base `U`. The quotient uses rows zero and
one. The two formulas below are chosen once for all widths and inputs.
-/

namespace Review.HAB63

open DiophantineNP

def input {U : ℕ} (rows : Fin U → ℕ) : HAB.Matrix U :=
  fun r c => (rows r).testBit c.val

theorem division_and_iterated_product :
    ∃ (division : HAB.Form 1) (product : HAB.Form 2),
      ∀ (U : ℕ) (hU : 2 ≤ U) (rows : Fin U → ℕ), (∀ r, rows r < 2 ^ U) →
        (∀ j : Fin U,
          division.Holds (input rows) (fun _ => j) ↔
            (rows ⟨0, by omega⟩ / rows ⟨1, by omega⟩).testBit j.val = true) ∧
        (∀ hi lo : Fin U,
          product.Holds (input rows) (Fin.cases hi (fun _ => lo)) ↔
            (∏ r, rows r).testBit (hi.val * U + lo.val) = true) := by
  obtain ⟨⟨division, hdiv⟩, ⟨product, hmul⟩⟩ := HAB.corollary63
  refine ⟨division, product, ?_⟩
  intro U hU rows bounded
  have decode (r : Fin U) : HAB.rowWord (input rows r) = rows r :=
    HAB.rowWord_natural (bounded r)
  constructor
  · intro j
    simpa only [decode] using hdiv hU (input rows) j
  · intro hi lo
    simpa only [decode, WidthFormula.pairEnv] using hmul hU (input rows) hi lo

open Lean Elab Command in
run_cmd do
  let axioms ← collectAxioms ``division_and_iterated_product
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "Unexpected axiom in Corollary 6.3: {axioms}"
  logInfo m!"Corollary 6.3 uses {axioms}."

end Review.HAB63
