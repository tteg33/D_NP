import DiophantineNP.HABIndexMul
import DiophantineNP.HABSmallIndexMul

/-! Eliminate the arithmetic atoms from every fixed template, including under majority.
The finite source formula is independent of the universe size. -/
namespace DiophantineNP.HAB
open WidthFormula Counting FiniteArithmeticGap

/-- Natural multiplication of represented indices, in order, BIT and strict majority. -/
noncomputable def indexMultiplication : IndexMultiplication where
  formula := extendSmallMul (indexSmallMul 0 1 2)
  correct A e := extendSmallMul_correct _ A
    (indexSmallMul_sound 0 1 2 A)
    (fun env _ _ hy hB hfit he => indexSmallMul_complete 0 1 2 A env hy hB hfit he) e

/-- Compile any arithmetic template into the literal source vocabulary of HAB. -/
noncomputable def toSource {k : ℕ} (p : Template k) : Form k := source indexMultiplication p

theorem toSource_correct {k U : ℕ} (p : Template k) (A : Matrix U) (e : Fin k → Fin U) :
    (toSource p).Holds A e ↔ p.eval A e = true := source_correct indexMultiplication p A e

end DiophantineNP.HAB
