import DiophantineNP.FormulaBackend

/-! # The concrete cyclic characters used by the Laurent expressions -/
namespace DiophantineNP.FormulaLaurent
open Counting ConcreteGrid LaurentBounds
open scoped BigOperators
noncomputable section

instance sizeNeZero (U : ℕ) : NeZero (size U) := ⟨(period U).property.ne'⟩

def rootIndex {U : ℕ} (p : Point U) : ZMod (size U) := (roots U p).val

def rootEquiv (U : ℕ) : Point U ≃ ZMod (size U) :=
  (roots U).trans (ZMod.finEquiv (size U)).toEquiv

private theorem val_finEquiv {n : ℕ} [NeZero n] (a : Fin n) :
    (ZMod.finEquiv n a).val = a.val := by
  cases n with
  | zero => exact Fin.elim0 a
  | succ _ => rfl

theorem rootEquiv_apply {U : ℕ} (p : Point U) : rootEquiv U p = rootIndex p := by
  change ZMod.finEquiv (size U) (roots U p) = ((roots U p).val : ZMod (size U))
  rw [← val_finEquiv (roots U p), ZMod.natCast_zmod_val]

def gridChar {U d : ℕ} (z : Fin d → Point U) : Character d ℂ where
  toFun v := Additive.ofMul (ZMod.stdAddChar (∑ j, (v j : ZMod (size U))*rootIndex (z j)))
  map_zero' := by
    apply Additive.toMul.injective
    simp
  map_add' v w := by
    apply Additive.toMul.injective
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul]

theorem gridChar_apply {U d : ℕ} (z : Fin d → Point U) (v : Fin d → ℤ) :
    (gridChar z v).toMul = ZMod.stdAddChar (∑ j, (v j : ZMod (size U))*rootIndex (z j)) := rfl

theorem gridChar_single {U d : ℕ} (z : Fin d → Point U) (j : Fin d) (s : ℤ) :
    (gridChar z (Pi.single j s)).toMul =
    ZMod.stdAddChar ((s*(roots U (z j)).val:ℤ) : ZMod (size U)) := by
  rw [gridChar_apply]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp [rootIndex]
  · intro i _ h
    simp [Pi.single_eq_of_ne h]
  · simp

end
end DiophantineNP.FormulaLaurent
