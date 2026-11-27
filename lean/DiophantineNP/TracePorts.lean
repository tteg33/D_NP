import DiophantineNP.TraceTable
import Mathlib.Tactic.DeriveFintype

/-! # External registers of a packed-tableau checker -/
namespace DiophantineNP.JMTableau.TraceTable

inductive Port (T : TraceTable) where
  | first (i : Fin T.k)
  | last (i : Fin T.k)
  | capacity
  | clock
  deriving Fintype, DecidableEq

def Affine.weight {m : ℕ} (p : JMTableau.Affine m) := p.offset + ∑ i, p.coeff i

def guard (T : TraceTable) := 1 + T.b + ∑ i, ((T.P i).map fun e => Affine.weight e.1 + Affine.weight e.2).sum

/-- The capacity and clock ports expose the number of bits consumed by packed
words. The register endpoints are included for time zero as well. -/
def Accepts (T : TraceTable) (z : T.Port → ℕ) :=
  ∃ n v, z .capacity = 2^v ∧ z .clock = 2^((T.guard+v)*n) ∧
    (∀ j, z (.first j)<2^v ∧ z (.last j)<2^v) ∧ T.Run n v (fun j => z (.first j)) (fun j => z (.last j))

end DiophantineNP.JMTableau.TraceTable
