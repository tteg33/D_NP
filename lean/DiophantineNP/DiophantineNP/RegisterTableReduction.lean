import DiophantineNP.RegisterNativeTrace
import DiophantineNP.RegisterFieldGraph
import DiophantineNP.RegisterFieldBudget

/-! # Compiling the actual NP verifier via its checker tables -/
namespace DiophantineNP.Classes.Jones.Machine
open BoundedRelation JMTableau

/-- The fixed table checker alone serves input framing and the actual native
machine. The binary-length graph enforces the original certificate cutoff. -/
theorem np_subset_d_of_table_compiler (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (tables : ∀ T : TraceTable, Short T.Accepts) : NP ⊆ D :=
  np_subset_d_of_short_tables (by intro σ x r w q; exact certCut_short hc hq x w q)
    (by intro M σ x r w s; exact initialStack_short_of_table M (tables (fieldTable M)) x w s) tables

end DiophantineNP.Classes.Jones.Machine
