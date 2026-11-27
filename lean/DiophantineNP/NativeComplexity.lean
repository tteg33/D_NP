import DiophantineNP.NativeBitLength
import DiophantineNP.RegisterTableReduction

/-! # The NP-to-D transfer from a native bitwise-inclusion verifier -/
namespace DiophantineNP.Classes
open Jones.Machine BoundedRelation

/-- The only premise of this machine-model transfer is global soundness and
short completeness for native bitwise inclusion. The proof checks encoded
inputs and accepting computations, including the original certificate budget. -/
theorem np_subset_d_of_native (native : NativeVerifier) : NP ⊆ D :=
  np_subset_d_of_short_tables
    (by intro σ x r w q; exact certCut_short_of_length (Short.nativeLength native) x w q)
    (by intro M σ x r w s; exact initialStack_short_of_table M ((fieldTable M).run_short native) x w s)
    (fun T => T.run_short native)

end DiophantineNP.Classes
