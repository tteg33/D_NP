import DiophantineNP.PackedTrace
import DiophantineNP.TraceHonest
import DiophantineNP.TraceWitnessSize

/-! # A uniform bounded Diophantine verifier for fixed affine trace tables -/
namespace DiophantineNP.JMTableau.TraceTable
open BoundedRelation

/-- A single polynomial, chosen before the input size, checks every trace of
this table. Soundness allows arbitrary raw words and auxiliary roots. The
honest witness budget is polynomial in the bit lengths of the two endpoint
vectors, the lane capacity and the clock word. -/
theorem run_short (T : TraceTable) (native : NativeVerifier) : Short T.Accepts := by
  apply Short.exists_of (fun x => T.Raw (x ∘ Sum.inl) (x ∘ Sum.inr)) (T.raw_short native)
    (Polynomial.X+Polynomial.C T.guard+1)
  · intro z u yes
    exact T.raw_sound z u yes
  · intro h z hz yes
    obtain ⟨u,hu⟩ := T.raw_complete z yes
    exact ⟨u,by simpa using T.raw_fits h z u hz hu,hu⟩

end DiophantineNP.JMTableau.TraceTable
