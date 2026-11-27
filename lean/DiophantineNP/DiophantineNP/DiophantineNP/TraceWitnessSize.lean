import DiophantineNP.TableauConstraints

/-! # Bit budget of a packed affine tableau -/
namespace DiophantineNP.JMTableau.TraceTable
open BoundedRelation

private theorem mask_le' {a b : ℕ} (h : BitIncl a b) : a ≤ b := by
  rw [← (bitIncl_iff_and a b).mp h]
  exact Nat.and_le_right

/-- Every satisfying raw tableau already has short named auxiliaries. The
clock bounds the packed data and selector words, while the radix predecessor
needs at most the capacity bit length plus the fixed guard width. -/
theorem raw_fits (T : TraceTable) (h : ℕ) (z : Env T.Port) (u : Env T.Aux)
    (hz : Fits h z) (yes : T.Raw z u) : Fits (h+T.guard+1) u := by
  obtain ⟨hK,hQ,hH,_,_,_,reg,_,br⟩ := yes
  have hg : 1 ≤ T.guard := by unfold guard; omega
  have hpow : 2 ≤ 2^T.guard := (Nat.pow_le_pow_right (by decide : 0 < 2) hg)
  have hKp : 0 < z .capacity := by omega
  have hbig := Nat.mul_le_mul_right (z .capacity) hpow
  have hq : 0 < u .radixPred := by omega
  have hkq : u .capPred ≤ u .radixPred := by omega
  have hI : u .ones ≤ z .clock := by have := Nat.le_mul_of_pos_left (u .ones) hq; omega
  have hw (j) : u (.word j) ≤ z .clock := (mask_le' (reg j)).trans
    ((Nat.mul_le_mul_right (u .ones) hkq).trans (by omega))
  have hword {n : ℕ} (hn : n ≤ z .clock) : bits n ≤ h+T.guard+1 :=
    ((FourSquare.bits_mono hn).trans (hz .clock)).trans (by omega)
  intro a; cases a with
  | ones => exact hword hI
  | capPred => exact ((FourSquare.bits_mono (by omega : u .capPred ≤ z .capacity)).trans (hz .capacity)).trans (by omega)
  | radixPred =>
    have hb := hz .capacity
    have hu : z .capacity < 2^h := Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) hb)
    have hlt : u .radixPred ≤ 2^(h+T.guard) := by
      rw [Nat.add_comm,pow_add]
      exact (show u .radixPred ≤ 2^T.guard * z .capacity by omega).trans (Nat.mul_le_mul_left _ hu.le)
    simpa [bits] using FourSquare.bits_mono hlt
  | flag i => exact hword ((mask_le' (br i).2.1).trans hI)
  | inactive i => have := (br i).1; exact hword (by omega)
  | word j => exact hword (hw j)
  | extracted i e j => exact hword ((mask_le' (((br i).2.2 e).2 j).1).trans (hw j))

end DiophantineNP.JMTableau.TraceTable
