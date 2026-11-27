import DiophantineNP.TraceBounds

/-! # Honest assignments for the packed verifier tableau -/
namespace DiophantineNP.JMTableau.TraceTable
open BoundedRelation

/-- Pack an actual bounded trace into one witness for each of the fixed
polynomial and mask constraints, including empty traces. -/
theorem raw_complete (T : TraceTable) (z : Env T.Port) (yes : T.Accepts z) :
    ∃ u : Env T.Aux, T.Raw z u := by
  classical
  obtain ⟨n,v,hK,hH,hEnds,r,hr,rows,link⟩ := yes
  let w := T.guard+v
  let q := 2^w
  let K := 2^v
  let I := pack q (fun _ : Fin n => 1)
  let R (j : Fin T.m) := pack q (r j)
  have kpos : 0<K := Nat.two_pow_pos _
  have qpos : 0<q := Nat.two_pow_pos _
  have hw : v ≤ w := by dsimp [w]; omega
  have Kq : K ≤ q := Nat.pow_le_pow_right (by decide) hw
  have eqQ : 2^T.guard*z .capacity = q := by rw [hK, ← pow_add]
  have eqH : z .clock = (q-1)*I+1 := hH.trans ((pow_mul 2 w n).trans (geom q n qpos).symm)
  have c := (frame_iff T r hr).mpr rows
  obtain ⟨L,hm,hs,hA⟩ := c
  have ext (i : Fin T.b) (e : Fin (T.P i).length) := hA i _ (List.get_mem (T.P i) e)
  choose A hsel heq using ext
  let u : Env T.Aux := fun j => match j with
    | .ones => I
    | .capPred => K-1
    | .radixPred => q-1
    | .flag i => L i
    | .inactive i => I-L i
    | .word j => R j
    | .extracted i e j => A i e j
  refine ⟨u,?_,?_,eqH,?_,?_,hs,?_,?_,?_⟩
  · exact hK.trans (Nat.sub_add_cancel kpos).symm
  · exact eqQ.trans (Nat.sub_add_cancel qpos).symm
  · change BitIncl (z .capacity) (2*(K-1)+1)
    rw [show 2*(K-1)+1=2*z .capacity-1 by change z .capacity=K at hK; omega]
    exact (power_two_iff_mask (hK ▸ kpos)).mp ⟨v,hK⟩
  · change BitIncl (z .clock) (2*((q-1)*I)+1)
    rw [show 2*((q-1)*I)+1=2*z .clock-1 by omega]
    exact (power_two_iff_mask (by omega)).mp ⟨_,hH⟩
  · intro j
    exact (register_mask_iff (n:=n) (v:=v) (w:=w) hw).mpr ⟨r j,rfl,hr j⟩
  · intro j
    obtain ⟨hf,hl⟩ := hEnds j
    refine ⟨hf.trans_eq hK.symm,hl.trans_eq hK.symm,?_⟩
    have shift := (shiftTrace_iff (r (T.old j)) (r (T.new j)) _ _ (fun t => (hr _ t).trans_le Kq)
      (fun t => (hr _ t).trans_le Kq) (hf.trans_le Kq) (hl.trans_le Kq)).mpr (link j)
    change R _+z .clock*z (.last j) = (2^T.guard*z .capacity)*R _+z (.first j)
    rw [eqH,eqQ]; exact shift
  · intro i
    have flag_le : L i ≤ I := incl_le (hm i)
    refine ⟨Nat.add_sub_of_le flag_le,hm i,fun e => ⟨heq i e,hsel i e⟩⟩

end DiophantineNP.JMTableau.TraceTable
