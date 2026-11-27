import DiophantineNP.TraceBounds

/-! # Decoding a packed register trace from its polynomial constraints -/
namespace DiophantineNP.JMTableau.TraceTable
open BoundedRelation

/-- Even an unbounded raw assignment decodes to a genuine trace; the masks
force all data registers and enough guard bits in every individual lane. -/
theorem raw_sound (T : TraceTable) (z : Env T.Port) (u : Env T.Aux) (yes : T.Raw z u) : T.Accepts z := by
  obtain ⟨hK,hQ,hH,mK,mH,sum,reg,ends,br⟩ := yes
  obtain ⟨v,hv⟩ := (power_two_iff_mask (x:=z .capacity) (by omega)).mpr (by
    have : 2*z .capacity-1 = 2*u .capPred+1 := by omega
    rwa [this])
  let w := T.guard+v
  let q := 2^w
  have wpos : 0<w := by have := guard_pos T; dsimp [w]; omega
  have Kq : 2^v ≤ q := Nat.pow_le_pow_right (by decide) (by dsimp [w]; omega)
  have Qq : 2^T.guard*z .capacity=q := by rw [hv,← pow_add]
  have kp : u .capPred=2^v-1 := by omega
  have qp : u .radixPred=q-1 := by omega
  have hClock : (q-1)*u .ones+1=z .clock := by rw [← qp]; exact hH.symm
  obtain ⟨n,hn⟩ := (clock_iff (I:=u .ones) wpos).mp (by
    change BitIncl ((q-1)*u .ones+1) (2*((q-1)*u .ones+1)-1)
    rw [hClock,show 2*z .clock-1=2*(u .radixPred*u .ones)+1 by omega]
    exact mH)
  let I := pack q (fun _ : Fin n => 1)
  have Hn : z .clock = q^n := hClock.symm.trans (hn ▸ geom q n (Nat.two_pow_pos w))
  have decode (j : Fin T.m) : ∃ a : Fin n → ℕ, u (.word j)=pack q a ∧ ∀ t, a t < 2^v := by
    apply (register_mask_iff (w:=w) (v:=v) (n:=n) (by dsimp [w]; omega)).mp
    simpa only [kp,hn] using reg j
  choose r wr hr using decode
  change u .ones=I at hn
  have b : branchChecks T.P q I (fun j => pack q (r j)) := by
    refine ⟨fun i => u (.flag i),fun i => by simpa only [← hn] using (br i).2.1,by simpa only [← hn] using sum,?_⟩
    intro i p hp
    obtain ⟨e,rfl⟩ := List.mem_iff_get.mp hp
    obtain ⟨eq,sub⟩ := (br i).2.2 e
    refine ⟨fun j => u (.extracted i e j),fun j => ?_,eq⟩
    have off : u (.inactive i) = I-u (.flag i) := by
      have h : u (.flag i)+u (.inactive i)=u .ones := (br i).1
      rw [← hn,← h,Nat.add_sub_cancel_left]
    simpa only [selected,← wr,← qp,← off] using sub j
  refine ⟨n,v,hv,Hn.trans (pow_mul 2 w n).symm,fun j => ⟨(ends j).1.trans_eq hv,(ends j).2.1.trans_eq hv⟩,
    r,hr,(frame_iff T r hr).mp b,fun j => ?_⟩
  apply (shiftTrace_iff (r (T.old j)) (r (T.new j)) _ _ (fun t => (hr _ t).trans_le Kq) (fun t => (hr _ t).trans_le Kq)
    (((ends j).1.trans_eq hv).trans_le Kq) (((ends j).2.1.trans_eq hv).trans_le Kq)).mp
  change pack q _+((q-1)*I+1)*_ = q*pack q _+_
  rw [show (q-1)*I+1=z .clock from by rw [← hn]; exact hClock,← wr,← wr,← Qq]
  exact (ends j).2.2

end DiophantineNP.JMTableau.TraceTable
