import DiophantineNP.TableauConstraints

/-! # Checking fixed affine transition tables by one polynomial -/
namespace DiophantineNP.JMTableau.TraceTable
open BoundedRelation

theorem geom (q n : ℕ) (hq : 0 < q) :
    (q-1)*pack q (fun _ : Fin n => 1)+1=q^n := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack,pow_succ,← ih]
    have hh : q-1+1=q := Nat.sub_add_cancel hq
    rw [Nat.mul_add,Nat.mul_one,show (q-1)*(q*pack q (fun _ : Fin n => 1)) =
      (q-1)*pack q (fun _ : Fin n => 1)*q by ring]
    rw [Nat.add_assoc, hh]; ring

theorem incl_le {a b : ℕ} (h : BitIncl a b) : a ≤ b := by
  rw [← (bitIncl_iff_and a b).mp h]; exact Nat.and_le_right

theorem guard_pos (T : TraceTable) : 0<T.guard := by unfold guard; omega

theorem frame_iff {n v : ℕ} (T : TraceTable) (r : Fin T.m → Fin n → ℕ) (hr : ∀ j t, r j t<2^v) :
    let q := 2^(T.guard+v)
    branchChecks T.P q (pack q (fun _ : Fin n => 1)) (fun j => pack q (r j)) ↔
      ∀ t, ∃ i, ∀ p ∈ T.P i, p.1.eval (fun j => r j t) = p.2.eval (fun j => r j t) := by
  let f (e : JMTableau.Affine T.m × JMTableau.Affine T.m) := Affine.weight e.1 + Affine.weight e.2
  let S (i : Fin T.b) := ((T.P i).map f).sum
  have hw (i) (e) (he : e ∈ T.P i) : f e < 2^T.guard := by
    have A : f e ≤ S i := List.le_sum_of_mem (List.mem_map.mpr ⟨e,he,rfl⟩)
    have B : S i ≤ ∑ j,S j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have C : f e ≤ T.guard := by change _ ≤ 1+T.b+∑ j,S j; omega
    exact C.trans_lt Nat.lt_two_pow_self
  have bounds (i) (e) (he : e ∈ T.P i) := hw i e he
  have hvw : 2^v ≤ 2^(T.guard+v) := Nat.pow_le_pow_right (by decide) (by omega)
  apply branchChecks_iff T.P r (by have := guard_pos T; omega)
    (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (by unfold guard; omega)))
    (fun j t => (hr j t).trans_le hvw)
  · intro i p hp t
    apply JMTableau.Affine.eval_lt _ _ (fun j => hr j t)
    exact (Nat.le_add_right (Affine.weight p.1) _).trans_lt (bounds i p hp)
  · intro i p hp t
    apply JMTableau.Affine.eval_lt _ _ (fun j => hr j t)
    exact (Nat.le_add_left (Affine.weight p.2) _).trans_lt (bounds i p hp)

end DiophantineNP.JMTableau.TraceTable
