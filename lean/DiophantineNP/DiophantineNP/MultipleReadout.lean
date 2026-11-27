import DiophantineNP.WidthFrame
import Mathlib.Data.Fintype.Pigeonhole

/-! # Replacing a CRT modulus and multiplier by a common multiple

The extra prime factors can contribute idempotent coordinates of their own.
Lifting both selectors and intersecting them preserves the native order test.
-/
namespace DiophantineNP.Readout

/-- A positive power of any residue is idempotent. Its value, reduced modulo
N, is small even though the exponent is only used for the existence proof. -/
private theorem has_idem_power (a N : ℕ) (hn : 0 < N) :
    ∃ e : ℕ, 0 < e ∧ a^e * a^e ≡ a^e [MOD N] := by
  let f (i : Fin (N+1)) : Fin N := ⟨a^i.val % N,Nat.mod_lt _ hn⟩
  obtain ⟨i,j,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have eqp : ∃ t d : ℕ, 0 < d ∧ a^t ≡ a^(t+d) [MOD N] := by
    rcases lt_or_gt_of_ne hne with h|h
    · refine ⟨i.val,j.val-i.val,by omega,?_⟩
      rw [Nat.add_sub_of_le (Nat.le_of_lt h)]
      exact congrArg Fin.val he
    · refine ⟨j.val,i.val-j.val,by omega,?_⟩
      rw [Nat.add_sub_of_le (Nat.le_of_lt h)]
      exact congrArg Fin.val he.symm
  obtain ⟨t,d,hd,he⟩ := eqp
  have shift {m : ℕ} (hm : t ≤ m) : a^m ≡ a^(m+d) [MOD N] := by
    obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hm
    simpa [pow_add,Nat.mul_right_comm,Nat.mul_assoc,Nat.mul_left_comm] using he.mul_right (a^b)
  let e := (t+1)*d
  have hpos : 0 < e := Nat.mul_pos (Nat.succ_pos _) hd
  have hte : t ≤ e := (Nat.le_succ t).trans (Nat.le_mul_of_pos_right _ hd)
  have multi (k : ℕ) : a^e ≡ a^(e+k*d) [MOD N] := by
    induction k with
    | zero => simp [Nat.ModEq]
    | succ k ih =>
      rw [Nat.succ_mul,← Nat.add_assoc]
      exact ih.trans (shift (hte.trans (Nat.le_add_right ..)))
  refine ⟨e,hpos,?_⟩
  rw [← pow_add]
  exact (multi (t+1)).symm

private theorem idem_pow {D s : ℕ} (h : s*s ≡ s [MOD D]) {m : ℕ} (hm : 0<m) : s^m ≡ s [MOD D] := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  induction k with
  | zero => simp [Nat.ModEq]
  | succ k ih => rw [pow_succ]; exact ((ih (Nat.succ_pos _)).mul_right s).trans h

/-- The same existential conditions as `Frame.Certificate` with D,J explicit. -/
def modulusCertificate (D J m a b : ℕ) := ∃ S < D, ∃ T < D,
  S*S ≡ S [MOD D] ∧ T*T ≡ T [MOD D] ∧ S*T ≡ S [MOD D] ∧
  Ceiling D m (S*J % D) a ∧ Ceiling D m (T*J % D) b

private theorem scaled_ceiling (D J m a S k : ℕ) (hk : 0<k) :
    Ceiling (k*D) m (S*(k*J) % (k*D)) a ↔ Ceiling D m (S*J % D) a := by
  rw [show S*(k*J) = k*(S*J) by ring,Nat.mul_mod_mul_left]
  unfold Ceiling
  rw [show m*(k*((S*J)%D)) = k*(m*((S*J)%D)) by ring,show a*(k*D) = k*(a*D) by ring,← Nat.mul_add]
  simp [hk]

/-- Common positive scaling is invisible to the sound and complete native
certificate test. No coprimality assumption on the scaling factor is needed. -/
theorem modulusCertificate_scale_iff (D J m a b k : ℕ) (hD : 0<D) (hk : 0<k) :
    modulusCertificate (k*D) (k*J) m a b ↔ modulusCertificate D J m a b := by
  have hN := Nat.mul_pos hk hD
  have hv : D ∣ k*D := dvd_mul_left ..
  constructor
  · rintro ⟨S,_,T,_,hs,ht,hst,ha,hb⟩
    have si := Nat.mod_modEq S D
    have ti := Nat.mod_modEq T D
    refine ⟨S%D,Nat.mod_lt _ hD,T%D,Nat.mod_lt _ hD,(si.mul si).trans ((hs.of_dvd hv).trans si.symm),
      (ti.mul ti).trans ((ht.of_dvd hv).trans ti.symm),(si.mul ti).trans ((hst.of_dvd hv).trans si.symm),?_,?_⟩
    · have e := si.mul_right J
      rw [e]; exact (scaled_ceiling D J m _ _ k hk).mp ha
    · have e := ti.mul_right J
      rw [e]; exact (scaled_ceiling D J m _ _ k hk).mp hb
  · rintro ⟨S,_,T,_,hs,ht,hst,ha,hb⟩
    obtain ⟨u,hu,su⟩ := has_idem_power S (k*D) hN
    obtain ⟨v,hv',tv⟩ := has_idem_power T (k*D) hN
    let s := S^u*T^v % (k*D)
    let t := T^v % (k*D)
    have sN : s ≡ S^u*T^v [MOD k*D] := Nat.mod_modEq ..
    have tN : t ≡ T^v [MOD k*D] := Nat.mod_modEq ..
    have sD : s ≡ S [MOD D] := (sN.of_dvd hv).trans (((idem_pow hs hu).mul (idem_pow ht hv')).trans hst)
    have tD : t ≡ T [MOD D] := (tN.of_dvd hv).trans (idem_pow ht hv')
    refine ⟨s,Nat.mod_lt _ hN,t,Nat.mod_lt _ hN,(sN.mul sN).trans (?_ : _ ≡ _ [MOD k*D]),
      (tN.mul tN).trans (tv.trans tN.symm),(sN.mul tN).trans (?_ : _ ≡ _ [MOD k*D]),?_,?_⟩
    · rw [show S^u*T^v*(S^u*T^v) = (S^u*S^u)*(T^v*T^v) by ring]
      exact (su.mul tv).trans sN.symm
    · rw [Nat.mul_assoc]; exact (tv.mul_left (S^u)).trans sN.symm
    · apply (scaled_ceiling D J m _ _ k hk).mpr
      rwa [sD.mul_right J]
    · apply (scaled_ceiling D J m _ _ k hk).mpr
      rwa [tD.mul_right J]

/-- The draft's readout therefore works with any positive multiple of the
product of selected prime powers and the corresponding scaled multiplier. -/
theorem Frame.multiple_certificate_iff (F : Frame) (k a b : ℕ) (hk : 0<k) (ha : a<2^F.n) (hb : b<2^F.n) :
    modulusCertificate (k*F.D) (k*F.J) F.m a b ↔ ∀ i, a.testBit i=true → b.testBit i=true :=
  (modulusCertificate_scale_iff F.D F.J F.m a b k F.D_pos hk).trans (F.certificate_iff ha hb)

end DiophantineNP.Readout
