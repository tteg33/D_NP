import DiophantineNP.HABSourceArithmetic

/-! # Exact left shift in the HAB source vocabulary

Every set input bit must have a representable translated position, and every
set output bit must come from one of those positions. This detects overflow. -/
namespace DiophantineNP.HAB

/-- The graph z = x·2^d on the finite index sort. -/
def indexShift {k : ℕ} (x d z : Fin k) : Form k :=
  .conj
    (.all (.disj (.neg (.BIT 0 x.succ))
      (.ex (.conj (indexAdd 1 d.succ.succ 0) (.BIT 0 z.succ.succ)))))
    (.all (.disj (.neg (.BIT 0 z.succ))
      (.ex (.conj (indexAdd 0 d.succ.succ 1) (.BIT 0 x.succ.succ)))))

private theorem pos_lt {n i U : ℕ} (hn : n<U) (hi : n.testBit i=true) : i<U :=
  (Nat.lt_two_pow_self (n:=i)).trans_le (Nat.ge_two_pow_of_testBit hi) |>.trans hn

theorem indexShift_correct {k U : ℕ} (x d z : Fin k) (A : Matrix U) (e : Fin k→Fin U) :
    (indexShift x d z).Holds A e ↔ (e z).val=(e x).val*2^(e d).val := by
  classical
  simp only [indexShift,Form.Holds,indexAdd_correct,Fin.cases_zero,Fin.cases_succ]
  constructor
  · rintro ⟨forward,backward⟩
    apply Nat.eq_of_testBit_eq
    intro n
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_mul_two_pow,Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · intro hn
      obtain ⟨t,ht,hx⟩ := (backward ⟨n,pos_lt (e z).isLt hn⟩).resolve_left (not_not_intro hn)
      have he : t.val+(e d).val=n := ht
      exact ⟨by omega,by simpa [show n-(e d).val=t.val by omega] using hx⟩
    · rintro ⟨hd,hx⟩
      obtain ⟨t,ht,hz⟩ := (forward ⟨n-(e d).val,pos_lt (e x).isLt hx⟩).resolve_left (not_not_intro hx)
      have he : n-(e d).val+(e d).val=t.val := ht
      simpa [show t.val=n by omega] using hz
  · intro he
    constructor
    · intro i
      by_cases hi : (e x).val.testBit i.val=true
      · right
        have hz : (e z).val.testBit (i.val+(e d).val)=true := by
          rw [he,Nat.testBit_mul_two_pow]; simp [hi]
        exact ⟨⟨_,pos_lt (e z).isLt hz⟩,rfl,hz⟩
      · exact Or.inl hi
    · intro j
      by_cases hj : (e z).val.testBit j.val=true
      · right
        rw [he,Nat.testBit_mul_two_pow,Bool.and_eq_true,decide_eq_true_eq] at hj
        exact ⟨⟨_,pos_lt (e x).isLt hj.2⟩, Nat.sub_add_cancel hj.1,hj.2⟩
      · exact Or.inl hj

end DiophantineNP.HAB
