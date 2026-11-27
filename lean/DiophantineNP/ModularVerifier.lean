import DiophantineNP.ModularPolynomial
import DiophantineNP.WidthFrame
import DiophantineNP.Statement
import Mathlib.NumberTheory.SumFourSquares

/-! The modular polynomial over unrestricted signed witnesses. Each of the seventeen
natural witnesses is replaced by four integer squares. The resulting equation has
the same five inputs for every width, and its honest witness cost is cubic in the
width when the correct width words are supplied. -/
namespace DiophantineNP.ModularPolynomial

open MvPolynomial
open WidthData

abbrev SignedSlots := Fin 17 × Fin 4

private def four {R : Type*} [CommRing R] (v : Fin 4 → R) : R :=
  v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2

private noncomputable def sub : Fin 5 ⊕ Fin 17 → MvPolynomial (Fin 5 ⊕ SignedSlots) ℤ :=
  Sum.elim (fun i => X (Sum.inl i)) (fun j => four (fun k => X (Sum.inr (j,k))))

noncomputable def signedPolynomial : MvPolynomial (Fin 5 ⊕ SignedSlots) ℤ :=
  bind₁ sub polynomial

def signedAssignment (a b D J m : ℕ) (u : SignedSlots → ℤ) : Fin 5 ⊕ SignedSlots → ℤ :=
  Sum.elim (fun i => assignment a b D J m (fun _ => 0) (.inl i)) u

def unpack (u : SignedSlots → ℤ) (j : Fin 17) : ℕ :=
  (four (fun k => u (j,k))).toNat

private theorem unpack_cast (u : SignedSlots → ℤ) (j : Fin 17) :
    (unpack u j : ℤ) = four (fun k => u (j,k)) := by
  apply Int.toNat_of_nonneg
  unfold four
  positivity

theorem eval_signed (a b D J m : ℕ) (u : SignedSlots → ℤ) :
    eval (signedAssignment a b D J m u) signedPolynomial =
    eval (assignment a b D J m (unpack u)) polynomial := by
  change aeval _ (bind₁ _ polynomial) = aeval _ polynomial
  rw [aeval_bind₁]
  apply congrArg (fun f : Fin 5 ⊕ Fin 17 → ℤ => aeval f polynomial)
  funext i
  cases i with
  | inl i => simp [sub, signedAssignment, assignment]
  | inr j => simp [sub, signedAssignment, four, assignment, unpack_cast]

private theorem pack (w : Fin 17 → ℕ) :
    ∃ u : SignedSlots → ℤ, unpack u = w ∧ ∀ i, (u i).natAbs ≤ w i.1 := by
  choose a b c d h using fun j => Nat.sum_four_squares (w j)
  let u : SignedSlots → ℤ := fun s => match s.2.val with
    | 0 => a s.1 | 1 => b s.1 | 2 => c s.1 | _ => d s.1
  refine ⟨u, ?_, ?_⟩
  · funext j
    have he : four (fun k => u (j,k)) = (w j : ℤ) := by
      change (a j : ℤ)^2 + (b j : ℤ)^2 + (c j : ℤ)^2 + (d j : ℤ)^2 = (w j : ℤ)
      exact_mod_cast h j
    simp [unpack, he]
  · intro ⟨j,k⟩
    have hh := h j
    have sqle (v : ℕ) : v ≤ v^2 := by
      cases v with
      | zero => decide
      | succ v => nlinarith
    have ha := sqle (a j)
    have hb := sqle (b j)
    have hc := sqle (c j)
    have hd := sqle (d j)
    fin_cases k <;> dsimp [u] <;> omega

private theorem concrete_bound {n a b : ℕ} (hn : 0 < n) (ha : a < 2^n) (hb : b < 2^n) :
    bound a b (widthD n) (widthJ n) (scale n) ≤ 2^(40*(n+2)^3+6) := by
  let H := 20*(n+2)^3
  have hsmall : n+2 ≤ H := by dsimp [H]; nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^2)]
  have hm : scale n ≤ 2^H := Nat.pow_le_pow_right (by decide) hsmall
  have hn' : 2^n ≤ scale n := (frame n hn).scale
  have ha' := ha.le.trans (hn'.trans hm)
  have hb' := hb.le.trans (hn'.trans hm)
  have hd : widthD n ≤ 2^H := widthD_bound n
  have hj := (widthJ_lt_D n hn).le.trans hd
  have hp := Nat.two_pow_pos H
  have hs : a+b+widthD n+widthJ n+scale n+2 ≤ 2^H * 8 := by omega
  unfold bound
  calc
    _ ≤ (2^H * 8)^2 := Nat.pow_le_pow_left hs 2
    _ = (2^(H+3))^2 := by rw [pow_add]; norm_num
    _ = _ := by rw [← pow_mul]; congr 1; dsimp [H]; omega

private theorem bits_le {z k : ℕ} (h : z ≤ 2^k) : bits z ≤ k+1 := by
  by_cases hz : z = 0
  · simp [hz, bits]
  · have hpow := (Nat.log2_self_le hz).trans h
    have hlog := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
    unfold bits
    omega

/-- Every modular certificate forces both input words to fit its own width. -/
theorem certificate_bounds (F : Readout.Frame) {a b : ℕ} (h : F.Certificate a b) :
    a < 2^F.n ∧ b < 2^F.n := by
  obtain ⟨S,_,T,_,hS,hT,_,hca,hcb⟩ := h
  have ea := Readout.ceiling_unique hca (F.readout S _ (F.select_correct hS))
  have eb := Readout.ceiling_unique hcb (F.readout T _ (F.select_correct hT))
  rw [ea, eb]
  exact ⟨Readout.word_lt _ _, Readout.word_lt _ _⟩

theorem nat_root_implies_incl {n a b : ℕ} (hn : 0 < n) {w : Fin 17 → ℕ}
    (hw : eval (assignment a b (widthD n) (widthJ n) (scale n) w) polynomial = 0) :
    BitIncl a b := by
  let F := frame n hn
  have hc := root_implies_certificate F hw
  obtain ⟨ha,hb⟩ := certificate_bounds F hc
  exact (F.certificate_iff ha hb).1 hc

theorem signed_root_implies_incl {n a b : ℕ} (hn : 0 < n) {u : SignedSlots → ℤ}
    (hu : eval (signedAssignment a b (widthD n) (widthJ n) (scale n) u) signedPolynomial = 0) :
    BitIncl a b := by
  rw [eval_signed] at hu
  exact nat_root_implies_incl hn hu

/-- The natural version uses seventeen witness slots with an explicit total bit cost. -/
theorem native_natural_complete {n a b : ℕ} (hn : 0 < n) (ha : a < 2^n) (hb : b < 2^n)
    (yes : BitIncl a b) : ∃ w : Fin 17 → ℕ, natCost w ≤ 17*(40*(n+2)^3+7) ∧
      eval (assignment a b (widthD n) (widthJ n) (scale n) w) polynomial = 0 := by
  let F := frame n hn
  obtain ⟨w,hw,hbound⟩ := certificate_has_bounded_root F ((F.certificate_iff ha hb).2 yes)
  refine ⟨w, ?_, hw⟩
  unfold natCost
  calc
    _ ≤ ∑ _i : Fin 17, (40*(n+2)^3+7) := by
      apply Finset.sum_le_sum
      intro i _
      exact bits_le ((hbound i).trans (concrete_bound hn ha hb))
    _ = _ := by simp

/-- All widths use the same five-input polynomial. Soundness holds for every signed
tuple. On a true instance its 68 coordinates have an explicit total signed bit bound. -/
theorem native_modular_verifier {n a b : ℕ} (hn : 0 < n) (ha : a < 2^n) (hb : b < 2^n) :
    (BitIncl a b → ∃ u : SignedSlots → ℤ,
      intCost u ≤ 68*(40*(n+2)^3+8) ∧
      eval (signedAssignment a b (widthD n) (widthJ n) (scale n) u) signedPolynomial = 0) ∧
    (∀ u : SignedSlots → ℤ,
      eval (signedAssignment a b (widthD n) (widthJ n) (scale n) u) signedPolynomial = 0 →
      BitIncl a b) := by
  let F := frame n hn
  constructor
  · intro yes
    obtain ⟨w, hw, hbound⟩ := certificate_has_bounded_root F ((F.certificate_iff ha hb).2 yes)
    obtain ⟨u, hu, huBound⟩ := pack w
    refine ⟨u, ?_, ?_⟩
    · unfold intCost
      calc
        _ ≤ ∑ _i : SignedSlots, (40*(n+2)^3+8) := by
          apply Finset.sum_le_sum
          intro i _
          have h := (huBound i).trans ((hbound i.1).trans (concrete_bound hn ha hb))
          have hh := bits_le h
          omega
        _ = _ := by simp [SignedSlots]
    · rw [eval_signed, hu]
      exact hw
  · intro u h
    rw [eval_signed] at h
    exact (F.certificate_iff ha hb).1 (root_implies_certificate F h)

end DiophantineNP.ModularPolynomial
