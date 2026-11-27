import DiophantineNP.Observation
import Mathlib.Logic.Equiv.Fin.Basic

/-! # The concrete cyclic grid behind the finite-formula induction -/
namespace DiophantineNP.ConcreteGrid

open Real
set_option maxRecDepth 3000
def J (U : ℕ) := 2*radius U+1
@[irreducible] def Q (U : ℕ) : ℤ := (2*(radius U:ℤ)+1)*(2*(radius U:ℤ)+2)^30

theorem fourQ (U : ℕ) : 4*Q U = (size U : ℤ) := by
  unfold size Grid.period Q
  push_cast
  ring

private theorem hRadius (U : ℕ) : 2 ≤ radius U ∧ U ≤ radius U := by
  simp [radius]

theorem radius_lt_Q (U : ℕ) : (radius U:ℤ) < Q U := by
  unfold Q
  have hr := hRadius U
  have hp : (1:ℤ) ≤ (2*(radius U:ℤ)+2)^30 := one_le_pow₀ (by omega)
  nlinarith [mul_le_mul_of_nonneg_left hp (by omega : 0≤2*(radius U:ℤ)+1)]

def centered {U : ℕ} (i : Fin (J U)) : ℤ := (i.val:ℤ)-radius U

theorem c_bound {U : ℕ} (i : Fin (J U)) : |centered i| ≤ radius U := by
  have hi := i.isLt
  unfold J at hi
  rw [centered, abs_le]
  omega

def atArc {U : ℕ} (i : Fin (J U)) (b : Bool) : ℤ :=
  if b then 4*Q U-(Q U+centered i) else Q U+centered i

theorem atArc_spec {U : ℕ} (i : Fin (J U)) (b : Bool) :
    0 ≤ atArc i b ∧ atArc i b < size U ∧ Grid.fold (Q U) (atArc i b) = centered i := by
  have hf := Grid.fold_fiber ((c_bound i).trans_lt (radius_lt_Q U))
  rw [← fourQ]
  exact (hf.2.2.2 _).mpr (by cases b <;> simp [atArc])

def arc {U : ℕ} (p : Fin (J U) × Bool) : Fin (size U) :=
  ⟨(atArc p.1 p.2).toNat, by have := atArc_spec p.1 p.2; omega⟩

theorem arc_val {U : ℕ} (i : Fin (J U)) (b : Bool) :
    ((arc (i,b)).val:ℤ) = atArc i b :=
  Int.toNat_of_nonneg (atArc_spec i b).1

private theorem arc_inj (U : ℕ) : Function.Injective (@arc U) := by
  rintro ⟨i,b⟩ ⟨j,d⟩ h
  have he := congrArg (fun l : Fin (size U) => (l.val:ℤ)) h
  dsimp only at he
  rw [arc_val, arc_val] at he
  have heq : centered i = centered j := by
    rw [← (atArc_spec i b).2.2, he, (atArc_spec j d).2.2]
  have hij : i = j := by apply Fin.ext; unfold centered at heq; omega
  subst j
  have hf := (Grid.fold_fiber ((c_bound i).trans_lt (radius_lt_Q U))).2.1
  have hbd : b = d := by
    cases b <;> cases d
    · rfl
    · simp only [atArc, Bool.false_eq_true, ↓reduceIte] at he
      omega
    · simp only [atArc, Bool.false_eq_true, ↓reduceIte] at he
      omega
    · rfl
  rw [hbd]

private theorem in_range_iff (U : ℕ) (l : Fin (size U)) :
    l ∈ Set.range (@arc U) ↔ |Grid.fold (Q U) l.val| ≤ (radius U:ℤ) := by
  constructor
  · rintro ⟨⟨i,b⟩,rfl⟩
    rw [arc_val, (atArc_spec i b).2.2]
    exact c_bound i
  · intro h
    let j := Grid.fold (Q U) l.val
    have hj : -(radius U:ℤ) ≤ j ∧ j ≤ radius U := abs_le.mp h
    let i : Fin (J U) := ⟨(j+radius U).toNat, by unfold J; omega⟩
    have hci : centered i = j := by unfold centered i; dsimp only; omega
    have hlt : (l.val:ℤ)<4*Q U := by rw [fourQ]; exact_mod_cast l.isLt
    have hf := (Grid.fold_fiber (h.trans_lt (radius_lt_Q U))).2.2.2 l.val
    rcases hf.mp ⟨Int.natCast_nonneg l.val,hlt,rfl⟩ with h₁|h₂
    · refine ⟨(i,false), Fin.ext ?_⟩
      have he := arc_val i false
      simp only [atArc, Bool.false_eq_true, ↓reduceIte, hci] at he
      omega
    · refine ⟨(i,true), Fin.ext ?_⟩
      have he := arc_val i true
      simp only [atArc, ↓reduceIte, hci] at he
      omega

abbrev Invalid (U : ℕ) := Fin (2*radius U+1-U) × Bool
abbrev Outside (U : ℕ) := {l : Fin (size U) // ¬ l ∈ Set.range (@arc U)}
noncomputable instance outsideFintype (U : ℕ) : Fintype (Outside U) := Fintype.ofFinite _

def selectedEquiv (U : ℕ) : (Fin U × Bool ⊕ Invalid U) ≃ Fin (J U) × Bool :=
  (Equiv.sumProdDistrib _ _ _).symm.trans (Equiv.prodCongr
    (finSumFinEquiv.trans (finCongr (by unfold J; have := hRadius U; omega))) (Equiv.refl _))

/-- The correspondence counts every root once, the two arcs of each native
label twice, and the remaining roots in a separate summand. -/
noncomputable def roots (U : ℕ) :
    Counting.LabelGrid U (Invalid U) (Outside U) ≃ Fin (size U) := by
  classical
  exact (Equiv.sumCongr ((selectedEquiv U).trans (Equiv.ofInjective arc (arc_inj U)))
    (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range (@arc U)))

theorem roots_selected (U : ℕ) (z : (Fin U × Bool) ⊕ Invalid U) :
    roots U (.inl z) = arc (selectedEquiv U z) := rfl

theorem roots_outside (U : ℕ) (z : Outside U) : roots U (.inr z) = z.val := rfl

private noncomputable def geometry (U : ℕ) := Grid.paperGeometry (radius U) (hRadius U).1
private def dist (U : ℕ) (l : Fin (size U)) := (Grid.fold (Q U) l.val).natAbs
private noncomputable def rootX (U : ℕ) (l : Fin (size U)) : ℝ :=
  (geometry U).B - (geometry U).M*cos (2*π*(l.val:ℝ)/(geometry U).M)/(2*(geometry U).P)
private noncomputable def rootY (U : ℕ) (l : Fin (size U)) : ℝ :=
  (((geometry U).P*(2*(geometry U).B+1)/(geometry U).M)^2 - cos (2*π*(l.val:ℝ)/(geometry U).M)^2)/4

private theorem gM (U : ℕ) : (geometry U).M = (size U:ℝ) := by rw [size]; rfl
theorem fourQ_real (U : ℕ) : 4*(Q U:ℝ) = (size U:ℝ) := by exact_mod_cast fourQ U

private theorem dist_bound (U : ℕ) (l : Fin (size U)) : 4*dist U l ≤ Grid.period (radius U) := by
  have hlt : (l.val:ℤ)<4*Q U := by rw [fourQ]; exact_mod_cast l.isLt
  have hf := Grid.fold_bounds (Int.natCast_nonneg l.val) hlt
  have hh := fourQ U
  rw [← Int.natCast_natAbs] at hf
  change 4*(Grid.fold (Q U) l.val).natAbs ≤ Grid.period (radius U)
  rw [← size]
  omega

private theorem window_eq (U : ℕ) (l : Fin (size U)) :
    rootY U l = (geometry U).window (dist U l) := by
  have hq : 0 < Q U := by have := radius_lt_Q U; omega
  have h := Grid.cos_sq_eq_sin_sq_distance hq (l.val:ℤ)
  rw [fourQ_real] at h
  unfold rootY Grid.Geometry.window Grid.Geometry.angle dist
  rw [gM]
  push_cast at h
  rw [h]

private theorem window_spec (U : ℕ) (l : Fin (size U)) :
    (0 < rootY U l ↔ l ∈ Set.range (@arc U)) ∧
    1/(size U:ℝ)^2 ≤ |rootY U l| ∧ |rootY U l| ≤ 1 := by
  have h := Grid.Geometry.paper_window (radius U) (dist U l) (hRadius U).1 (dist_bound U l)
  dsimp only at h
  rw [window_eq]
  change (0 < (geometry U).window (dist U l) ↔ dist U l ≤ radius U) ∧ 1/(geometry U).M^2 ≤ |(geometry U).window (dist U l)| ∧ |(geometry U).window (dist U l)| ≤ 1 at h
  rw [gM] at h
  refine ⟨h.1.trans ?_, h.2⟩
  rw [in_range_iff, ← Int.natCast_natAbs]
  unfold dist
  exact_mod_cast Iff.rfl

theorem rootX_close {U : ℕ} (i : Fin (J U)) (b : Bool) :
    |rootX U (arc (i,b)) - (i.val:ℝ)| ≤ error U := by
  have hq : 0 < Q U := by have := radius_lt_Q U; omega
  have hfold := Grid.cos_fold hq ((arc (i,b)).val:ℤ)
  rw [fourQ_real] at hfold
  conv_rhs at hfold => rw [arc_val, (atArc_spec i b).2.2]
  push_cast at hfold
  have hcb : |(centered i:ℝ)| ≤ (geometry U).B := by
    change |(centered i:ℝ)| ≤ (radius U:ℝ)
    exact_mod_cast c_bound i
  have he := (geometry U).label_error hcb
  unfold rootX
  rw [gM, hfold]
  unfold Grid.Geometry.angle at he
  rw [gM] at he
  change |((radius U:ℝ)+_) - ((radius U:ℝ)+(centered i:ℝ))| ≤ _ at he
  have hi : (radius U:ℝ)+(centered i:ℝ) = i.val := by unfold centered; push_cast; ring
  rw [hi] at he
  unfold error
  simpa only [mul_neg, neg_div, sub_neg_eq_add] using he

/-- The geometric input to the finite-arithmetic syntax induction comes
from its literal cosine and window formulas on the complete cyclic grid. -/
noncomputable def observed (U : ℕ) : Observed U (Invalid U) (Outside U) where
  card_eq := (Fintype.card_congr (roots U)).trans (Fintype.card_fin _)
  x z := rootX U (roots U z)
  Y z := rootY U (roots U z)
  x_bound z := by
    have h := (geometry U).observable_bound (abs_le.mpr
      ⟨neg_one_le_cos (2*π*((roots U z).val:ℝ)/(geometry U).M), cos_le_one _⟩)
    exact h.le.trans (le_of_eq (gM U))
  y_bound z := (window_spec U (roots U z)).2.2
  y_selected z := by
    rw [roots_selected]
    let i := selectedEquiv U z
    have h := window_spec U (arc i)
    have hpos : 0 < rootY U (arc i) := h.1.mpr ⟨i,rfl⟩
    simpa only [abs_of_pos hpos] using h.2.1
  y_off o := by
    rw [roots_outside]
    have h := window_spec U o.val
    have hn : rootY U o.val ≤ 0 := not_lt.mp (fun hp => o.prop (h.1.mp hp))
    have hw := h.2.1
    rw [abs_of_nonpos hn] at hw
    linarith
  close_valid i b := by
    exact rootX_close (selectedEquiv U (.inl (i,b))).1 b
  close_invalid k := by
    refine ⟨U+k.1.val, by omega, ?_, ?_⟩
    · have := k.1.isLt
      have := hRadius U
      omega
    · exact rootX_close (selectedEquiv U (.inr k)).1 k.2

/-- On the actual roots, the two observation fields are computed by these
rational Laurent expressions in the cosine. -/
theorem observation_formulas {U : ℕ} (p : Counting.LabelGrid U (Invalid U) (Outside U)) :
    let M := size U
    let B := radius U
    let P := Wallis.approxPi (M^4)
    let c := Real.cos (2*Real.pi*((roots U p).val:ℝ)/(M:ℝ))
    ((observed U).x p = (B:ℝ)-(M:ℝ)*c/(2*P)) ∧
    ((observed U).Y p = ((P*(2*B+1)/(M:ℝ))^2-c^2)/4) := by
  have gb : (geometry U).B = (radius U:ℝ) := rfl
  have gp : (geometry U).P = Wallis.approxPi ((size U)^4) := by unfold size; rfl
  dsimp only
  change (rootX U (roots U p) = _) ∧ (rootY U (roots U p) = _)
  simp only [rootX,rootY,gb,gp,gM, and_self]

end DiophantineNP.ConcreteGrid
