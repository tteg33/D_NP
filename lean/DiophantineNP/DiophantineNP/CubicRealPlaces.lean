import DiophantineNP.CurveKummer
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

/-! # The three real embeddings of the cubic descent field and signs on the curve -/
namespace DiophantineNP.Curve37.Kummer
open Polynomial WeierstrassCurve
noncomputable section

def realCubic (r : ℝ) : ℝ := r^3-4*r+2

private theorem root_between (a b : ℝ) (hab : a ≤ b)
    (h : (realCubic a ≤ 0 ∧ 0 ≤ realCubic b) ∨ (realCubic b ≤ 0 ∧ 0 ≤ realCubic a)) :
    ∃ r ∈ Set.Icc a b, realCubic r = 0 := by
  have hc : Continuous realCubic := by unfold realCubic; fun_prop
  rcases h with h | h
  · exact intermediate_value_Icc hab hc.continuousOn h
  · exact intermediate_value_Icc' hab hc.continuousOn h

private theorem root_ranges : ∃ a b c : ℝ, a ∈ Set.Icc (-3) (-2) ∧ b ∈ Set.Icc (1/4) (3/4) ∧
    c ∈ Set.Icc (5/3) (17/10) ∧ realCubic a=0 ∧ realCubic b=0 ∧ realCubic c=0 := by
  obtain ⟨a,ha,e⟩ := root_between (-3) (-2) (by norm_num) (by left; norm_num [realCubic])
  obtain ⟨b,hb,f⟩ := root_between (1/4) (3/4) (by norm_num) (by right; norm_num [realCubic])
  obtain ⟨c,hc,g⟩ := root_between (5/3) (17/10) (by norm_num) (by left; norm_num [realCubic])
  exact ⟨a,b,c,ha,hb,hc,e,f,g⟩

structure RealRoots where
  a : ℝ
  b : ℝ
  c : ℝ
  ha : a ∈ Set.Icc (-3) (-2)
  hb : b ∈ Set.Icc (1/4) (3/4)
  hc : c ∈ Set.Icc (5/3) (17/10)
  za : realCubic a=0
  zb : realCubic b=0
  zc : realCubic c=0

def roots : RealRoots := Classical.choice (show Nonempty RealRoots by
  obtain ⟨a,b,c,h,k,l,e,f,g⟩ := root_ranges
  exact ⟨⟨a,b,c,h,k,l,e,f,g⟩⟩)

def RealRoots.root (s : RealRoots) (i : Fin 3) := ![s.a,s.b,s.c] i

def RealRoots.emb (s : RealRoots) (i : Fin 3) : L →ₐ[ℚ] ℝ :=
  AdjoinRoot.liftHom f (s.root i) (by
    simp only [f,map_add,map_sub,map_mul,map_pow,map_ofNat,aeval_X]; fin_cases i <;> first | exact s.za | exact s.zb | exact s.zc)

@[simp] theorem RealRoots.emb_theta (s : RealRoots) (i : Fin 3) : s.emb i θ = s.root i :=
  AdjoinRoot.liftHom_root ..

private theorem RealRoots.factor (s : RealRoots) (z : ℝ) :
    (z-s.a)*(z-s.b)*(z-s.c)=realCubic z := by
  obtain ⟨a,b,c,⟨ha,ha'⟩,⟨hb,hb'⟩,⟨hc,hc'⟩,za,zb,zc⟩ := s
  dsimp only
  unfold realCubic at *
  have pair (u v : ℝ) (h : u ≠ v) (hu : u^3-4*u+2=0) (hv : v^3-4*v+2=0) :
      u^2+u*v+v^2=4 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (u-v)*(u^2+u*v+v^2-4)=0 by linear_combination hu-hv)).resolve_left
    exact sub_ne_zero.mpr h
  have ab := pair a b (by linarith) za zb
  have bc := pair b c (by linarith) zb zc
  have sum : a+b+c=0 := (mul_eq_zero.mp (show (a-c)*(a+b+c)=0 by linear_combination ab-bc)).resolve_left
    (by linarith)
  have ce : c= -(a+b) := by linarith
  rw [ce]
  linear_combination (a-z)*(ab) - za

abbrev SignPattern := Fin 3 → Bool

/-- The three signs, with `true` for a negative embedding. -/
def signs (x : L) : SignPattern := fun i => decide (roots.emb i x < 0)

theorem emb_image {x y : ℚ} (hp : E.Nonsingular x y) (i : Fin 3) :
    roots.emb i (image (.some hp)) = 4*(x:ℝ)-2*roots.root i := by
  simp [image,triple,map_ofNat]; ring

theorem signs_sq_mul (x z : L) (hz : z ≠ 0) : signs (x*z^2) = signs x := by
  funext i
  have h : roots.emb i z ≠ 0 := (_root_.map_ne_zero _).mpr hz
  simp only [signs,map_mul,map_pow,decide_eq_decide]
  constructor
  · intro hn; by_contra! hx; exact (not_lt_of_ge (mul_nonneg hx (sq_nonneg _))) hn
  · intro hx; exact mul_neg_of_neg_of_pos hx (sq_pos_of_ne_zero h)

/-- A rational point on the curve has either the all-positive signature or
the same real signature as (0,0). -/
theorem point_signs (Q : E.Point) : signs (image Q) = (fun _ => false) ∨
    signs (image Q) = signs (image P) := by
  cases Q with
  | zero => left; funext i; simp [signs,image]
  | @some x y hp =>
    let X := (4:ℝ)*(x:ℝ)
    let a := roots.a
    let b := roots.b
    let c := roots.c
    have ab : a<b := by dsimp [a,b]; linarith [roots.ha.2,roots.hb.1]
    have bc : b<c := by dsimp [b,c]; linarith [roots.hb.2,roots.hc.1]
    have hz : (8*y+4 : ℚ) ≠ 0 := by
      intro hz
      apply cubic_ne_zero x
      have e := curve_eq hp
      have hy : y= -1/2 := by linarith
      rw [hy] at e
      nlinarith only [e]
    have hf := roots.factor (X/2)
    have eqn : (X-2*a)*(X-2*b)*(X-2*c)=(8*(y:ℝ)+4)^2 := by
      have e : (y:ℝ)^2+(y:ℝ)=(x:ℝ)^3-(x:ℝ) := by exact_mod_cast curve_eq hp
      dsimp [X,a,b,c,realCubic] at *
      linear_combination 8*hf-64*e
    have hy : (8*(y:ℝ)+4) ≠ 0 := by exact_mod_cast hz
    have pos := eqn.symm ▸ sq_pos_of_ne_zero hy
    have hP (i : Fin 3) : roots.emb i (image P) = -2*roots.root i := by
      change roots.emb i (triple (4*0) (-2) 0) = _
      simp [triple,map_ofNat]
    by_cases h : 2*c<X
    · left; funext i
      simp only [signs,emb_image,decide_eq_false_iff_not,not_lt]
      fin_cases i <;> change 0 ≤ X-2*_ <;> first | change 0 ≤ X-2*a | change 0 ≤ X-2*b | change 0 ≤ X-2*c
      all_goals linarith
    · right
      have hcneg : X-2*c<0 := by rcases lt_or_eq_of_le (le_of_not_gt h) with lt|eq <;> first | linarith | rw [eq] at pos; simp at pos
      have habneg : (X-2*a)*(X-2*b)<0 := lt_of_not_ge (fun hh => (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hh hcneg.le)) pos)
      have ha : 0<X-2*a := by rcases mul_neg_iff.mp habneg with h|h <;> linarith
      have hb : X-2*b<0 := by rcases mul_neg_iff.mp habneg with h|h <;> linarith
      funext i
      simp only [signs,hP,emb_image,decide_eq_decide]
      fin_cases i <;> dsimp [RealRoots.root]
      all_goals dsimp [a,b,c,X] at *; first | exact iff_of_false (by linarith) (by linarith [roots.ha.2]) | exact iff_of_true (by linarith) (by linarith [roots.hb.1, roots.hc.1])

end
end DiophantineNP.Curve37.Kummer
