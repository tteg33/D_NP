import DiophantineNP.FormulaLeaves
import DiophantineNP.LaurentGrowth
import Mathlib.Data.Rat.Lemmas

/-! # Bit bounds for the actual scalar and trigonometric Laurent leaves -/
namespace DiophantineNP.FormulaLaurent

open LaurentBounds ConcreteGrid
noncomputable section

theorem polyId : Poly id := ⟨1, fun u => by simp [id]⟩

theorem polyToBits {f : ℕ → ℕ} (h : Poly f) : PolyBits f :=
  ⟨f,h,fun u => (Nat.lt_two_pow_self (n := f u)).le⟩

theorem polyRadius : Poly radius :=
  ⟨1, fun u => by rw [radius, pow_one]; omega⟩

theorem polyFixedPow {f : ℕ → ℕ} (h : Poly f) (n : ℕ) : Poly (fun u => f u ^ n) := by
  obtain ⟨c,hc⟩ := h
  exact ⟨c*n, fun u => (Nat.pow_le_pow_left (hc u) n).trans_eq (pow_mul _ _ _).symm⟩

theorem polySize : Poly size := by
  have a := (poly_const 2).mul polyRadius
  have b := (poly_const 4).mul (a.add (poly_const 1))
  apply (b.mul (polyFixedPow (a.add (poly_const 2)) 30)).mono
  intro u
  rw [size,Grid.period]

/-- Bounds for the reduced numerator and denominator. -/
def RatBits (f : ℕ → ℚ) : Prop :=
  PolyBits (fun u => (f u).num.natAbs) ∧ PolyBits (fun u => (f u).den)

namespace RatBits
variable {f g : ℕ → ℚ}

theorem const (a : ℚ) : RatBits (fun _ => a) :=
  ⟨polyBits_const _,polyBits_const _⟩

theorem natCast {f : ℕ → ℕ} (h : PolyBits f) : RatBits (fun u => (f u:ℚ)) := by
  simpa only [RatBits,Rat.num_natCast,Int.natAbs_natCast,Rat.den_natCast] using
    And.intro h (polyBits_const 1)

theorem neg (hf : RatBits f) : RatBits (fun u => -(f u)) := by
  simpa only [RatBits,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hf

theorem mul (hf : RatBits f) (hg : RatBits g) : RatBits (fun u => f u*g u) := by
  constructor
  · refine (hf.1.mul hg.1).mono fun u => ?_
    rw [Rat.mul_num, ← Int.natAbs_mul]
    exact Int.natAbs_ediv_le_natAbs _ _
  · exact (hf.2.mul hg.2).mono fun u => Nat.le_of_dvd (Nat.mul_pos (f u).den_pos (g u).den_pos) (Rat.mul_den_dvd _ _)

theorem add (hf : RatBits f) (hg : RatBits g) : RatBits (fun u => f u+g u) := by
  constructor
  · refine ((hf.1.mul hg.2).add (hf.2.mul hg.1)).mono fun u => ?_
    have h := Rat.add_num_den (f u) (g u)
    obtain ⟨c,hc,hd⟩ := Rat.num_den_mk
      (mul_ne_zero (Int.natCast_ne_zero.mpr (f u).den_nz) (Int.natCast_ne_zero.mpr (g u).den_nz)) h
    have hc0 : c ≠ 0 := by
      intro hh
      rw [hh,zero_mul] at hd
      exact (mul_ne_zero (Int.natCast_ne_zero.mpr (f u).den_nz) (Int.natCast_ne_zero.mpr (g u).den_nz)) hd
    have hle := Nat.le_mul_of_pos_left (f u+g u).num.natAbs (Int.natAbs_pos.mpr hc0)
    rw [← Int.natAbs_mul, ← hc] at hle
    have ha := Int.natAbs_add_le ((f u).num*(g u).den) ((f u).den*(g u).num)
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at ha
    exact hle.trans ha
  · exact (hf.2.mul hg.2).mono fun u => Nat.le_of_dvd
      (Nat.mul_pos (f u).den_pos (g u).den_pos) (Rat.add_den_dvd _ _)

theorem inv (hf : RatBits f) : RatBits (fun u => (f u)⁻¹) := by
  constructor
  · apply hf.2.mono
    intro u
    rw [Rat.num_inv, Int.natAbs_mul, Int.natAbs_sign, Int.natAbs_natCast]
    split <;> simp
  · apply (hf.1.add (polyBits_const 1)).mono
    intro u
    rw [Rat.den_inv]
    split <;> omega

theorem div (hf : RatBits f) (hg : RatBits g) : RatBits (fun u => f u/g u) := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

theorem pow (hf : RatBits f) {n : ℕ → ℕ} (hn : Poly n) : RatBits (fun u => (f u)^(n u)) := by
  simpa only [RatBits,Rat.num_pow,Int.natAbs_pow,Rat.den_pow] using
    And.intro (hf.1.pow hn) (hf.2.pow hn)

theorem admissible {d : ℕ} (hf : RatBits f) : Admissible (fun u => rational (d := d) (f u)) :=
  .scalar _ _ hf.1 hf.2
end RatBits

private theorem wallisBits : RatBits (fun u => piRational ((size u)^4)) := by
  let β := fun u => (size u)^4
  have hb : Poly β := polyFixedPow polySize 4
  have hc : PolyBits (fun u => (2*β u).choose (β u)) := by
    apply ((polyBits_const 2).pow ((poly_const 2).mul hb)).mono
    intro u
    have hsum := Nat.sum_range_choose (2*β u)
    have h := Finset.single_le_sum (f := fun i => (2*β u).choose i)
      (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : β u < 2*β u+1))
    simpa only [hsum] using h
  exact ((RatBits.const 16).pow hb).div
    ((RatBits.natCast (polyToBits hb)).mul ((RatBits.natCast hc).pow (poly_const 2)))

theorem cosineLeaf_admissible {d : ℕ} (j : Fin d) :
    Admissible (fun _ => cosineLeaf j) := by
  have hm (s : ℤ) : Admissible (fun _ => mono j s) := .monomial _ (poly_const _)
  exact .mul (RatBits.const (1/2)).admissible (.add (hm 1) (hm (-1)))

theorem xLeaf_admissible {d : ℕ} (j : Fin d) :
    Admissible (fun u => xLeaf u j) :=
  .add (RatBits.natCast (polyToBits polyRadius)).admissible
    (.mul (((RatBits.natCast (polyToBits polySize)).neg).div ((RatBits.const 2).mul wallisBits)).admissible
      (cosineLeaf_admissible j))

theorem yLeaf_admissible {d : ℕ} (j : Fin d) :
    Admissible (fun u => yLeaf u j) := by
  have J := ((RatBits.const 2).mul (RatBits.natCast (polyToBits polyRadius))).add (RatBits.const 1)
  have h := (((wallisBits.mul J).div (RatBits.natCast (polyToBits polySize))).pow
    (poly_const 2)).div (RatBits.const 4)
  exact .add h.admissible (.mul (RatBits.const (-1/4)).admissible
    (.pow (cosineLeaf_admissible j) _ (poly_const 2)))

end
end DiophantineNP.FormulaLaurent
