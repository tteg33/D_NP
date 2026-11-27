import DiophantineNP.Readout
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! A concrete fixed polynomial for the modular verification stage, when
the modulus, multiplier and scale are supplied. All seventeen witnesses are
natural numbers. False instances admit no root of any size in that domain. -/
namespace DiophantineNP.ModularPolynomial

open MvPolynomial

/-- Witness slots 0–3 contain the CRT selectors and the two readout residues,
4–8 contain Euclidean quotients, and 9–16 contain nonnegative comparison slacks. -/
private def residuals {R : Type*} [CommRing R] (a b D J m : R) (w : Fin 17 → R) : List R :=
  [w 0 + w 9 + 1 - D, w 1 + w 10 + 1 - D,
   w 2 + w 11 + 1 - D, w 3 + w 12 + 1 - D,
   w 0 * w 0 - (D * w 4 + w 0), w 1 * w 1 - (D * w 5 + w 1),
   w 0 * w 1 - (D * w 6 + w 0),
   w 0 * J - (D * w 7 + w 2), w 1 * J - (D * w 8 + w 3),
   m * w 2 + w 13 - a * D, a * D + 1 + w 14 - (m * w 2 + D),
   m * w 3 + w 15 - b * D, b * D + 1 + w 16 - (m * w 3 + D)]

private def squares {R : Type*} [CommRing R] : List R → R
  | [] => 0
  | h :: t => h^2 + squares t

/-- The five input slots are (a,b,D,J,m). -/
noncomputable def polynomial : MvPolynomial (Fin 5 ⊕ Fin 17) ℤ :=
  squares (residuals (X (.inl 0)) (X (.inl 1)) (X (.inl 2)) (X (.inl 3))
    (X (.inl 4)) (fun i => X (.inr i)))

def assignment (a b D J m : ℕ) (w : Fin 17 → ℕ) : Fin 5 ⊕ Fin 17 → ℤ :=
  Sum.elim (fun i => match i.val with
    | 0 => a | 1 => b | 2 => D | 3 => J | _ => m) (fun i => w i)

private theorem squares_nonneg (xs : List ℤ) : 0 ≤ squares xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact add_nonneg (sq_nonneg _) ih

private theorem squares_zero_iff (xs : List ℤ) :
    squares xs = 0 ↔ ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => simp [squares]
  | cons x xs ih =>
    change x^2 + squares xs = 0 ↔ _
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (squares_nonneg _)]
    simp [ih]

private def System (a b D J m : ℕ) (w : Fin 17 → ℕ) : Prop :=
  w 0 + w 9 + 1 = D ∧ w 1 + w 10 + 1 = D ∧
  w 2 + w 11 + 1 = D ∧ w 3 + w 12 + 1 = D ∧
  w 0 * w 0 = D * w 4 + w 0 ∧ w 1 * w 1 = D * w 5 + w 1 ∧
  w 0 * w 1 = D * w 6 + w 0 ∧
  w 0 * J = D * w 7 + w 2 ∧ w 1 * J = D * w 8 + w 3 ∧
  m * w 2 + w 13 = a * D ∧ a * D + 1 + w 14 = m * w 2 + D ∧
  m * w 3 + w 15 = b * D ∧ b * D + 1 + w 16 = m * w 3 + D

private theorem polynomial_zero_iff (a b D J m : ℕ) (w : Fin 17 → ℕ) :
    eval (assignment a b D J m w) polynomial = 0 ↔ System a b D J m w := by
  let x := assignment a b D J m w
  have he : eval x polynomial =
      squares (residuals (a:ℤ) b D J m (fun i => (w i:ℤ))) := by
    simp [polynomial, squares, residuals, x, assignment]
  change eval x polynomial = 0 ↔ _
  rw [he, squares_zero_iff]
  simp only [System, residuals, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, sub_eq_zero]
  exact_mod_cast Iff.rfl

private theorem remainder {x D r q : ℕ} (hr : r < D) (hx : x = D*q+r) : x % D = r := by
  rw [hx, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

private theorem expand {x D r : ℕ} (hx : x % D = r) : x = D*(x/D)+r := by
  have := Nat.mod_add_div x D
  omega

theorem root_implies_certificate (F : Readout.Frame) {a b : ℕ} {w : Fin 17 → ℕ}
    (hw : eval (assignment a b F.D F.J F.m w) polynomial = 0) : F.Certificate a b := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩ := (polynomial_zero_iff ..).mp hw
  have hS : w 0 < F.D := by omega
  have hT : w 1 < F.D := by omega
  have hN : w 2 < F.D := by omega
  have hM : w 3 < F.D := by omega
  refine ⟨w 0, hS, w 1, hT, ?_, ?_, ?_, ?_, ?_⟩
  · exact (remainder hS h4).trans (Nat.mod_eq_of_lt hS).symm
  · exact (remainder hT h5).trans (Nat.mod_eq_of_lt hT).symm
  · exact (remainder hS h6).trans (Nat.mod_eq_of_lt hS).symm
  · rw [remainder hN h7]
    constructor <;> omega
  · rw [remainder hM h8]
    constructor <;> omega

/-- Size of the supplied inputs on the ordinary scale. Its square bounds
each numerical witness, so its logarithm bounds the bit cost of each slot. -/
def bound (a b D J m : ℕ) := (a+b+D+J+m+2)^2

theorem certificate_has_bounded_root (F : Readout.Frame) {a b : ℕ} (hc : F.Certificate a b) :
    ∃ w : Fin 17 → ℕ, eval (assignment a b F.D F.J F.m w) polynomial = 0 ∧
      ∀ i, w i ≤ bound a b F.D F.J F.m := by
  obtain ⟨S,hS,T,hT,hs,ht,hst,hca,hcb⟩ := hc
  let N := S*F.J % F.D
  let M := T*F.J % F.D
  have hN : N < F.D := Nat.mod_lt _ F.D_pos
  have hM : M < F.D := Nat.mod_lt _ F.D_pos
  let w : Fin 17 → ℕ := fun i => match i.val with
    | 0 => S | 1 => T | 2 => N | 3 => M
    | 4 => S*S/F.D | 5 => T*T/F.D | 6 => S*T/F.D
    | 7 => S*F.J/F.D | 8 => T*F.J/F.D
    | 9 => F.D-S-1 | 10 => F.D-T-1 | 11 => F.D-N-1 | 12 => F.D-M-1
    | 13 => a*F.D-F.m*N | 14 => F.m*N+F.D-a*F.D-1
    | 15 => b*F.D-F.m*M | _ => F.m*M+F.D-b*F.D-1
  refine ⟨w, (polynomial_zero_iff ..).mpr ?_, ?_⟩
  · have eS := expand (Eq.trans hs (Nat.mod_eq_of_lt hS))
    have eT := expand (Eq.trans ht (Nat.mod_eq_of_lt hT))
    have eST := expand (Eq.trans hst (Nat.mod_eq_of_lt hS))
    have eN := expand (show S*F.J % F.D = N from rfl)
    have eM := expand (show T*F.J % F.D = M from rfl)
    obtain ⟨c₁,c₂⟩ := hca
    obtain ⟨c₃,c₄⟩ := hcb
    change F.m * N ≤ a * F.D at c₁
    change a * F.D < F.m * N + F.D at c₂
    change F.m * M ≤ b * F.D at c₃
    change b * F.D < F.m * M + F.D at c₄
    dsimp only [System, w, Fin.val_ofNat]
    repeat' constructor <;> omega
  · let K := a+b+F.D+F.J+F.m+2
    have hprod : ∀ {u v : ℕ}, u ≤ K → v ≤ K → u*v ≤ K^2 :=
      fun hu hv => by simpa [pow_two] using Nat.mul_le_mul hu hv
    have hdk : F.D ≤ K := by dsimp [K]; omega
    have hjk : F.J ≤ K := by dsimp [K]; omega
    have hak : a ≤ K := by dsimp [K]; omega
    have hbk : b ≤ K := by dsimp [K]; omega
    have hmk : F.m+1 ≤ K := by dsimp [K]; omega
    have hsK := hS.le.trans hdk
    have htK := hT.le.trans hdk
    have hnK := hN.le.trans hdk
    have hmK := hM.le.trans hdk
    have hDsq : F.D ≤ K^2 := by simpa using (hprod (u:=1) (by dsimp [K]; omega) hdk)
    have p0 := hprod hsK hsK
    have p1 := hprod htK htK
    have p2 := hprod hsK htK
    have p3 := hprod hsK hjk
    have p4 := hprod htK hjk
    have p5 := hprod hak hdk
    have p6 := hprod hbk hdk
    have p7 : F.m*F.D+F.D ≤ K^2 := by simpa [Nat.add_mul] using hprod hmk hdk
    have p8 := Nat.mul_le_mul_left F.m hN.le
    have p9 := Nat.mul_le_mul_left F.m hM.le
    have d0 := Nat.div_le_self (S*S) F.D
    have d1 := Nat.div_le_self (T*T) F.D
    have d2 := Nat.div_le_self (S*T) F.D
    have d3 := Nat.div_le_self (S*F.J) F.D
    have d4 := Nat.div_le_self (T*F.J) F.D
    intro i
    change w i ≤ K^2
    fin_cases i <;> dsimp [w] <;> omega

end DiophantineNP.ModularPolynomial
