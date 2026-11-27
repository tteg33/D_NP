import DiophantineNP.Statement
import DiophantineNP.Counting
import DiophantineNP.WidthFrame

/-! # From the packing theorem to the two CRT width graphs

The two propositions specify the uniform width descriptions of §2.1 and the
packing theorem of §3. The specialization substitutes the numerical universe
size into one fixed polynomial.
-/
namespace DiophantineNP.Packing

open MvPolynomial Counting WidthData

/-- Pack a formula with a distinguished first free variable, in little-endian order. -/
def packed {k U : ℕ} (φ : Formula (k+1)) (t : Fin k → Fin U) : ℕ :=
  Readout.word (fun j => if h : j < U then φ.eval (Fin.cases ⟨j,h⟩ t) else false) U

inductive Slot (k : ℕ) where
  | universeSize
  | parameter (i : Fin k)
  | output

def arguments {k U : ℕ} (t : Fin k → Fin U) (y : ℤ) : Slot k → ℤ
  | .universeSize => U
  | .parameter i => (t i).val
  | .output => y

/-- Theorem 3.1 as a proposition. The fixed polynomial precedes every input
quantifier; the signed candidate output and all dishonest witnesses are unrestricted. -/
def PackingClaim : Prop :=
  ∀ (k : ℕ) (φ : Formula (k+1)), ∃ (r C : ℕ) (P : MvPolynomial (Slot k ⊕ Fin r) ℤ),
    ∀ U : ℕ, 0 < U → ∀ t : Fin k → Fin U,
      (∃ w : Fin r → ℤ, intCost w ≤ (1+U)^C ∧
        aeval (Sum.elim (arguments t (packed φ t)) w) P = 0) ∧
      (∀ (y : ℤ) (w : Fin r → ℤ), aeval (Sum.elim (arguments t y) w) P = 0 →
        y = (packed φ t : ℤ))

def widthParam (n : ℕ) : Fin 1 → Fin (WidthData.universeSize n) :=
  fun _ => ⟨n, width_parameter_fits n⟩

def Describes (φ : Formula 2) (f : ℕ → ℕ) : Prop :=
  ∀ n, 0 < n → ∀ j : Fin (WidthData.universeSize n),
    φ.eval (Fin.cases j (widthParam n)) = (f n).testBit j

/-- Lemma 2.2, specialized to the actual two sequences of §2. -/
def WidthDescriptions : Prop :=
  (∃ φ, Describes φ widthD) ∧ (∃ φ, Describes φ widthJ)

private theorem word_congr {n : ℕ} {f g : ℕ → Bool} (h : ∀ i < n, f i = g i) :
    Readout.word f n = Readout.word g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Readout.word f n + (f n).toNat * 2^n = Readout.word g n + (g n).toNat * 2^n
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem packed_width_eq {φ : Formula 2} {f : ℕ → ℕ} (hf : Describes φ f)
    {n : ℕ} (hn : 0 < n) (fits : f n < 2^(WidthData.universeSize n)) :
    packed φ (widthParam n) = f n := by
  unfold packed
  refine (word_congr (g := (f n).testBit) ?_).trans (Readout.word_native fits)
  intro i hi
  simp only [dif_pos hi]
  exact hf n hn ⟨i, hi⟩

/-- Replace the universe input with the polynomial (n+2)^20 and the sole
parameter with n. The output slot remains a free signed integer. -/
noncomputable def specialize {r : ℕ} (P : MvPolynomial (Slot 1 ⊕ Fin r) ℤ) :
    Equation (Fin r) :=
  bind₁ (Sum.elim (fun s => match s with
    | .universeSize => (X (.inl false) + 2)^20
    | .parameter _ => X (.inl false)
    | .output => X (.inl true)) (fun i => X (.inr i))) P

noncomputable def widthValue {r : ℕ} (P : Equation (Fin r)) (n : ℕ) (y : ℤ)
    (w : Fin r → ℤ) : ℤ :=
  aeval (Sum.elim (fun b : Bool => if b then y else (n : ℤ)) w) P

theorem specialize_value {r : ℕ} (P : MvPolynomial (Slot 1 ⊕ Fin r) ℤ) (n : ℕ) (y : ℤ)
    (w : Fin r → ℤ) : widthValue (specialize P) n y w =
      aeval (Sum.elim (arguments (widthParam n) y) w) P := by
  unfold widthValue specialize
  rw [aeval_bind₁]
  apply congrArg (fun f : Slot 1 ⊕ Fin r → ℤ => aeval f P)
  funext s
  rcases s with s | i
  · cases s with
    | universeSize =>
      simp only [Sum.elim_inl, map_pow, map_add, map_ofNat, aeval_X, arguments]
      change ((n : ℤ) + 2)^20 = ((n+2)^20 : ℕ)
      push_cast
      rfl
    | parameter i => simp only [Sum.elim_inl, aeval_X]; rfl
    | output => simp only [Sum.elim_inl, aeval_X]; rfl
  · simp

/-- A separate fixed polynomial for a width word, with honest total auxiliary
bits polynomial in n and uniquely determined output for witnesses of every size. -/
def HasWidthGraph (f : ℕ → ℕ) : Prop :=
  ∃ (r C : ℕ) (P : Equation (Fin r)), ∀ n : ℕ, 0 < n →
    (∃ w, intCost w ≤ (n+2)^C ∧ widthValue P n (f n) w = 0) ∧
    (∀ y w, widthValue P n y w = 0 → y = (f n : ℤ))

theorem widthGraph_of_description (pack : PackingClaim) {f : ℕ → ℕ} {φ : Formula 2}
    (desc : Describes φ f) (fits : ∀ n, 0 < n → f n < 2^(WidthData.universeSize n)) :
    HasWidthGraph f := by
  obtain ⟨r, C, P, hp⟩ := pack 1 φ
  refine ⟨r, 21*C, specialize P, ?_⟩
  intro n hn
  have hu : 0 < WidthData.universeSize n := (Nat.zero_le n).trans_lt (width_parameter_fits n)
  obtain ⟨honest, sound⟩ := hp _ hu (widthParam n)
  rw [packed_width_eq desc hn (fits n hn)] at honest sound
  constructor
  · obtain ⟨w, cost, hz⟩ := honest
    refine ⟨w, cost.trans ?_, (specialize_value _ _ _ _).trans hz⟩
    have hbase : 1 + WidthData.universeSize n ≤ (n+2)^21 := by
      rw [show (21 : ℕ) = 20+1 by decide, pow_succ]
      let u := WidthData.universeSize n
      change 1+u ≤ u*(n+2)
      have h : 1 ≤ u := hu
      have hmul : u*2 ≤ u*(n+2) := Nat.mul_le_mul_left u (by omega)
      omega
    simpa [pow_mul] using Nat.pow_le_pow_left hbase C
  · intro y w h
    exact sound y w ((specialize_value _ _ _ _).symm.trans h)

theorem widthGraphs (pack : PackingClaim) (uniform : WidthDescriptions) :
    HasWidthGraph widthD ∧ HasWidthGraph widthJ := by
  obtain ⟨⟨φ, hφ⟩, ⟨ψ, hψ⟩⟩ := uniform
  exact ⟨widthGraph_of_description pack hφ (fun n _ => widthD_fits n),
         widthGraph_of_description pack hψ (fun n hn =>
           (widthJ_lt_D n hn).trans (widthD_fits n))⟩

end DiophantineNP.Packing
