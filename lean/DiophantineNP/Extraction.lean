import Std

/-!
# Signed radix extraction

This file proves the integer arithmetic used in the scalar partial-mean
evaluator (the manuscript's lemma "Extraction of a cyclic mean"). Coefficients
are stored in increasing order of degree. The two divisions in
`extractCoefficient` use Euclidean integer division and also work for negative
coefficients and negative evaluations.
-/

namespace DiophantineNP.Extraction

/-- Horner evaluation of a dense list of integer coefficients, constant first. -/
def evaluate (z : Int) : List Int → Int
  | [] => 0
  | a :: as => a + z * evaluate z as

/-- Sum of the absolute values of the coefficients. -/
def mass : List Int → Int
  | [] => 0
  | a :: as => (a.natAbs : Int) + mass as

theorem mass_nonneg (as : List Int) : 0 ≤ mass as := by
  induction as with
  | nil => decide
  | cons a as ih => simp only [mass]; omega

theorem abs_bounds (a : Int) :
    -(a.natAbs : Int) ≤ a ∧ a ≤ (a.natAbs : Int) := by
  cases a <;> simp [Int.natAbs] <;> omega

theorem evaluate_append (z : Int) (lo hi : List Int) :
    evaluate z (lo ++ hi) = evaluate z lo + z ^ lo.length * evaluate z hi := by
  induction lo with
  | nil => simp [evaluate]
  | cons a lo ih =>
    simp only [List.cons_append, List.length_cons, evaluate, ih, Int.pow_succ]
    grind

theorem mass_append (lo hi : List Int) :
    mass (lo ++ hi) = mass lo + mass hi := by
  induction lo with
  | nil => simp [mass]
  | cons a lo ih => simp [mass, ih, Int.add_assoc]

/-- Upper and lower bounds for a polynomial consisting only of low digits. -/
theorem evaluate_scaled_bounds (z : Int) (hz : 0 < z) (lo : List Int) :
    -(mass lo * z ^ lo.length) ≤ z * evaluate z lo ∧
    z * evaluate z lo ≤ mass lo * z ^ lo.length := by
  induction lo with
  | nil => simp [mass, evaluate]
  | cons a lo ih =>
    let p := z ^ lo.length
    have hp : 0 < p := Int.pow_pos hz
    have hmag : 0 ≤ (a.natAbs : Int) := by omega
    have habs := abs_bounds a
    have hexpand := Int.mul_le_mul_of_nonneg_left (show 1 ≤ p by omega) hmag
    have hLo : -(((a.natAbs : Int) + mass lo) * p) ≤ a + z * evaluate z lo := by
      change -(mass lo * p) ≤ _ ∧ _ ≤ mass lo * p at ih
      grind
    have hHi : a + z * evaluate z lo ≤ ((a.natAbs : Int) + mass lo) * p := by
      change -(mass lo * p) ≤ _ ∧ _ ≤ mass lo * p at ih
      grind
    have hL := Int.mul_le_mul_of_nonneg_left hLo (Int.le_of_lt hz)
    have hU := Int.mul_le_mul_of_nonneg_left hHi (Int.le_of_lt hz)
    change -(mass (a :: lo) * z ^ (lo.length+1)) ≤ _ ∧ _ ≤ _
    simp only [mass, evaluate, List.length_cons, Int.pow_succ]
    dsimp [p] at hL hU
    grind

/-- Round a rational to its nearest integer, breaking ties upwards. -/
def nearest (v d : Int) : Int := (2*v+d)/(2*d)

/-- Center an integer residue, taking the interval `[-z/2,z/2)`. -/
def centered (v z : Int) : Int := v - z * nearest v z

/-- The two manuscript operations: round after scaling, then center the residue. -/
def extractCoefficient (value z : Int) (k : Nat) : Int :=
  centered (nearest value (z ^ k)) z

/-- On a strict half-unit interval, rounded division removes the low part. -/
theorem nearest_eq_of_error (v d q : Int) (hd : 0 < d)
    (hl : -d ≤ 2*(v-d*q)) (hu : 2*(v-d*q) < d) :
    nearest v d = q := by
  let r := 2*(v-d*q)+d
  have hr : 0 ≤ r := by dsimp [r]; omega
  have hr' : r < 2*d := by dsimp [r]; omega
  have heq : 2*v+d = r+(2*d)*q := by dsimp [r]; grind
  rw [nearest, heq, Int.add_mul_ediv_left _ _ (by omega),
      Int.ediv_eq_zero_of_lt hr hr', Int.zero_add]

/-- A residue in the centered interval survives removing arbitrary higher digits. -/
theorem centered_eq_of_decomposition (a q z : Int) (hz : 0 < z)
    (hl : -z ≤ 2*a) (hu : 2*a < z) :
    centered (a+z*q) z = a := by
  have e : a+z*q-z*q = a := by omega
  rw [centered, nearest_eq_of_error _ _ q hz (by simpa [e] using hl)
      (by simpa [e] using hu)]
  omega

/-- Scaling by the length of a low prefix and rounding discards that prefix. -/
theorem nearest_append (lo hi : List Int) (z : Int) (h : 2 * mass lo < z) :
    nearest (evaluate z (lo ++ hi)) (z ^ lo.length) = evaluate z hi := by
  have h0 := mass_nonneg lo
  have hz : 0 < z := by omega
  let d := z ^ lo.length
  have hd : 0 < d := Int.pow_pos hz
  obtain ⟨hL,hU⟩ := evaluate_scaled_bounds z hz lo
  change -(mass lo * d) ≤ _ at hL
  change _ ≤ mass lo * d at hU
  have hmul := Int.mul_lt_mul_of_pos_right h hd
  have hltU : z*(2*evaluate z lo) < z*d := by grind
  have hltL : z*(-d) < z*(2*evaluate z lo) := by grind
  have hup := Int.lt_of_mul_lt_mul_left hltU (Int.le_of_lt hz)
  have hlow := Int.lt_of_mul_lt_mul_left hltL (Int.le_of_lt hz)
  apply nearest_eq_of_error _ _ _ hd
  all_goals rw [evaluate_append]
  all_goals dsimp [d] at *
  all_goals omega

/-- One integer evaluation determines any indicated signed coefficient when
twice the total absolute coefficient mass is strictly less than the radix.
The lists `lo` and `hi` specify the degrees on each side of the coefficient. -/
theorem extractCoefficient_eq (lo hi : List Int) (a z : Int)
    (h : 2 * mass (lo ++ a :: hi) < z) :
    extractCoefficient (evaluate z (lo ++ a :: hi)) z lo.length = a := by
  have h0 := mass_nonneg lo
  have h1 := mass_nonneg hi
  rw [mass_append] at h
  simp only [mass] at h
  have hz : 0 < z := by omega
  rw [extractCoefficient, nearest_append _ _ _ (by omega)]
  apply centered_eq_of_decomposition _ _ _ hz
  all_goals have := abs_bounds a
  all_goals omega

/-- Zero extension permits extraction at and beyond the highest stored degree. -/
def coefficient : List Int → Nat → Int
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, k+1 => coefficient as k

private theorem splitAtDegree (z : Int) (cs : List Int) (k : Nat) :
    ∃ lo hi : List Int, lo.length = k ∧
      evaluate z (lo ++ coefficient cs k :: hi) = evaluate z cs ∧
      mass (lo ++ coefficient cs k :: hi) = mass cs := by
  induction k generalizing cs with
  | zero =>
    cases cs with
    | nil => exact ⟨[], [], by simp, by simp [coefficient, evaluate], by simp [coefficient, mass]⟩
    | cons a cs => exact ⟨[], cs, rfl, rfl, rfl⟩
  | succ k ih =>
    cases cs with
    | nil =>
      obtain ⟨lo,hi,hl,he,hm⟩ := ih []
      refine ⟨0 :: lo, hi, by simp [hl], ?_, ?_⟩
      simp only [List.cons_append, evaluate, coefficient] at he ⊢
      rw [he]; simp
      simp only [List.cons_append, mass, coefficient] at hm ⊢
      rw [hm]; decide
    | cons a cs =>
      obtain ⟨lo,hi,hl,he,hm⟩ := ih cs
      exact ⟨a :: lo, hi, by simp [hl], by simp only [List.cons_append, coefficient, evaluate, he],
        by simp only [List.cons_append, coefficient, mass, hm]⟩

theorem extractCoefficient_at (cs : List Int) (k : Nat) (z : Int)
    (h : 2 * mass cs < z) :
    extractCoefficient (evaluate z cs) z k = coefficient cs k := by
  obtain ⟨lo,hi,hlen,hv,hm⟩ := splitAtDegree z cs k
  simpa only [hv, hlen] using extractCoefficient_eq lo hi (coefficient cs k) z (by rwa [hm])

/-- Add coefficient lists using implicit zeros at missing degrees. -/
def addCoeffs : List Int → List Int → List Int
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a+b) :: addCoeffs as bs

theorem addCoeffs_eval (as bs : List Int) (z : Int) :
    evaluate z (addCoeffs as bs) = evaluate z as + evaluate z bs := by
  induction as generalizing bs with
  | nil => simp [addCoeffs, evaluate]
  | cons a as ih =>
    cases bs with
    | nil => simp [addCoeffs, evaluate]
    | cons b bs => simp only [addCoeffs, evaluate, ih]; grind

theorem addCoeffs_mass (as bs : List Int) :
    mass (addCoeffs as bs) ≤ mass as + mass bs := by
  induction as generalizing bs with
  | nil => simp [addCoeffs, mass]
  | cons a as ih =>
    cases bs with
    | nil => simp [addCoeffs, mass]
    | cons b bs =>
      have := Int.natAbs_add_le a b
      have := ih bs
      simp only [addCoeffs, mass]
      omega

theorem addCoeffs_coeff (as bs : List Int) (k : Nat) :
    coefficient (addCoeffs as bs) k = coefficient as k + coefficient bs k := by
  induction as generalizing bs k with
  | nil => simp [addCoeffs, coefficient]
  | cons a as ih =>
    cases bs with
    | nil => simp [addCoeffs, coefficient]
    | cons b bs => cases k <;> simp [addCoeffs, coefficient, ih]

/-- Multiply a coefficient list by the monomial of degree `n`. -/
def shift : Nat → List Int → List Int
  | 0, cs => cs
  | n+1, cs => 0 :: shift n cs

private theorem shift_eval (n : Nat) (cs : List Int) (z : Int) :
    evaluate z (shift n cs) = z^n * evaluate z cs := by
  induction n with
  | zero => simp [shift]
  | succ n ih => simp [shift, evaluate, Int.pow_succ, ih]; grind

private theorem shift_mass (n : Nat) (cs : List Int) :
    mass (shift n cs) = mass cs := by
  induction n <;> simp [shift, mass, *]

private theorem shift_coeff (n k : Nat) (cs : List Int) :
    coefficient (shift n cs) k =
      (if n ≤ k then coefficient cs (k-n) else 0) := by
  induction n generalizing k with
  | zero => simp [shift]
  | succ n ih => cases k <;> simp [shift, coefficient, ih]

/-- Geometric kernel with `n` terms. -/
def geometric (r : Int) : Nat → Int
  | 0 => 0
  | n+1 => geometric r n + r^n

theorem geometric_identity (r : Int) (n : Nat) :
    (r-1)*geometric r n = r^n-1 := by
  induction n with
  | zero => simp [geometric]
  | succ n ih => simp only [geometric, Int.pow_succ]; grind

/-- The coefficient list after multiplication by `1 + X^m + ... + X^(m*(n-1))`. -/
def applyKernel (m : Nat) : Nat → List Int → List Int
  | 0, _ => []
  | n+1, cs => addCoeffs (applyKernel m n cs) (shift (m*n) cs)

private theorem powProduct (z : Int) (m n : Nat) : z^(m*n) = (z^m)^n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.mul_succ, Int.pow_add, Int.pow_succ, ih]

private theorem applyKernel_eval (m n : Nat) (cs : List Int) (z : Int) :
    evaluate z (applyKernel m n cs) = evaluate z cs * geometric (z^m) n := by
  induction n with
  | zero => simp [applyKernel, evaluate, geometric]
  | succ n ih =>
    simp only [applyKernel, addCoeffs_eval, shift_eval, ih, geometric, powProduct]
    grind

private theorem applyKernel_mass (m n : Nat) (cs : List Int) :
    mass (applyKernel m n cs) ≤ n * mass cs := by
  induction n with
  | zero => simp [applyKernel, mass]
  | succ n ih =>
    have h := addCoeffs_mass (applyKernel m n cs) (shift (m*n) cs)
    simp only [shift_mass] at h
    simp only [applyKernel, Int.natCast_succ, Int.add_mul, Int.one_mul]
    omega

/-- Backward samples starting at degree `k`, spaced by the period `m`.
Samples at negative indices contribute zero. -/
def periodicSum (cs : List Int) (m k : Nat) : Nat → Int
  | 0 => 0
  | n+1 => periodicSum cs m k n + if m*n ≤ k then coefficient cs (k-m*n) else 0

private theorem applyKernel_coeff (m n k : Nat) (cs : List Int) :
    coefficient (applyKernel m n cs) k = periodicSum cs m k n := by
  induction n with
  | zero => simp [applyKernel, periodicSum, coefficient]
  | succ n ih => simp [applyKernel, addCoeffs_coeff, periodicSum, shift_coeff, ih]

/-- Single-evaluation extraction of a periodic sum of signed coefficients.
For the manuscript use `cs` for the coefficients of `X^b L(X)`, `k = 2*b`,
and `n = 2*b/m+1`. The proof's auxiliary coefficient list is absent from
the scalar expression on the left. -/
theorem extract_periodic_sum (cs : List Int) (m n k : Nat) (z : Int)
    (h : 2 * (n * mass cs) < z) :
    extractCoefficient (evaluate z cs * geometric (z^m) n) z k =
      periodicSum cs m k n := by
  have hb := applyKernel_mass m n cs
  have h' : 2 * mass (applyKernel m n cs) < z := by omega
  simpa only [applyKernel_eval, applyKernel_coeff] using
    extractCoefficient_at (applyKernel m n cs) k z h'

/-- Exact division computes the geometric multiplier without iterating over
its terms, including when there are zero terms. -/
theorem geometric_quotient (r : Int) (n : Nat) (hr : r ≠ 1) :
    (r^n-1)/(r-1) = geometric r n := by
  rw [← geometric_identity, Int.mul_ediv_cancel_left _ (by omega)]

/-- Closed-form version of periodic extraction. This evaluates the input word
once and uses a fixed number of scalar operations, including variable powers. -/
theorem extract_periodic_quotient (cs : List Int) (m n k : Nat) (z : Int)
    (hm : 0 < m) (hz : 1 < z) (h : 2 * (n * mass cs) < z) :
    extractCoefficient (evaluate z cs * ((z^(m*n)-1)/(z^m-1))) z k =
      periodicSum cs m k n := by
  have hpow := Int.pow_lt_pow_of_lt hz (show 0 < m from hm)
  simp only [Int.pow_zero] at hpow
  rw [powProduct z m n, geometric_quotient _ _ (by omega)]
  exact extract_periodic_sum cs m n k z h

/-- For a Laurent polynomial shifted up by `b`, the sampled exponents are
precisely the multiples of the period in the interval from `-b` to `b`.
The index `h` records the term of the geometric multiplier. -/
theorem periodic_indices (b m : Nat) (hm : 0 < m) (hb : m ∣ b) (t : Int) :
    (-(b : Int) ≤ t ∧ t ≤ (b : Int) ∧ (m : Int) ∣ t) ↔
      ∃ h : Nat, h ≤ 2*b/m ∧ t = (b : Int)-(m : Int)*(h : Int) := by
  obtain ⟨u, rfl⟩ := hb
  have hq : 2*(m*u)/m = 2*u := by
    rw [show 2*(m*u) = m*(2*u) by ac_rfl, Nat.mul_div_cancel_left _ hm]
  rw [hq, Int.natCast_mul]
  have hM : 0 < (m : Int) := by omega
  constructor
  · rintro ⟨hL,hU,q,rfl⟩
    have qU : q ≤ (u : Int) := Int.le_of_mul_le_mul_left hU hM
    have qL : -(u : Int) ≤ q :=
      Int.le_of_mul_le_mul_left (by simpa [Int.mul_neg] using hL) hM
    let h := ((u : Int)-q).toNat
    have he : (h : Int) = (u : Int)-q := Int.toNat_of_nonneg (by omega)
    refine ⟨h, by omega, ?_⟩
    rw [he]; grind
  · rintro ⟨h,hh,rfl⟩
    have hv : (h : Int) ≤ 2*(u : Int) := by omega
    have hu := Int.mul_le_mul_of_nonneg_left hv (Int.le_of_lt hM)
    have hl : 0 ≤ (m : Int)*(h : Int) := Int.mul_nonneg (by omega) (by omega)
    refine ⟨by grind, by omega, (u : Int)-(h : Int), by grind⟩

theorem periodic_index_unique (b m h₁ h₂ : Nat) (hm : 0 < m)
    (h : (b : Int)-(m : Int)*(h₁ : Int) = (b : Int)-(m : Int)*(h₂ : Int)) :
    h₁ = h₂ := by
  have eq : (m : Int)*(h₁ : Int) = (m : Int)*(h₂ : Int) := by omega
  have eq' := Int.eq_of_mul_eq_mul_left (by omega : (m : Int) ≠ 0) eq
  omega

end DiophantineNP.Extraction
