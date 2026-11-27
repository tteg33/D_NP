import DiophantineNP.PackingBridge

/-! A fixed formula for the prime-index stage of §2.1.  Because the candidate
prime is far below half the universe, unary majority can compare a prime count
to the supplied index by reserving a disjoint final segment of the universe. -/
namespace DiophantineNP.PrimeFormula

open Counting
open WidthData

def ltF {k : ℕ} (x y : Fin k) : Formula k := .neg (.atom (.leq y x))

theorem ltF_true {k U : ℕ} (x y : Fin k) (env : Fin k → Fin U) :
    (ltF x y).eval env = true ↔ (env x).val < (env y).val := by
  change (!decide ((env y).val ≤ (env x).val)) = true ↔ _
  simp

theorem exists_true {k U : ℕ} (φ : Formula (k+1)) (env : Fin k → Fin U) :
    (Formula.ex φ).eval env = true ↔ ∃ z : Fin U, φ.eval (Fin.cases z env) = true := by
  simp [Formula.eval, count, Finset.card_pos, Finset.Nonempty]

def atLeast (r : ℕ) : {k : ℕ} → Fin k → Formula k :=
  match r with
  | 0 => fun x => .atom (.eqv x x)
  | r+1 => fun x => .ex (.conj (ltF 0 x.succ) (atLeast r 0))

theorem atLeast_true (r : ℕ) {k U : ℕ} (x : Fin k) (env : Fin k → Fin U) :
    (atLeast r x).eval env = true ↔ r ≤ (env x).val := by
  induction r generalizing k with
  | zero => simp [atLeast, Formula.eval, Atom.eval]
  | succ r ih =>
    rw [atLeast, exists_true]
    simp only [Formula.eval, Bool.and_eq_true, ltF_true, ih, Fin.cases_zero, Fin.cases_succ]
    constructor
    · rintro ⟨j,h,h'⟩; omega
    · intro h
      exact ⟨⟨r, by have := (env x).isLt; omega⟩, by simp; omega, by simp⟩

/-- Primality using order and the graph of multiplication restricted to [U]. -/
private def factorPair {k : ℕ} (x : Fin k) : Formula (k+2) :=
  .conj (ltF 0 x.succ.succ)
    (.conj (ltF (0 : Fin (k+1)).succ x.succ.succ) (.atom (.mul 0 (0 : Fin (k+1)).succ x.succ.succ)))

def prime {k : ℕ} (x : Fin k) : Formula k :=
  .conj (atLeast 2 x) (.neg (.ex (.ex (factorPair x))))

theorem prime_true {k U : ℕ} (x : Fin k) (env : Fin k → Fin U) :
    (prime x).eval env = true ↔ (env x).val.Prime := by
  change ((atLeast 2 x).eval env && !((Formula.ex (.ex (factorPair x))).eval env)) = true ↔ _
  rw [Bool.and_eq_true, atLeast_true, Bool.not_eq_true', ← Bool.not_eq_true, exists_true]
  simp only [exists_true]
  simp only [factorPair, Formula.eval, Bool.and_eq_true, ltF_true, Atom.eval, decide_eq_true_eq,
    Fin.cases_zero, Fin.cases_succ]
  constructor
  · rintro ⟨h2, hn⟩
    by_contra hp
    obtain ⟨a,b,ha,hb,hab⟩ := (Nat.not_prime_iff_exists_mul_eq h2).mp hp
    exact hn ⟨⟨b, hb.trans (env x).isLt⟩, ⟨a, ha.trans (env x).isLt⟩, ha, hb, hab⟩
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    rintro ⟨b,a,ha,hb,hab⟩
    exact ((Nat.not_prime_iff_exists_mul_eq hp.two_le).mpr ⟨_,_,ha,hb,hab⟩) hp

private theorem count_fin_eq (U : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    count (fun j : Fin U => decide (P j.val)) = ((Finset.range U).filter P).card := by
  unfold count
  apply Finset.card_bij (fun j _ => j.val)
  · intro j hj
    simpa using And.intro j.isLt (show P j.val by simpa using hj)
  · intro _ _ _ _ h
    exact Fin.ext h
  · intro a ha
    obtain ⟨hl,hp⟩ := Finset.mem_filter.mp ha
    exact ⟨⟨a, Finset.mem_range.mp hl⟩, by simpa using hp, rfl⟩

private theorem tail_card (U t : ℕ) :
    ((Finset.range U).filter (fun x => t ≤ x)).card = U-t := by
  have he : (Finset.range U).filter (fun x => t ≤ x) = Finset.Ico t U := by
    ext j
    simp [and_comm]
  rw [he, Nat.card_Ico]

private def cut (U : ℕ) : ℕ := U - U / 2

/-- The upper half begins where the suffix ceases to be a strict majority. -/
private def upper {k : ℕ} (x : Fin k) : Formula k :=
  .neg (.maj (.atom (.leq x.succ 0)))

private theorem upper_true {k U : ℕ} (x : Fin k) (env : Fin k → Fin U) :
    (upper x).eval env = true ↔ cut U ≤ (env x).val := by
  change (!decide (U/2 < count (fun z : Fin U => decide ((env x).val ≤ z.val)))) = true ↔ _
  rw [count_fin_eq, tail_card]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  unfold cut
  omega

private def strictUpper {k : ℕ} (x : Fin k) : Formula k :=
  .ex (.conj (upper 0) (ltF 0 x.succ))

private theorem strictUpper_true {k U : ℕ} (x : Fin k) (env : Fin k → Fin U) :
    (strictUpper x).eval env = true ↔ cut U+1 ≤ (env x).val := by
  rw [strictUpper, exists_true]
  simp only [Formula.eval, Bool.and_eq_true, upper_true, ltF_true, Fin.cases_zero, Fin.cases_succ]
  constructor
  · rintro ⟨z,h,h'⟩; omega
  · intro h
    exact ⟨⟨cut U, by have := (env x).isLt; omega⟩, by simp, by dsimp; omega⟩

private def padded {k : ℕ} (later : Bool) (z i : Fin k) : Formula k :=
  .ex (.conj (if later then strictUpper 0 else upper 0) (.atom (.add 0 i.succ z.succ)))

private theorem padded_true {k U : ℕ} (later : Bool) (z i : Fin k) (env : Fin k → Fin U) :
    (padded later z i).eval env = true ↔ cut U + (env i).val + later.toNat ≤ (env z).val := by
  rw [padded, exists_true]
  have hh (v : Fin U) : ((if later then strictUpper 0 else upper 0) : Formula (k+1)).eval
      (Fin.cases v env) = true ↔ cut U+later.toNat ≤ v.val := by
    cases later <;> simp [upper_true, strictUpper_true]
  simp only [Formula.eval, Bool.and_eq_true, hh, Atom.eval, decide_eq_true_eq,
    Fin.cases_succ, Fin.cases_zero]
  constructor
  · rintro ⟨v,h,h'⟩; omega
  · intro h
    exact ⟨⟨(env z).val-(env i).val, by have := (env z).isLt; omega⟩, by dsimp; omega, by dsimp; omega⟩

private theorem combined_card {p U t : ℕ} (hp : p ≤ t) (ht : t ≤ U) :
    ((Finset.range U).filter (fun x => (x.Prime ∧ x < p) ∨ t ≤ x)).card =
      Nat.count Nat.Prime p + (U-t) := by
  let L := (Finset.range p).filter Nat.Prime
  let R := Finset.Ico t U
  have he : (Finset.range U).filter (fun x => (x.Prime ∧ x < p) ∨ t ≤ x) = L ∪ R := by
    ext x
    simp only [L, R, Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    by_cases hpr : x.Prime <;> simp [hpr] <;> omega
  have hd : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have h1 := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have h2 := (Finset.mem_Ico.mp hy).1
    omega
  rw [he, Finset.card_union_of_disjoint hd, Nat.count_eq_card_filter_range, Nat.card_Ico]

private def rankTest {k : ℕ} (later : Bool) (p i : Fin k) : Formula k :=
  .maj (.disj (.conj (prime 0) (ltF 0 p.succ)) (padded later 0 i.succ))

private theorem rankTest_true {k U : ℕ} (later : Bool) (p i : Fin k) (env : Fin k → Fin U)
    (hp : (env p).val ≤ cut U) (hi : (env i).val+later.toNat ≤ U/2) :
    (rankTest later p i).eval env = true ↔ (env i).val+later.toNat < Nat.count Nat.Prime (env p).val := by
  let t := cut U + (env i).val + later.toNat
  let P := fun x : ℕ => (x.Prime ∧ x < (env p).val) ∨ t ≤ x
  have hfun : (fun z : Fin U => (Formula.disj (.conj (prime 0) (ltF 0 p.succ))
      (padded later 0 i.succ)).eval (Fin.cases z env)) = (fun z => decide (P z.val)) := by
    funext z
    apply Bool.eq_iff_iff.mpr
    simp [Formula.eval, prime_true, ltF_true, padded_true, P, t]
  change decide (U/2 < count _) = true ↔ _
  rw [hfun, count_fin_eq]
  have ht : t ≤ U := by dsimp [t, cut]; omega
  have hpt : (env p).val ≤ t := by dsimp [t]; omega
  rw [show ((Finset.range U).filter P).card = _ from combined_card hpt ht]
  simp only [decide_eq_true_eq]
  dsimp [t, cut]
  omega

/-- Formula with candidate prime at slot zero and zero-based odd-prime index at slot one. -/
def oddPrimeAtVars {k : ℕ} (p i : Fin k) : Formula k :=
  .conj (prime p) (.conj (.neg (upper p)) (.conj (rankTest false p i) (.neg (rankTest true p i))))

theorem oddPrimeAtVars_true {k U : ℕ} (p i : Fin k) (env : Fin k → Fin U) (hi : (env i).val+1 ≤ U/2) :
    (oddPrimeAtVars p i).eval env = true ↔ (env p).val < cut U ∧ (env p).val = Nat.nth Nat.Prime ((env i).val+1) := by
  have h0 := (env p).isLt
  change (_ && ((!_) && (_ && (!_)))) = true ↔ _
  simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, prime_true, upper_true, not_le]
  constructor
  · rintro ⟨hp,hu,hyes,hno⟩
    have h1 := (rankTest_true false p i env hu.le (by simp; omega)).mp hyes
    have h2 := mt (rankTest_true true p i env hu.le (by simpa using hi)).mpr hno
    simp at h1 h2
    have hc : Nat.count Nat.Prime (env p).val = (env i).val+1 := by omega
    exact ⟨hu, by rw [← hc, Nat.nth_count hp]⟩
  · rintro ⟨hu,he⟩
    have hp : (env p).val.Prime := he ▸ Nat.prime_nth_prime _
    have hc : Nat.count Nat.Prime (env p).val = (env i).val+1 := by
      rw [he, Nat.count_nth_of_infinite Nat.infinite_setOf_prime]
    refine ⟨hp,hu,(rankTest_true false p i env hu.le (by simp; omega)).mpr ?_, ?_⟩
    · simp [hc]
    · intro h
      have hh := (rankTest_true true p i env hu.le (by simpa using hi)).mp h
      simp [hc] at hh

def oddPrimeAt : Formula 2 := oddPrimeAtVars 0 1

theorem oddPrimeAt_true {U : ℕ} (env : Fin 2 → Fin U) (hi : (env 1).val+1 ≤ U/2) :
    oddPrimeAt.eval env = true ↔ (env 0).val < cut U ∧ (env 0).val = Nat.nth Nat.Prime ((env 1).val+1) :=
  oddPrimeAtVars_true 0 1 env hi

/-- For every legal index the actual width universe supplies the entire prime
rank relation, including rejection of all spurious candidates outside the window. -/
theorem width_prime_vars {k n : ℕ} (p i : Fin k) (env : Fin k → Fin (universeSize n)) (hi : (env i).val < n) :
    (oddPrimeAtVars p i).eval env = true ↔
      (env p).val = Nat.nth Nat.Prime ((env i).val+1) := by
  let x := n+2
  have hx : 3 ≤ x := by dsimp [x]; omega
  have hx4 : 64 ≤ x^4 := le_trans (by decide : 64 ≤ 3^4) (Nat.pow_le_pow_left hx _)
  have hx6 : 64*x^2 ≤ x^6 := (Nat.mul_le_mul_right (x^2) hx4).trans_eq (pow_add x 4 2).symm
  have hu : 64*x^2 ≤ universeSize n := hx6.trans (Nat.pow_le_pow_right (by omega) (by decide))
  have hK : 32*x^2 ≤ (universeSize n)/2 := by omega
  have hind : (env i).val+1 ≤ universeSize n/2 := by
    have hi' : (env i).val+1 ≤ x := by dsimp [x]; omega
    nlinarith [Nat.mul_self_le_mul_self hx]
  rw [oddPrimeAtVars_true p i env hind]
  change ((env p).val < cut (universeSize n) ∧ (env p).val = Nat.nth Nat.Prime ((env i).val+1)) ↔ _
  constructor
  · exact And.right
  · intro h
    have hp := oddPrime_lt_search_limit hi
    change Nat.nth Nat.Prime ((env i).val+1) < 32*x^2 at hp
    exact ⟨by unfold cut; omega, h⟩

theorem width_prime_formula {n : ℕ} (p i : Fin (universeSize n)) (hi : i.val < n) :
    oddPrimeAt.eval (Fin.cases p (fun _ => i)) = true ↔
      p.val = Nat.nth Nat.Prime (i.val+1) := by
  let env : Fin 2 → Fin (universeSize n) := Fin.cases p (fun _ : Fin 1 => i)
  have hi' : (env 1).val < n := by change i.val < n; exact hi
  have h := width_prime_vars (n := n) 0 1 env hi'
  change (oddPrimeAtVars 0 1).eval env = true ↔ _
  rw [h]
  rfl

end DiophantineNP.PrimeFormula
