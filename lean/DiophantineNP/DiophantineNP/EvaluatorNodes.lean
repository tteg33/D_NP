import DiophantineNP.EvaluatorSemantics
import DiophantineNP.EvaluatorArithmetic

/-! # Uniform scalar terms for Laurent expression constructors -/

namespace DiophantineNP.Blueprint
open LaurentBounds ScalarProgram ScalarProjection FormulaLaurent
open scoped BigOperators
noncomputable section

/-- Terms that evaluate the family `e`, uniformly in the inputs. The terms
`den`, `height`, `radius` do not depend on the point. `num` takes the terms of
the coordinates and returns the term of the cleared numerator. -/
structure Evaluated (I : Type) (d : ℕ) (Valid : (I → ℤ) → Prop) (e : (I → ℤ) → Expr d) where
  den : Term I
  height : Term I
  radius : Term I
  num : (Fin d → Term I) → Term I
  wellFormed : ∀ ι, Valid ι → WellFormed (e ι)
  den_run : ∀ ι, Valid ι → den.run ι = ((evalBounds (e ι)).denominator : ℤ)
  height_run : ∀ ι, Valid ι → height.run ι = ((evalBounds (e ι)).height : ℤ)
  radius_run : ∀ ι, Valid ι → radius.run ι = ((evalBounds (e ι)).radius : ℤ)
  num_run : ∀ ι, Valid ι → ∀ (ctx : Fin d → Term I) (x : Fin d → ℕ),
    (∀ i, (ctx i).run ι = (x i : ℤ)) → (∀ i, 0 < x i) →
      (num ctx).run ι = clearedNum (e ι) x
  den_tame : TameTerm den
  height_tame : TameTerm height
  radius_small : SmallTerm radius
  num_tame : ∀ ctx : Fin d → Term I, (∀ i, TameTerm (ctx i)) → TameTerm (num ctx)

variable {I : Type} {d : ℕ} {Valid : (I → ℤ) → Prop}

/-- A rational leaf given by two terms. The denominator need not be reduced. -/
def Evaluated.scalar (p q : Term I) (hp : TameTerm p) (hq : TameTerm q)
    (pos : ∀ ι, Valid ι → 0 < q.run ι) :
    Evaluated I d Valid (fun ι => .scalar (p.run ι) (Nat.toPNat' (q.run ι).toNat)) := {
  den := q
  height := Arith.add (Arith.mul p p) (.literal 1)
  radius := .literal 0
  num := fun _ => p
  wellFormed := fun _ _ => trivial
  den_run := by
    intro ι hι
    change q.run ι = (((q.run ι).toNat.toPNat' : ℕ) : ℤ)
    have h := pos ι hι
    rw [PNat.toPNat'_coe (by omega), Int.toNat_of_nonneg h.le]
  height_run := by
    intro ι _
    change _ = (((p.run ι).natAbs^2 + 1 : ℕ) : ℤ)
    rw [Nat.cast_add, Nat.cast_pow, Int.natCast_natAbs, sq_abs]
    simp only [Arith.run_add, Arith.run_mul, Arith.run_lit, Nat.cast_one, pow_two]
  radius_run := fun _ _ => rfl
  num_run := fun _ _ _ _ _ _ => rfl
  den_tame := hq
  height_tame := Arith.tame_add (Arith.tame_mul hp hp) (.small (.literal 1))
  radius_small := .literal 0
  num_tame := fun _ _ => hp
}

def Evaluated.monomial (v : Fin d → ℤ) : Evaluated I d Valid (fun _ => .monomial v) := {
  den := .literal 1
  height := .literal 1
  radius := .literal ↑(∑ j, (v j).natAbs)
  num := fun ctx => Arith.prod (fun i => Arith.fixedPow (ctx i) (((∑ j, (v j).natAbs : ℕ) : ℤ) + v i).toNat)
  wellFormed := fun _ _ => trivial
  den_run := fun _ _ => rfl
  height_run := fun _ _ => rfl
  radius_run := fun _ _ => rfl
  num_run := by
    intro ι _ ctx x hctx _
    simp only [Arith.run_prod, Arith.run_fixedPow, hctx, clearedNum]
  den_tame := .small (.literal 1)
  height_tame := .small (.literal 1)
  radius_small := .literal _
  num_tame := fun _ hctx => Arith.tame_prod (fun i => Arith.tame_fixedPow (hctx i) _)
}

namespace Arith
/-- Cleared geometric series including its value at the removable pole `y=2`. -/
def geomSumTerm (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (y J : Term I) : Term I :=
  let gap := sub y (.literal 2)
  let square := fixedPow gap 2
  let twoPow := pow hc hq (.literal 2) J
  let top := mul (mul (sub (pow hc hq y J) twoPow) y) gap
  add (div top square) (mul (sub (.literal 1) (div square square)) (mul J twoPow))

theorem run_geomSumTerm (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (y J : Term I) (ι : I → ℤ) (hJ : 0 ≤ J.run ι) :
    (geomSumTerm hc hq y J).run ι = geomSum (y.run ι) (J.run ι).toNat := by
  rw [geomSum_closed]
  simp [geomSumTerm, Int.toNat_of_nonneg hJ]

theorem tame_geomSumTerm (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {y J : Term I} (hy : TameTerm y) (hJ : SmallTerm J) :
    TameTerm (geomSumTerm hc hq y J) := by
  unfold geomSumTerm
  apply tame_add
  · apply tame_div
    · exact tame_mul (tame_mul (tame_sub (tame_pow hc hq hy hJ)
        (tame_pow hc hq (.small (.literal 2)) hJ)) hy) (tame_sub hy (.small (.literal 2)))
    · exact tame_fixedPow (tame_sub hy (.small (.literal 2))) 2
  · have hs := tame_fixedPow (tame_sub hy (.small (.literal 2))) 2
    exact tame_mul (tame_sub (.small (.literal 1)) (tame_div hs hs))
      (tame_mul (.small hJ) (tame_pow hc hq (.small (.literal 2)) hJ))
end Arith

def Evaluated.geometric (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (j : Fin d)
    (s J : Term I) (hs : SmallTerm s) (hJ : SmallTerm J)
    (nonneg : ∀ ι, Valid ι → 0 ≤ s.run ι ∧ 0 ≤ J.run ι) :
    Evaluated I d Valid (fun ι => .geometric j (s.run ι).toNat (J.run ι).toNat) := by
  let G := Arith.mul J s
  let others (ctx : Fin d → Term I) := Arith.prod
    (fun i => if i=j then .literal 1 else Arith.pow hc hq (ctx i) G)
  let series (ctx : Fin d → Term I) :=
    Arith.geomSumTerm hc hq (Arith.pow hc hq (ctx j) s) J
  refine ⟨.literal 1, Arith.pow hc hq (.literal 2) J, G,
    fun ctx => Arith.mul (others ctx) (series ctx), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ _ => trivial
  · intro ι h; rfl
  · intro ι h; simp [evalBounds]
  · intro ι h
    obtain ⟨hs',hJ'⟩ := nonneg ι h
    simp [G, evalBounds, hs', hJ']
  · intro ι h ctx x he hx
    obtain ⟨hs',hJ'⟩ := nonneg ι h
    have hr : (G.run ι).toNat = (J.run ι).toNat * (s.run ι).toNat := by
      apply Int.ofNat_inj.mp
      simp [G, hJ', hs', Int.mul_nonneg hJ' hs']
    have hothers : (others ctx).run ι =
        ∏ i, if i=j then (1:ℤ) else (x i : ℤ)^((J.run ι).toNat*(s.run ι).toNat) := by
      simp only [others, Arith.run_prod]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hij : i=j <;> simp [hij, hr, he]
    simp [series, Arith.run_geomSumTerm _ _ _ _ _ hJ', hothers, he, clearedNum]
  · exact .small (.literal 1)
  · exact Arith.tame_pow hc hq (.small (.literal 2)) hJ
  · exact Arith.small_mul hJ hs
  · intro ctx ht
    apply Arith.tame_mul
    · apply Arith.tame_prod
      intro i
      by_cases hij : i=j
      · simp only [hij, if_true]; exact .small (.literal 1)
      · simp only [hij, if_false]
        exact Arith.tame_pow hc hq (ht i) (Arith.small_mul hJ hs)
    · exact Arith.tame_geomSumTerm hc hq (Arith.tame_pow hc hq (ht j) hs) hJ

def Evaluated.neg {f : (I → ℤ) → Expr d} (F : Evaluated I d Valid f) :
    Evaluated I d Valid (fun ι => (f ι).neg) := {
  den := F.den
  height := F.height
  radius := F.radius
  num := fun ctx => Arith.sub (.literal 0) (F.num ctx)
  wellFormed := F.wellFormed
  den_run := F.den_run
  height_run := F.height_run
  radius_run := F.radius_run
  num_run := by
    intro ι hι ctx x hctx hx
    rw [Arith.run_sub, Arith.run_lit, zero_sub, F.num_run ι hι ctx x hctx hx]
    rfl
  den_tame := F.den_tame
  height_tame := F.height_tame
  radius_small := F.radius_small
  num_tame := fun ctx hctx => Arith.tame_sub (.small (.literal 0)) (F.num_tame ctx hctx)
}

def Evaluated.add (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) {f g : (I → ℤ) → Expr d}
    (F : Evaluated I d Valid f) (G : Evaluated I d Valid g) :
    Evaluated I d Valid (fun ι => (f ι).add (g ι)) := {
  den := Arith.mul F.den G.den
  height := Arith.add (Arith.mul G.den F.height) (Arith.mul F.den G.height)
  radius := Arith.add F.radius G.radius
  num := fun ctx =>
    let X := Arith.prod ctx
    let summand (D R N : Term I) := Arith.mul (Arith.mul D (Arith.pow hc hq X R)) N
    Arith.add (summand G.den G.radius (F.num ctx)) (summand F.den F.radius (G.num ctx))
  wellFormed := fun ι hι => ⟨F.wellFormed ι hι, G.wellFormed ι hι⟩
  den_run := by
    intro ι hι
    simp only [Arith.run_mul, F.den_run ι hι, G.den_run ι hι, evalBounds, Nat.cast_mul]
  height_run := by
    intro ι hι
    simp only [Arith.run_add, Arith.run_mul, F.den_run ι hι, G.den_run ι hι,
      F.height_run ι hι, G.height_run ι hι, evalBounds, Nat.cast_mul, Nat.cast_add]
  radius_run := by
    intro ι hι
    simp only [Arith.run_add, F.radius_run ι hι, G.radius_run ι hι, evalBounds, Nat.cast_add]
  num_run := by
    intro ι hι ctx x hctx hx
    simp only [Arith.run_add, Arith.run_mul, Arith.run_pow, Arith.run_prod, hctx, F.den_run ι hι,
      G.den_run ι hι, F.radius_run ι hι, G.radius_run ι hι, Int.toNat_natCast,
      F.num_run ι hι ctx x hctx hx, G.num_run ι hι ctx x hctx hx, clearedNum]
  den_tame := Arith.tame_mul F.den_tame G.den_tame
  height_tame := Arith.tame_add (Arith.tame_mul G.den_tame F.height_tame) (Arith.tame_mul F.den_tame G.height_tame)
  radius_small := Arith.small_add F.radius_small G.radius_small
  num_tame := by
    intro ctx hctx
    have hX := Arith.tame_prod hctx
    exact Arith.tame_add (Arith.tame_mul (Arith.tame_mul G.den_tame (Arith.tame_pow hc hq hX G.radius_small)) (F.num_tame _ hctx))
      (Arith.tame_mul (Arith.tame_mul F.den_tame (Arith.tame_pow hc hq hX F.radius_small)) (G.num_tame _ hctx))
}

def Evaluated.mul {f g : (I → ℤ) → Expr d}
    (F : Evaluated I d Valid f) (G : Evaluated I d Valid g) :
    Evaluated I d Valid (fun ι => (f ι).mul (g ι)) := {
  den := Arith.mul F.den G.den
  height := Arith.mul F.height G.height
  radius := Arith.add F.radius G.radius
  num := fun ctx => Arith.mul (F.num ctx) (G.num ctx)
  wellFormed := fun ι hι => ⟨F.wellFormed ι hι, G.wellFormed ι hι⟩
  den_run := by
    intro ι hι
    simp only [Arith.run_mul, F.den_run ι hι, G.den_run ι hι, evalBounds, Nat.cast_mul]
  height_run := by
    intro ι hι
    simp only [Arith.run_mul, F.height_run ι hι, G.height_run ι hι, evalBounds, Nat.cast_mul]
  radius_run := by
    intro ι hι
    simp only [Arith.run_add, F.radius_run ι hι, G.radius_run ι hι, evalBounds, Nat.cast_add]
  num_run := by
    intro ι hι ctx x hctx hx
    simp only [Arith.run_mul, F.num_run ι hι ctx x hctx hx, G.num_run ι hι ctx x hctx hx, clearedNum]
  den_tame := Arith.tame_mul F.den_tame G.den_tame
  height_tame := Arith.tame_mul F.height_tame G.height_tame
  radius_small := Arith.small_add F.radius_small G.radius_small
  num_tame := fun ctx hctx => Arith.tame_mul (F.num_tame ctx hctx) (G.num_tame ctx hctx)
}

def Evaluated.pow (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) {f : (I → ℤ) → Expr d}
    (F : Evaluated I d Valid f) (n : Term I) (hn : SmallTerm n)
    (nonneg : ∀ ι, Valid ι → 0 ≤ n.run ι) :
    Evaluated I d Valid (fun ι => (f ι).pow (n.run ι).toNat) := {
  den := Arith.pow hc hq F.den n
  height := Arith.pow hc hq F.height n
  radius := Arith.mul n F.radius
  num := fun ctx => Arith.pow hc hq (F.num ctx) n
  wellFormed := F.wellFormed
  den_run := by
    intro ι hι
    simp only [Arith.run_pow, F.den_run ι hι, evalBounds, Nat.cast_pow]
  height_run := by
    intro ι hι
    simp only [Arith.run_pow, F.height_run ι hι, evalBounds, Nat.cast_pow]
  radius_run := by
    intro ι hι
    simp only [Arith.run_mul, F.radius_run ι hι, evalBounds, Nat.cast_mul, Int.toNat_of_nonneg (nonneg ι hι)]
  num_run := by
    intro ι hι ctx x hctx hx
    simp only [Arith.run_pow, F.num_run ι hι ctx x hctx hx, clearedNum]
  den_tame := Arith.tame_pow hc hq F.den_tame hn
  height_tame := Arith.tame_pow hc hq F.height_tame hn
  radius_small := Arith.small_mul hn F.radius_small
  num_tame := fun ctx hctx => Arith.tame_pow hc hq (F.num_tame ctx hctx) hn
}

namespace Arith

/-- The absolute value expressed using total positive division. -/
def absolute (v : Term I) : Term I :=
  mul v (sub (mul (.literal 2) (div v v)) (.literal 1))

@[simp] theorem run_absolute (v : Term I) (ι : I → ℤ) :
    (absolute v).run ι = ((v.run ι).natAbs : ℤ) := by
  simp only [absolute,run_mul,run_sub,run_div,run_lit,positiveDiv]
  split
  next h => simp [Int.ediv_self (by omega : v.run ι ≠ 0),Int.natAbs_of_nonneg h.le]
  next h => simp [Int.ofNat_natAbs_of_nonpos (by omega : v.run ι ≤ 0)]

theorem tame_absolute {v : Term I} (hv : TameTerm v) : TameTerm (absolute v) :=
  tame_mul hv (tame_sub (tame_mul (.small (.literal 2)) (tame_div hv hv)) (.small (.literal 1)))

def nearest (v d : Term I) : Term I :=
  div (add (mul (.literal 2) v) d) (mul (.literal 2) d)

@[simp] theorem run_nearest (v d : Term I) (ι : I → ℤ) (hd : 0 < d.run ι) :
    (nearest v d).run ι = Extraction.nearest (v.run ι) (d.run ι) := by
  simp [nearest,positiveDiv,Extraction.nearest,show 0 < 2*d.run ι by omega]

theorem tame_nearest {v d : Term I} (hv : TameTerm v) (hd : TameTerm d) : TameTerm (nearest v d) :=
  tame_div (tame_add (tame_mul (.small (.literal 2)) hv) hd) (tame_mul (.small (.literal 2)) hd)

def centered (v z : Term I) : Term I := sub v (mul z (nearest v z))

@[simp] theorem run_centered (v z : Term I) (ι : I → ℤ) (hz : 0 < z.run ι) :
    (centered v z).run ι = Extraction.centered (v.run ι) (z.run ι) := by
  simp [centered,Extraction.centered,hz]

theorem tame_centered {v z : Term I} (hv : TameTerm v) (hz : TameTerm z) : TameTerm (centered v z) :=
  tame_sub hv (tame_mul hz (tame_nearest hv hz))

/-- The signed radix used to recover the binomial tail with one pair of rounded divisions. -/
def tailRadix (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (a b n : Term I) : Term I :=
  add (mul (.literal 8) (pow hc hq (add (add (.literal 2) (absolute a)) (absolute b)) n)) (.literal 3)

@[simp] theorem run_tailRadix (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (a b n : Term I) (ι : I → ℤ) :
    (tailRadix hc hq a b n).run ι =
      8 * (((2+(a.run ι).natAbs+(b.run ι).natAbs)^(n.run ι).toNat : ℕ) : ℤ) + 3 := by
  simp [tailRadix]

theorem tame_tailRadix (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) {a b n : Term I}
    (ha : TameTerm a) (hb : TameTerm b) (hn : SmallTerm n) : TameTerm (tailRadix hc hq a b n) :=
  tame_add (tame_mul (.small (.literal 8))
    (tame_pow hc hq (tame_add (tame_add (.small (.literal 2)) (tame_absolute ha)) (tame_absolute hb)) hn))
    (.small (.literal 3))

def tailNumerator (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (a b n k : Term I) : Term I :=
  let z := tailRadix hc hq a b n
  centered (nearest (pow hc hq (add b (mul a z)) n) (pow hc hq z k)) (sub z (.literal 1))

@[simp] theorem run_tailNumerator (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (a b n k : Term I) (ι : I → ℤ) :
    (tailNumerator hc hq a b n k).run ι =
      TailRadix.tailNumerator (a.run ι) (b.run ι) (n.run ι).toNat (k.run ι).toNat := by
  have hz : 1 < (tailRadix hc hq a b n).run ι := by
    rw [run_tailRadix]
    have hn := Int.natCast_nonneg ((2+(a.run ι).natAbs+(b.run ι).natAbs)^(n.run ι).toNat)
    omega
  have hm : 0 < (sub (tailRadix hc hq a b n) (.literal 1)).run ι := by simp only [run_sub, run_lit]; omega
  have hpow : 0 < (pow hc hq (tailRadix hc hq a b n) k).run ι := by
    rw [run_pow]
    exact pow_pos (by omega) _
  rw [tailNumerator,run_centered _ _ _ hm,run_nearest _ _ _ hpow]
  simp [TailRadix.tailNumerator]

theorem tame_tailNumerator (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) {a b n k : Term I}
    (ha : TameTerm a) (hb : TameTerm b) (hn : SmallTerm n) (hk : SmallTerm k) :
    TameTerm (tailNumerator hc hq a b n k) := by
  have hz := tame_tailRadix hc hq ha hb hn
  exact tame_centered (tame_nearest (tame_pow hc hq (tame_add hb (tame_mul ha hz)) hn)
    (tame_pow hc hq hz hk)) (tame_sub hz (.small (.literal 1)))

end Arith

def Evaluated.threshold (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {f : (I → ℤ) → Expr d} (F : Evaluated I d Valid f) (n k : Term I)
    (hn : SmallTerm n) (hk : SmallTerm k)
    (range : ∀ ι, Valid ι → 0 ≤ n.run ι ∧ 0 ≤ k.run ι ∧ k.run ι ≤ n.run ι + 1) :
    Evaluated I d Valid (fun ι => (f ι).threshold (n.run ι).toNat (k.run ι).toNat) := by
  let scale := fun ctx : Fin d → Term I => Arith.mul (Arith.pow hc hq (Arith.prod ctx) F.radius) F.den
  refine ⟨Arith.pow hc hq (Arith.mul (.literal 2) F.den) n,
    Arith.pow hc hq (Arith.mul (.literal 2) (Arith.add F.den F.height)) n,
    Arith.mul n F.radius,
    fun ctx => Arith.tailNumerator hc hq (Arith.add (scale ctx) (F.num ctx))
      (Arith.sub (scale ctx) (F.num ctx)) n k, ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro ι hi
    obtain ⟨h1,h2,h3⟩ := range ι hi
    exact ⟨by omega,F.wellFormed ι hi⟩
  · intro ι hi
    simp [evalBounds,F.den_run ι hi]
  · intro ι hi
    simp [evalBounds,F.den_run ι hi,F.height_run ι hi]
  · intro ι hi
    have hnon := (range ι hi).1
    simp [evalBounds,F.radius_run ι hi, Int.toNat_of_nonneg hnon]
  · intro ι hi ctx x hx hpos
    simp [scale,clearedNum,F.radius_run ι hi,F.den_run ι hi,F.num_run ι hi ctx x hx hpos,hx]
  · exact Arith.tame_pow hc hq (Arith.tame_mul (.small (.literal 2)) F.den_tame) hn
  · exact Arith.tame_pow hc hq (Arith.tame_mul (.small (.literal 2)) (Arith.tame_add F.den_tame F.height_tame)) hn
  · exact Arith.small_mul hn F.radius_small
  · intro ctx hctx
    have hs : TameTerm (scale ctx) :=
      Arith.tame_mul (Arith.tame_pow hc hq (Arith.tame_prod hctx) F.radius_small) F.den_tame
    exact Arith.tame_tailNumerator hc hq (Arith.tame_add hs (F.num_tame ctx hctx))
      (Arith.tame_sub hs (F.num_tame ctx hctx)) hn hk

namespace ProjectionTerms

open Arith
variable {I : Type}

private abbrev lit (n : ℤ) : Term I := Term.literal n

/-- The signed term computes the least positive multiple of the period above the radius.
The self-division supplies the adjustment at radius zero. -/
def shift (g m : Term I) : Term I :=
  mul m (add (div (sub g (div g g)) m) (lit 1))

theorem shift_small {g m : Term I} (hg : SmallTerm g) (hm : SmallTerm m) : SmallTerm (shift g m) :=
  small_mul hm (small_add (small_div (small_sub hg (small_div hg hg)) hm) (.literal 1))

theorem shift_run (g m : Term I) (ι : I → ℤ) (G M : ℕ)
    (hg : g.run ι = (G : ℤ)) (hm : m.run ι = (M : ℤ)) (hM : 0 < M) :
    (shift g m).run ι = (shiftBound G M : ℤ) := by
  cases G with
  | zero => simp [shift, hg, hm, shiftBound, positiveDiv, lit]
  | succ n =>
    have hn : (n:ℤ)+1 ≠ 0 := by omega
    simp [shift, hg, hm, shiftBound, positiveDiv, hM, lit, Int.ediv_self hn]

/-- The radix after specializing all coordinates to positive integers. -/
def radix {d : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (ctx : Fin d → Term I) (h g b : Term I) : Term I :=
  let mass := mul h (prod (fun i => pow hc hq (ctx i) (mul (lit 2) g)))
  add (mul (lit 4) (mul mass (add (mul (lit 2) b) (lit 1)))) (lit 5)

theorem radix_tame {d : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {ctx : Fin d → Term I} {h g b : Term I} (hx : ∀ i, TameTerm (ctx i))
    (hh : TameTerm h) (hg : SmallTerm g) (hb : SmallTerm b) :
    TameTerm (radix hc hq ctx h g b) := by
  apply tame_add _ (.small (.literal 5))
  apply tame_mul (.small (.literal 4))
  apply tame_mul
  · exact tame_mul hh (tame_prod (fun i => tame_pow hc hq (hx i) (small_mul (.literal 2) hg)))
  · exact .small (small_add (small_mul (.literal 2) hb) (.literal 1))

theorem radix_run {d : ℕ} (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (ctx : Fin d → Term I) (h g b : Term I) (ι : I → ℤ) (x : Fin d → ℕ) (H G B : ℕ)
    (hx : ∀ i, (ctx i).run ι = (x i : ℤ)) (hp : ∀ i, 0 < x i)
    (hh : h.run ι = H) (hg : g.run ι = G) (hb : b.run ι = B) :
    (radix hc hq ctx h g b).run ι = (RadixGrowth.radix x (fun _ => 1) H G B : ℤ) := by
  have ep : ((2:ℤ)*G).toNat = 2*G := by omega
  have hmax (i : Fin d) : max (x i : ℤ) 1 = x i := max_eq_left (by exact_mod_cast hp i : 1 ≤ (x i:ℤ))
  simp [radix, hx, hh, hg, hb, lit, ep, RadixGrowth.radix, RadixGrowth.specializedHeight, hmax]

private def near (v q : Term I) := div (add (mul (lit 2) v) q) (mul (lit 2) q)

private theorem near_tame {v q : Term I} (hv : TameTerm v) (hq : TameTerm q) : TameTerm (near v q) :=
  tame_div (tame_add (tame_mul (.small (.literal 2)) hv) hq) (tame_mul (.small (.literal 2)) hq)

private theorem near_run (v q : Term I) (ι : I → ℤ) (hq : 0 < q.run ι) :
    (near v q).run ι = Extraction.nearest (v.run ι) (q.run ι) := by
  simp [near, Extraction.nearest, positiveDiv, show 0 < 2*q.run ι by omega, lit, Term.run]

private def extract (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (v z k : Term I) :=
  let n := near v (pow hc hq z k)
  sub n (mul z (near n z))

private theorem extract_tame (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) {v z k : Term I}
    (hv : TameTerm v) (hz : TameTerm z) (hk : SmallTerm k) : TameTerm (extract hc hq v z k) := by
  have h := near_tame hv (tame_pow hc hq hz hk)
  exact tame_sub h (tame_mul hz (near_tame h hz))

private theorem extract_run (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (v z k : Term I)
    (ι : I → ℤ) (hz : 0 < z.run ι) : (extract hc hq v z k).run ι =
      Extraction.extractCoefficient (v.run ι) (z.run ι) (k.run ι).toNat := by
  have hp : 0 < (pow hc hq z k).run ι := by rw [run_pow]; positivity
  simp [extract, near_run _ _ _ hp, near_run _ _ _ hz, Extraction.extractCoefficient, Extraction.centered]

/-- Finish extracting the projected coefficient after a single child call at the new radix. -/
def finish (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic) (coord g b m z child : Term I) : Term I :=
  let v := mul (mul (pow hc hq coord g) (pow hc hq z (sub b g))) child
  let twice := mul (lit 2) b
  let exp := mul m (add (div twice m) (lit 1))
  let kernel := div (sub (pow hc hq z exp) (lit 1)) (sub (pow hc hq z m) (lit 1))
  extract hc hq (mul v kernel) z twice

theorem finish_tame (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {coord g b m z child : Term I} (hx : TameTerm coord) (hg : SmallTerm g) (hb : SmallTerm b)
    (hm : SmallTerm m) (hz : TameTerm z) (hchild : TameTerm child) :
    TameTerm (finish hc hq coord g b m z child) := by
  have h2 := small_mul (.literal 2) hb
  have he := small_mul hm (small_add (small_div h2 hm) (.literal 1))
  have hv := tame_mul (tame_mul (tame_pow hc hq hx hg) (tame_pow hc hq hz (small_sub hb hg))) hchild
  have hk := tame_div (tame_sub (tame_pow hc hq hz he) (.small (.literal 1)))
    (tame_sub (tame_pow hc hq hz hm) (.small (.literal 1)))
  exact extract_tame hc hq (tame_mul hv hk) hz h2

theorem finish_run (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    (coord g b m z child : Term I) (ι : I → ℤ) (G B M Z : ℕ)
    (hg : g.run ι = G) (hb : b.run ι = B) (hm : m.run ι = M) (hz : z.run ι = Z)
    (hGB : G ≤ B) (hM : 0 < M) (hZ : 1 < Z) :
    (finish hc hq coord g b m z child).run ι =
      Extraction.extractCoefficient ((coord.run ι^G*(Z:ℤ)^(B-G)*child.run ι)*
        (((Z:ℤ)^(M*(2*B/M+1))-1)/((Z:ℤ)^M-1))) Z (2*B) := by
  have hzi : 1 < (Z : ℤ) := by exact_mod_cast hZ
  have hd : 1 < (Z:ℤ)^M := one_lt_pow₀ hzi hM.ne'
  have ep : ((M:ℤ)*((2*(B:ℤ))/M+1)).toNat = M*(2*B/M+1) := by
    have eq : (M:ℤ)*((2*(B:ℤ))/M+1) = ((M*(2*B/M+1):ℕ):ℤ) := by push_cast; rfl
    exact (congrArg Int.toNat eq).trans (Int.toNat_natCast _)
  have subexp : ((B:ℤ)-G).toNat = B-G := by omega
  have twice : ((2:ℤ)*B).toNat = 2*B := by omega
  simp [finish, extract_run _ _ _ _ _ _ (by omega : 0 < z.run ι), hg, hb, hm, hz, lit,
    Term.run, positiveDiv, hM, hd, ep, subexp, twice]

end ProjectionTerms
def Evaluated.project (hc : PowerTests.Cyclic) (hq : PowerTests.Quadratic)
    {f : (I → ℤ) → Expr d} (F : Evaluated I d Valid f) (j : Fin d) (m : Term I)
    (hm : SmallTerm m) (pos : ∀ ι, Valid ι → 0 < m.run ι) :
    Evaluated I d Valid (fun ι => (f ι).project j (Nat.toPNat' (m.run ι).toNat)) := by
  let b := ProjectionTerms.shift F.radius m
  let z (ctx : Fin d → Term I) := ProjectionTerms.radix hc hq ctx F.height F.radius b
  let child (ctx : Fin d → Term I) := F.num (Function.update ctx j (z ctx))
  refine { den := F.den, height := F.height, radius := F.radius,
           num := fun ctx => ProjectionTerms.finish hc hq (ctx j) F.radius b m (z ctx) (child ctx),
           wellFormed := F.wellFormed, den_run := F.den_run, height_run := F.height_run,
           radius_run := F.radius_run, den_tame := F.den_tame, height_tame := F.height_tame,
           radius_small := F.radius_small, num_run := ?_, num_tame := ?_ }
  · intro ι hv ctx x hx hp
    let M := (m.run ι).toNat
    let G := (evalBounds (f ι)).radius
    let H := (evalBounds (f ι)).height
    let B := shiftBound G M
    let Z := RadixGrowth.radix x (fun _ => 1) H G B
    have hM : 0 < M := by dsimp [M]; have := pos ι hv; omega
    have hm' : m.run ι = (M:ℤ) := (Int.toNat_of_nonneg (pos ι hv).le).symm
    have hb : b.run ι = B := ProjectionTerms.shift_run _ _ _ _ _ (F.radius_run ι hv) hm' hM
    have hz : (z ctx).run ι = Z := ProjectionTerms.radix_run hc hq _ _ _ _ _ _ _ _ _ hx hp
      (F.height_run ι hv) (F.radius_run ι hv) hb
    have hZ : 1 < Z := by dsimp [Z,RadixGrowth.radix]; omega
    have hu (i : Fin d) : ((Function.update ctx j (z ctx)) i).run ι = ((Function.update x j Z i : ℕ):ℤ) := by
      by_cases eq : i = j
      · subst i; simpa using hz
      · simpa only [Function.update_of_ne eq] using hx i
    have hpos (i : Fin d) : 0 < Function.update x j Z i := by
      by_cases eq : i = j
      · subst i; simpa using (show 0 < Z by omega)
      · simpa only [Function.update_of_ne eq] using hp i
    have hchild := F.num_run ι hv _ _ hu hpos
    have hc' : (child ctx).run ι = clearedNum (f ι) (Function.update x j Z) := hchild
    rw [ProjectionTerms.finish_run hc hq _ _ _ _ _ _ _ G B M Z (F.radius_run ι hv) hb hm' hz
      (shift_properties G hM).1 hM hZ, hc', hx j]
    have hco : ((m.run ι).toNat.toPNat' : ℕ) = M := PNat.toPNat'_coe hM
    simp only [clearedNum, hco]
    rfl
  · intro ctx hctx
    have hb := ProjectionTerms.shift_small F.radius_small hm
    have hz := ProjectionTerms.radix_tame hc hq hctx F.height_tame F.radius_small hb
    have hchild : TameTerm (child ctx) := F.num_tame _ (fun i => by
      by_cases eq : i = j
      · subst i; simpa using hz
      · simpa only [Function.update_of_ne eq] using hctx i)
    exact ProjectionTerms.finish_tame hc hq (hctx j) F.radius_small hb hm hz hchild

/-- Evaluate at the point `(1, …, 1)`. -/
theorem Evaluated.programs {k d : ℕ} {Valid : ((Option (Fin k)) → ℤ) → Prop}
    {e : ((Option (Fin k)) → ℤ) → Expr d} (E : Evaluated (Option (Fin k)) d Valid e) :
    ∃ num den : Packing.IntegerTerm k, TameTerm num ∧ TameTerm den ∧
      ∀ ι, Valid ι → 0 < den.run ι ∧
        ((num.run ι : ℤ) : ℚ) / ((den.run ι : ℤ) : ℚ) = scalarAtOne (e ι) := by
  let ones : Fin d → Packing.IntegerTerm k := fun _ => .literal 1
  refine ⟨E.num ones, E.den, E.num_tame ones (fun _ => .small (.literal 1)), E.den_tame, ?_⟩
  intro ι hι
  rw [E.den_run ι hι, evalBounds_denominator]
  constructor
  · exact_mod_cast (e ι).denominator_pos
  · rw [E.num_run ι hι ones (fun _ => 1) (fun _ => rfl) (fun _ => Nat.one_pos),
      scalarAtOne_eq_clearedNum _ (E.wellFormed ι hι)]
    norm_cast

/-- The inputs that `PackedScalarPrograms` quantifies over. -/
def ValidInput (k : ℕ) (ι : Option (Fin k) → ℤ) : Prop :=
  ∃ (U : ℕ) (t : Fin k → Fin U), 0 < U ∧ ι = Packing.termInputs t

end
end DiophantineNP.Blueprint
