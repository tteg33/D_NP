import DiophantineNP.FormulaOutput
import DiophantineNP.FormulaLeafGrowth

/-! # Fixed formula trees have polynomial bit budgets

Index positive universe sizes by u+1 so arbitrary tuples of numerical
parameters exist at every input index, including u=0. The exponent below
is uniform over the choice of numerical parameters. -/
namespace DiophantineNP.FormulaLaurent
open Counting ConcreteGrid LaurentBounds
noncomputable section

private theorem poly_shift {f : ℕ → ℕ} (hf : Poly f) : Poly (fun u => f (u+1)) := by
  obtain ⟨c,h⟩ := hf
  refine ⟨2*c, fun u => (h (u+1)).trans ?_⟩
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by nlinarith [Nat.zero_le (u^2)]) _

private theorem bits_shift {f : ℕ → ℕ} (hf : PolyBits f) : PolyBits (fun u => f (u+1)) := by
  obtain ⟨e,h,he⟩ := hf
  exact ⟨fun u => e (u+1), poly_shift h, fun u => he (u+1)⟩

theorem shifted {d : ℕ} {f : ℕ → Expr d} (h : Admissible f) :
    Admissible (fun u => f (u+1)) := by
  induction h with
  | scalar p q hp hq => exact .scalar _ _ (bits_shift hp) (bits_shift hq)
  | monomial v hv => exact .monomial _ (poly_shift hv)
  | geometric j s J hs hJ => exact .geometric _ _ _ (poly_shift hs) (poly_shift hJ)
  | add _ _ f g => exact .add f g
  | neg _ f => exact .neg f
  | mul _ _ f g => exact .mul f g
  | pow _ n hn f => exact .pow f _ (poly_shift hn)
  | threshold _ n k hn f => exact .threshold f _ _ (poly_shift hn)
  | project _ j m f => exact .project f _ _

private theorem poly_precision : Poly precision := by
  let l := (polyToBits polySize).log2.add (poly_const 1)
  let j := ((poly_const 2).mul polyRadius).add (poly_const 1)
  exact (poly_const 100).mul ((j.add ((poly_const 10).mul l)).add (poly_const 20))

private theorem poly_halfDegree : Poly halfDegree :=
  ((poly_const (2^15)).mul (polyFixedPow polySize 8)).mul
    ((poly_precision.add ((poly_const 20).mul ((polyToBits polySize).log2.add (poly_const 1)))).add (poly_const 100))

theorem adm_const {d : ℕ} (q : ℚ) : Admissible (fun _ : ℕ => (const q : Expr d)) :=
  (RatBits.const q).admissible

theorem adm_sub {d : ℕ} {f g : ℕ → Expr d} (hf : Admissible f) (hg : Admissible g) :
    Admissible (fun u => sub (f u) (g u)) := .add hf (.neg hg)

theorem adm_tail {d : ℕ} {f : ℕ → Expr d} (hf : Admissible f) :
    Admissible (fun u => tail (u+1) (f u)) :=
  .threshold hf _ _ (poly_shift (((poly_const 2).mul poly_halfDegree).add (poly_const 1)))

private theorem adm_and {d : ℕ} {f g : ℕ → Expr d} (hf : Admissible f) (hg : Admissible g) :
    Admissible (fun u => andExpr (u+1) (f u) (g u)) :=
  adm_tail (.mul (adm_sub (.add hf hg) (adm_const _)) (adm_const _))

private theorem adm_or {d : ℕ} {f g : ℕ → Expr d} (hf : Admissible f) (hg : Admissible g) :
    Admissible (fun u => orExpr (u+1) (f u) (g u)) :=
  adm_tail (.mul (adm_sub (.add hf hg) (adm_const _)) (adm_const _))

theorem adm_normalize {d : ℕ} {f : ℕ → Expr d} (hf : Admissible f) :
    Admissible (fun u => normalize (u+1) (f u)) := by
  apply Admissible.mul hf
  exact shifted (((RatBits.const 1).div ((RatBits.const 8).mul
    ((RatBits.natCast (polyToBits polySize)).pow (poly_const 4)))).admissible)

private theorem adm_guard {d : ℕ} {f : ℕ → Expr d} (hf : Admissible f) :
    Admissible (fun u => guardExpr (u+1) (f u)) :=
  adm_tail (adm_normalize (.add (adm_sub (adm_sub (shifted (RatBits.natCast (polyToBits polyId)).admissible)
    (adm_const _)) hf) (adm_const _)))

private theorem adm_atom {d k : ℕ} (a : Atom k) {f : ℕ → Fin k → Expr d}
    (hf : ∀ i, Admissible (fun u => f u i)) :
    Admissible (fun u => atomExpr (u+1) a (f u)) := by
  have hr : Admissible (fun u => residual a (f u)) := by
    cases a with
    | eqv i j => exact adm_sub (hf i) (hf j)
    | leq i j => exact adm_sub (hf j) (hf i)
    | add i j m => exact adm_sub (.add (hf i) (hf j)) (hf m)
    | mul i j m => exact adm_sub (.mul (hf i) (hf j)) (hf m)
  unfold atomExpr
  apply adm_tail
  apply adm_normalize
  cases h : a.isOrder <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact adm_sub (adm_const _) (.pow hr _ (poly_const 2))
  · exact .add hr (adm_const _)

private theorem adm_quant {d : ℕ} {f : ℕ → Expr d} (j : Fin d) {k : ℕ → ℕ}
    (hf : Admissible f) (hk : Poly k) :
    Admissible (fun u => quantExpr (concreteBackend (u+1) d) j (k u) (f u)) := by
  apply adm_tail
  apply Admissible.mul
  · apply adm_sub _ (adm_const _)
    apply adm_sub _ ((RatBits.natCast (polyToBits hk)).admissible)
    apply Admissible.mul
    · exact shifted (((RatBits.natCast (polyToBits polySize)).div (RatBits.const 2)).admissible)
    · apply Admissible.project
      exact .mul (adm_tail (shifted (yLeaf_admissible j))) (adm_and hf (adm_guard (shifted (xLeaf_admissible j))))
  · exact shifted (((RatBits.const 1).div (((RatBits.natCast (polyToBits polySize)).add
      (RatBits.natCast (polyToBits polyId))).add (RatBits.const 2))).admissible)

/-- Structural proof of fixed arity and admissible numerical data. The address
of each bound slot depends on the syntax alone. -/
private theorem compile_admissible {d k : ℕ} (φ : Formula k) :
    ∀ (r : (u : ℕ) → Fin k → Address (u+1) d) (s : ℕ) (hs : s + depth φ ≤ d),
    (∀ i, Admissible (fun u => addressExpr (concreteBackend (u+1) d) (r u i))) →
    Admissible (fun u => compile (concreteBackend (u+1) d) φ (r u) s hs) := by
  induction φ with
  | atom a =>
    intro r s hs hr
    exact adm_atom a hr
  | neg φ ih =>
    intro r s hs hr
    exact adm_sub (adm_const 1) (ih r s hs hr)
  | conj φ ψ ih jh =>
    intro r s hs hr
    exact adm_and (ih r s _ hr) (jh r s _ hr)
  | disj φ ψ ih jh =>
    intro r s hs hr
    exact adm_or (ih r s _ hr) (jh r s _ hr)
  | ex φ ih =>
    intro r s hs hr
    let j : Fin d := ⟨s, by simp only [depth] at hs; omega⟩
    apply adm_quant j _ (poly_const 0)
    apply ih
    exact Fin.cases (shifted (xLeaf_admissible j)) hr
  | maj φ ih =>
    intro r s hs hr
    let j : Fin d := ⟨s, by simp only [depth] at hs; omega⟩
    apply adm_quant j _ ((poly_shift polyId).mono (fun u => Nat.div_le_self (u+1) 2))
    apply ih
    exact Fin.cases (shifted (xLeaf_admissible j)) hr

theorem truthExpr_admissible {k : ℕ} (φ : Formula (k+1)) (t : ∀ u, Fin k → Fin (u+1)) :
    Admissible (fun u => truthExpr φ (t u)) := by
  apply adm_and _ (adm_guard (shifted (xLeaf_admissible _)))
  apply compile_admissible
  refine Fin.cases (shifted (xLeaf_admissible _)) ?_
  intro i
  exact (RatBits.natCast (polyToBits ((poly_shift polyId).mono
    (fun u => (t u i).isLt.le)))).admissible

/-- Taking the worst legal parameter tuple per universe upgrades a bound along
every parameter family to one exponent uniform over all tuples. -/
theorem uniform_bound {k : ℕ} (cost : (u : ℕ) → (Fin k → Fin (u+1)) → ℕ)
    (bounded : ∀ t : (u : ℕ) → Fin k → Fin (u+1), Poly (fun u => cost u (t u))) :
    ∃ c : ℕ, ∀ u t, cost u t ≤ (u+2)^c := by
  classical
  have best (u : ℕ) : ∃ t, ∀ v, cost u v ≤ cost u t := by
    obtain ⟨t,_,h⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k → Fin (u+1)))
      (cost u) Finset.univ_nonempty
    exact ⟨t, fun v => h v (Finset.mem_univ _)⟩
  choose t ht using best
  obtain ⟨c,hc⟩ := bounded t
  exact ⟨c, fun u v => (ht u v).trans (hc u)⟩

/-- One exponent works for all positive universe sizes and every legal
parameter tuple. The maximum is used only in the proof of the bound. -/
theorem truthExpr_uniform_size {k : ℕ} (φ : Formula (k+1)) :
    ∃ c : ℕ, ∀ (U : ℕ), 0 < U → ∀ t : Fin k → Fin U,
      let b := (truthExpr φ t).bounds
      b.radius + (b.denominator.log2+1) + (b.height.log2+1) ≤ (U+1)^c := by
  let cost (u : ℕ) (t : Fin k → Fin (u+1)) :=
    let b := (truthExpr φ t).bounds
    b.radius + (b.denominator.log2+1) + (b.height.log2+1)
  obtain ⟨c,hc⟩ := uniform_bound cost (fun t => (truthExpr_admissible φ t).total_size)
  refine ⟨c, ?_⟩
  rintro (_ | u) h v
  · omega
  · exact hc u v

end
end DiophantineNP.FormulaLaurent
