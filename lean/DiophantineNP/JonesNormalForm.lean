import DiophantineNP.JonesInterface
import DiophantineNP.NaturalBridge
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Compiling the numerical normal form (53) to one bounded equation

All length comparisons occur inside the polynomial. This is necessary because
bounded Diophantine membership permits larger spurious roots.
-/
namespace DiophantineNP.Classes.Jones
open MvPolynomial
open scoped BigOperators
noncomputable section

private def inputs {T : Type} (x : ℕ) (w : T → ℕ) : Option T → ℤ
  | none => x
  | some i => w i

private theorem eqEval {A : Type} (h : A → ℤ) (p : MvPolynomial A ℤ) : aeval h p = eval h p := by
  exact DFunLike.congr_fun (coe_aeval_eq_eval h) p

/-- Any integer polynomial admits a nonnegative-coefficient polynomial
majorant in the magnitudes of its inputs. -/
private theorem majorant (P : Polynomial ℤ) :
    ∃ p : Polynomial ℕ, ∀ n N : ℕ, n ≤ N → (P.eval (n:ℤ)).natAbs ≤ p.eval N := by
  induction P using Polynomial.induction_on' with
  | monomial k a =>
    exact ⟨Polynomial.monomial k a.natAbs, fun n N hn => by
      simpa [Int.natAbs_mul,Int.natAbs_pow] using Nat.mul_le_mul_left a.natAbs (Nat.pow_le_pow_left hn k)⟩
  | add P Q ihP ihQ =>
    obtain ⟨p,hp⟩ := ihP
    obtain ⟨q,hq⟩ := ihQ
    exact ⟨p+q, fun n N hn => by
      rw [Polynomial.eval_add, Polynomial.eval_add]
      exact (Int.natAbs_add_le ..).trans (Nat.add_le_add (hp _ _ hn) (hq _ _ hn))⟩

private theorem size_le_bits (n : ℕ) : n.size ≤ bits n :=
  Nat.size_le.mpr Nat.lt_log2_self

private theorem bits_le_size_succ (n : ℕ) : bits n ≤ n.size+1 := by
  by_cases hz : n=0
  · subst n; simp [bits]
  · have h := Nat.lt_size.mpr (Nat.log2_self_le hz)
    unfold bits; omega

private theorem bits_le_succ (n : ℕ) : bits n ≤ n+1 := by
  unfold bits
  have := Nat.log2_le_self n
  omega

private theorem component_cost {T : Type} [Fintype T] (w : T → ℕ) (i : T) : bits (w i) ≤ natCost w :=
  Finset.single_le_sum (f := fun j => bits (w j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Original witness fields, certified lengths of all fields including the input,
comparison slacks, length certificates, and the native inclusion certificate. -/
private abbrev Fields (n l : ℕ) (B : Type) :=
  Fin n ⊕ (Option (Fin n) ⊕ (Fin n ⊕ ((Option (Fin n) × Fin l) ⊕ B)))

namespace Fields
variable {n l : ℕ} {B : Type}
private def word (i : Fin n) : Fields n l B := .inl i
private def len (u : Option (Fin n)) : Fields n l B := .inr (.inl u)
private def slack (i : Fin n) : Fields n l B := .inr (.inr (.inl i))
private def aux (u : Option (Fin n)) (j : Fin l) : Fields n l B := .inr (.inr (.inr (.inl (u,j))))
private def bitAux (j : B) : Fields n l B := .inr (.inr (.inr (.inr j)))
private def make (w : Fin n → ℕ) (v : Option (Fin n) → ℕ) (s : Fin n → ℕ)
    (a : Option (Fin n) → Fin l → ℕ) (b : B → ℕ) : Fields n l B → ℕ :=
  Sum.elim w (Sum.elim v (Sum.elim s (Sum.elim (fun u => a u.1 u.2) b)))
end Fields

private def inputField {n : ℕ} (x : ℕ) (w : Fin n → ℕ) : Option (Fin n) → ℕ
  | none => x
  | some i => w i

private def invar {n l : ℕ} {B : Type} : Option (Fin n) → Option (Fields n l B) := Option.map Fields.word

private def lengthPoly {n l : ℕ} {B : Type} (T : Equation (Fin l)) (u : Option (Fin n)) :
    MvPolynomial (Option (Fields n l B)) ℤ :=
  rename (Sum.elim (fun b : Bool => if b then some (Fields.len u) else invar u)
    (fun j => some (Fields.aux u j))) T

private def bitPoly {n l : ℕ} {B : Type} (T : Equation B) (i j : Fin n) :
    MvPolynomial (Option (Fields n l B)) ℤ :=
  rename (Sum.elim (fun b : Bool => some (Fields.word (if b then j else i)))
    (fun k => some (Fields.bitAux k))) T

private def liftBound {σ : Type} (P : Polynomial ℤ) (v : σ) : MvPolynomial σ ℤ :=
  P.eval₂ C (X v)

private theorem liftBound_eval {σ : Type} (P : Polynomial ℤ) (v : σ) (y : σ → ℤ) :
    eval y (liftBound P v) = P.eval (y v) := by
  induction P using Polynomial.induction_on' with
  | monomial k a => simp [liftBound]
  | add P Q hp hq => simpa [liftBound,Polynomial.eval₂_add] using congrArg₂ (·+·) hp hq

private def boundPoly {n l : ℕ} {B : Type} (P : Polynomial ℤ) (i : Fin n) :
    MvPolynomial (Option (Fields n l B)) ℤ :=
  liftBound P (some (Fields.len none)) - X (some (Fields.len (some i))) - X (some (Fields.slack i))

private abbrev Tests (n : ℕ) := Unit ⊕ (Unit ⊕ (Option (Fin n) ⊕ Fin n))

private def equations {r l : ℕ} {B : Type} (P : Polynomial ℤ)
    (Q : MvPolynomial (Option (Fin (r+2))) ℤ) (T : Equation (Fin l)) (V : Equation B) :
    Tests (r+2) → MvPolynomial (Option (Fields (r+2) l B)) ℤ :=
  Sum.elim (fun _ => rename invar Q) (Sum.elim (fun _ => bitPoly V 0 1)
    (Sum.elim (lengthPoly T) (boundPoly P)))

private def combined {r l : ℕ} {B : Type} (P : Polynomial ℤ)
    (Q : MvPolynomial (Option (Fin (r+2))) ℤ) (T : Equation (Fin l)) (V : Equation B) :=
  ∑ k, (equations P Q T V k)^2

private theorem combined_zero {r l : ℕ} {B : Type} (P : Polynomial ℤ)
    (Q : MvPolynomial (Option (Fin (r+2))) ℤ) (T : Equation (Fin l)) (V : Equation B)
    (x : ℕ) (a : Fields (r+2) l B → ℕ) :
    eval (inputs x a) (combined P Q T V) = 0 ↔
      polyValue Q x (a ∘ Fields.word) = 0 ∧
      value V (a (Fields.word 0)) (a (Fields.word 1)) (fun j => (a (Fields.bitAux j):ℤ)) = 0 ∧
      (∀ u, value T (inputField x (a ∘ Fields.word) u) (a (Fields.len u))
        (fun j => (a (Fields.aux u j):ℤ)) = 0) ∧
      (∀ i, P.eval (a (Fields.len none):ℤ) = (a (Fields.len (some i)):ℤ) + a (Fields.slack i)) := by
  have wordenv : (inputs x a) ∘ invar = inputs x (a ∘ Fields.word) := by
    funext u; cases u <;> rfl
  have vb : eval (inputs x a) (bitPoly V 0 1) =
      value V (a (Fields.word 0)) (a (Fields.word 1)) (fun j => (a (Fields.bitAux j):ℤ)) := by
    rw [bitPoly,eval_rename]
    rw [value,eqEval]
    apply congrArg (fun u => eval u _)
    funext i; rcases i with b|u
    · cases b <;> rfl
    · rfl
  have vl (u : Option (Fin (r+2))) : eval (inputs x a) (lengthPoly T u) =
      value T (inputField x (a ∘ Fields.word) u) (a (Fields.len u)) (fun j => (a (Fields.aux u j):ℤ)) := by
    rw [lengthPoly,eval_rename]
    rw [value,eqEval]
    apply congrArg (fun u => eval u _)
    funext i; rcases i with b|j
    · cases b <;> cases u <;> rfl
    · rfl
  have vq : eval (inputs x a) (rename invar Q) = polyValue Q x (a ∘ Fields.word) := by
    rw [eval_rename,wordenv,polyValue,eqEval]
    apply congrArg (fun u => eval u Q); funext i; cases i <;> rfl
  simp only [combined, map_sum, map_pow]
  simp only [pow_two, Finset.sum_mul_self_eq_zero_iff, Finset.mem_univ,
    forall_const, Sum.forall, equations, Sum.elim_inl, Sum.elim_inr, vq, vb, vl,
    boundPoly, map_sub, eval_X, liftBound_eval]
  simp [inputs, sub_sub, sub_eq_zero]


private theorem membership_from_fields {W : Type} [Fintype W] (L : Language)
    (R : MvPolynomial (Option W) ℤ) (q : Polynomial ℕ)
    (yes : ∀ x ∈ L, ∃ a : W → ℕ, (∀ i, bits (a i) ≤ q.eval (bits x)) ∧ eval (inputs x a) R = 0)
    (sound : ∀ x (a : W → ℕ), eval (inputs x a) R = 0 → x ∈ L) : L ∈ D := by
  classical
  let e := Fintype.equivFin W
  let P := rename (Option.map e) R
  have ep (x : ℕ) (w : Fin (Fintype.card W) → ℕ) :
      polyValue P x w = eval (inputs x (w ∘ e)) R := by
    rw [polyValue,eqEval]
    unfold P
    rw [eval_rename]
    apply congrArg (fun u => eval u R)
    funext i; cases i <;> rfl
  refine ⟨_,Polynomial.C (Fintype.card W)*q,P,fun x => ⟨?_,?_⟩⟩
  · intro h
    obtain ⟨a,ha,he⟩ := yes x h
    refine ⟨a ∘ e.symm, ?_, ?_⟩
    · simpa [natCost,Polynomial.eval_mul] using
        (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (Fintype.card W))))
          (fun i _ => ha (e.symm i)))
    · simpa [ep,Function.comp_def] using he
  · rintro ⟨w,_,hw⟩
    exact sound x (w ∘ e) ((ep x w).symm.trans hw)

private theorem strong_of_native (native : NativeVerifier) : StrongNatVerifier := by
  obtain ⟨r,C,_,_,T,ht⟩ := native
  refine ⟨Fin r ⊕ Fin r,inferInstance,C,splitEquation T,?_⟩
  intro n a b hn ha hb
  obtain ⟨yes,sound⟩ := ht n a b hn ha hb
  constructor
  · intro incl
    obtain ⟨w,hw,hv⟩ := yes incl
    exact ⟨splitWitness w, by simpa [cost_split] using hw, by rwa [value_split,decode_split]⟩
  · intro w hw
    exact sound _ ((value_split ..).symm.trans hw)

/-- Every zero of the compiled polynomial satisfies the source's inclusive
length comparisons. A true instance admits one such zero whose total witness
length is polynomial in the input length. -/
theorem mem_D_of_normalForm {L : Language} (source : NormalForm L)
    (native : NativeVerifier) (lengths : LengthGraph) : L ∈ D := by
  classical
  obtain ⟨r,P,Q,hsource⟩ := source
  obtain ⟨l,c,T,tsound,tyes⟩ := lengths
  obtain ⟨B,bfin,k,V,hv⟩ := strong_of_native native
  letI : Fintype B := bfin
  obtain ⟨p,hp⟩ := majorant P
  let A : Polynomial ℕ := Polynomial.X + p + 5
  let budget : Polynomial ℕ := A+1 + (A+2)^c + (A+2)^k
  apply membership_from_fields L (combined P Q T V) budget
  · intro x xyes
    obtain ⟨w,hw,wi,wq⟩ := (hsource x).mp xyes
    let cut : ℤ := P.eval (x.size : ℤ)
    let vals := inputField x w
    let lens (u : Option (Fin (r+2))) := (vals u).size
    let slack (i : Fin (r+2)) := (cut-(lens (some i):ℤ)).toNat
    have hslack (i) : cut = (lens (some i):ℤ) + slack i := by
      have h : (lens (some i):ℤ) ≤ cut := hw i
      dsimp [slack]; omega
    choose aux haux eaux using fun u => tyes (vals u)
    let wid := width (w 0) (w 1)
    obtain ⟨hn,h0,h1⟩ := width_spec (w 0) (w 1)
    obtain ⟨b,hb,eb⟩ := (hv wid (w 0) (w 1) hn h0 h1).1 wi
    let a := Fields.make w lens slack aux b
    refine ⟨a,?_,(combined_zero ..).mpr ⟨wq,eb,eaux,hslack⟩⟩
    let v := A.eval (bits x)
    have hv_eq : v = bits x + p.eval (bits x) + 5 := by simp [v,A]
    have hcut : cut.natAbs ≤ p.eval (bits x) := hp _ _ (size_le_bits x)
    have hcut' : cut ≤ (cut.natAbs:ℤ) := Int.le_natAbs
    have hsize (i) : (w i).size ≤ p.eval (bits x) := by have := hw i; change _ ≤ cut at this; omega
    have hword (i) : bits (w i) ≤ v := by have := hsize i; have := bits_le_size_succ (w i); omega
    have hval (u) : bits (vals u) ≤ v := by cases u with
      | none => change bits x ≤ v; omega
      | some i => exact hword i
    have hlens (u) : bits (lens u) ≤ v+1 :=
      (bits_le_succ _).trans (Nat.succ_le_succ ((size_le_bits _).trans (hval u)))
    have hs (i) : bits (slack i) ≤ v+1 := by
      have := hslack i
      have := bits_le_succ (slack i)
      omega
    have haux' (u i) : bits (aux u i) ≤ (v+2)^c :=
      (component_cost _ i).trans ((haux u).trans (Nat.pow_le_pow_left (by have := hval u; omega) c))
    have hb' (i) : bits (b i) ≤ (v+2)^k := by
      have hh : wid ≤ v := max_le (hword 0) (hword 1)
      exact (component_cost _ i).trans (hb.trans (Nat.pow_le_pow_left (by omega) k))
    have hbudget : budget.eval (bits x) = v+1+(v+2)^c+(v+2)^k := by simp [budget,v]
    rw [hbudget]
    rintro (i | u | i | ⟨u,j⟩ | j)
    · exact (hword i).trans (by omega)
    · exact (hlens u).trans (by omega)
    · exact (hs i).trans (by omega)
    · exact (haux' u j).trans (by omega)
    · exact (hb' j).trans (by omega)
  · intro x a ha
    obtain ⟨eqn,binc,llen,bounds⟩ := (combined_zero ..).mp ha
    let w := a ∘ Fields.word
    obtain ⟨hn,h0,h1⟩ := width_spec (w 0) (w 1)
    have incl := (hv _ (w 0) (w 1) hn h0 h1).2 _ binc
    have ht (u) : a (Fields.len u) = (inputField x w u).size := tsound _ _ _ (llen u)
    apply (hsource x).mpr
    refine ⟨w,fun i => ?_,incl,eqn⟩
    have hi := bounds i
    rw [ht none, ht (some i)] at hi
    change P.eval (x.size:ℤ) = ((w i).size : ℤ) + _ at hi
    omega

end
end DiophantineNP.Classes.Jones
