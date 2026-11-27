import DiophantineNP.BoundedPolynomials
import DiophantineNP.TracePorts

/-! # Fixed-polynomial compilation of all tableau masks and equations -/
namespace DiophantineNP.JMTableau.TraceTable
open BoundedRelation MvPolynomial

/-- The index of every auxiliary depends only on the finite instruction table. -/
inductive Aux (T : TraceTable) where
  | ones | capPred | radixPred
  | flag (i : Fin T.b)
  | inactive (i : Fin T.b)
  | word (j : Fin T.m)
  | extracted (i : Fin T.b) (e : Fin (T.P i).length) (j : Fin T.m)
  deriving Fintype, DecidableEq

/-- Representation using ordinary natural polynomial equalities, comparisons,
and native masks. Complements are named explicitly to avoid natural subtraction. -/
def Raw (T : TraceTable) (z : Env T.Port) (u : Env T.Aux) : Prop :=
  let K := z .capacity
  let H := z .clock
  let Q := 2^T.guard*K
  let I := u .ones
  let k := u .capPred
  let q := u .radixPred
  let L (i) := u (.flag i)
  let R (j) := u (.word j)
  K=k+1 ∧ Q=q+1 ∧ H=q*I+1 ∧ BitIncl K (2*k+1) ∧ BitIncl H (2*(q*I)+1) ∧
  (∑ i, L i)=I ∧ (∀ j, BitIncl (R j) (k*I)) ∧
  (∀ j, z (.first j)<K ∧ z (.last j)<K ∧
    R (T.old j)+H*z (.last j) = Q*R (T.new j)+z (.first j)) ∧
  ∀ i, L i+u (.inactive i)=I ∧ BitIncl (L i) I ∧
    ∀ e : Fin (T.P i).length,
      let a := (T.P i).get e
      let A (j) := u (.extracted i e j)
      a.1.packed (L i) A = a.2.packed (L i) A ∧
      ∀ j, BitIncl (A j) (R j) ∧ BitIncl (A j) (q*L i) ∧ BitIncl (R j) (q*u (.inactive i)+A j)

private structure Check (σ : Type) where
  test : Relation σ
  code : Short test

private def conj {σ} (p q : Check σ) : Check σ := ⟨_,p.code.and q.code⟩
private def every {σ ι : Type} [Fintype ι] (p : ι → Check σ) : Check σ := ⟨_,Short.all fun i => (p i).code⟩
private def eqn {σ} (a b : MvPolynomial σ ℕ) : Check σ := ⟨_,Short.eqPoly a b⟩
private def less {σ} (a b : MvPolynomial σ ℕ) : Check σ := ⟨_,Short.ltPoly a b⟩
private def incl {σ} (native : NativeVerifier) (a b : MvPolynomial σ ℕ) : Check σ := ⟨_,Short.maskPoly native a b⟩
local infixr:30 " &&&ₚ " => conj

noncomputable def packedPoly {m σ} (p : JMTableau.Affine m) (l : MvPolynomial σ ℕ) (a : Fin m → MvPolynomial σ ℕ) :=
  C p.offset*l + ∑ i, C (p.coeff i) * a i

private noncomputable def checks (native : NativeVerifier) (T : TraceTable) : Check (T.Port ⊕ T.Aux) :=
  let z (i : T.Port) : MvPolynomial (T.Port⊕T.Aux) ℕ := X (.inl i)
  let u (i : T.Aux) : MvPolynomial (T.Port⊕T.Aux) ℕ := X (.inr i)
  let K := z .capacity
  let H := z .clock
  let Q := C (2^T.guard)*K
  let I := u .ones
  let k := u .capPred
  let q := u .radixPred
  let L (i) := u (.flag i)
  let R (j) := u (.word j)
  eqn K (k+1) &&&ₚ eqn Q (q+1) &&&ₚ eqn H (q*I+1) &&&ₚ incl native K (2*k+1) &&&ₚ incl native H (2*(q*I)+1) &&&ₚ
  eqn (∑ i, L i) I &&&ₚ (every fun j => incl native (R j) (k*I)) &&&ₚ
  (every fun j => less (z (.first j)) K &&&ₚ less (z (.last j)) K &&&ₚ
    eqn (R (T.old j)+H*z (.last j)) (Q*R (T.new j)+z (.first j))) &&&ₚ
  (every fun i => eqn (L i+u (.inactive i)) I &&&ₚ incl native (L i) I &&&ₚ
    every fun e : Fin (T.P i).length =>
      let a := (T.P i).get e
      let A (j) := u (.extracted i e j)
      eqn (packedPoly a.1 (L i) A) (packedPoly a.2 (L i) A) &&&ₚ
      every fun j => incl native (A j) (R j) &&&ₚ incl native (A j) (q*L i) &&&ₚ incl native (R j) (q*u (.inactive i)+A j))

/-- Native certificates are included independently for all masks. All
introduced certificate slots have a polynomial bound in the tableau word lengths. -/
theorem raw_short (native : NativeVerifier) (T : TraceTable) : Short (fun x => T.Raw (x ∘ Sum.inl) (x ∘ Sum.inr)) := by
  apply (checks native T).code.congr
  intro x
  simp only [checks,Raw,conj,every,eqn,less,incl,packedPoly,JMTableau.Affine.packed,
    map_add,map_mul,map_one,map_ofNat,map_sum,eval_C,eval_X,Function.comp_apply]

end DiophantineNP.JMTableau.TraceTable
