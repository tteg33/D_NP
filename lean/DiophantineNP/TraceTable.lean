import DiophantineNP.JMTableau

/-! # Fixed tables of guarded affine register transitions -/
namespace DiophantineNP.JMTableau

structure TraceTable where
  m : ℕ
  b : ℕ
  k : ℕ
  P : Fin b → List (Affine m × Affine m)
  old : Fin k → Fin m
  new : Fin k → Fin m

def TraceTable.Run (T : TraceTable) (n v : ℕ) (first last : Fin T.k → ℕ) : Prop :=
  ∃ r : Fin T.m → Fin n → ℕ, (∀ i t, r i t < 2^v) ∧
    (∀ t, ∃ i, ∀ p ∈ T.P i, p.1.eval (fun j => r j t) = p.2.eval (fun j => r j t)) ∧
    ∀ j, ∃ s : Fin (n+1) → ℕ, s 0 = first j ∧ s (Fin.last n) = last j ∧
      (∀ t, s t.castSucc = r (T.old j) t) ∧ ∀ t, s t.succ = r (T.new j) t

end DiophantineNP.JMTableau
