import DiophantineNP.TraceChecker
import DiophantineNP.RegisterFieldPacking

/-! # Native masking suffices to verify the binary length graph

An affine program repeatedly divides a register by two and decrements a second
register. It stops as soon as the value is 0 or 1. The endpoint counter is one,
so zero is charged one bit, just as in the fixed-polynomial complexity classes. -/
namespace DiophantineNP.BoundedRelation
open JMTableau Classes.Jones.Machine MvPolynomial
noncomputable section

private def lengthRows (i : Fin 2) : List (Classes.Jones.Machine.Equation 5) :=
  [(linear 0 1 0,linear 2 2 i.val),(linear 1 1 0,linear 3 1 1),(linear 0 1 0,linear 4 1 2)]

private def counter : TraceTable where
  m := 5
  b := 2
  k := 2
  P := lengthRows
  old := ![0,1]
  new := ![2,3]

private theorem row_eq (i : Fin 2) (u : Fin 5 → ℕ) : Satisfies (lengthRows i) u ↔
    u 0 = i.val+2*u 2 ∧ u 1 = 1+u 3 ∧ u 0 = 2+u 4 := by simp [lengthRows,Satisfies]

private theorem half_bits {a : ℕ} (ha : 2≤a) : bits a=bits (a/2)+1 := by
  unfold bits; rw [Nat.log2_def a,if_pos ha]

private theorem counter_sound {x y tail n v : ℕ} (ht : tail≤1)
    (run : counter.Run n v (pairRegs x y) (pairRegs tail 1)) : y=bits x := by
  obtain ⟨r,_,br,link⟩ := run
  change Fin 5 → Fin n → ℕ at r
  obtain ⟨a,az,al,ao,an⟩ := link (0 : Fin 2)
  obtain ⟨c,cz,cl,co,cn⟩ := link (1 : Fin 2)
  change a 0=x at az; change a (Fin.last n)=tail at al
  change c 0=y at cz; change c (Fin.last n)=1 at cl
  have next (t : Fin n) : bits (a t.castSucc) = bits (a t.succ)+1 ∧ c t.castSucc=c t.succ+1 := by
    obtain ⟨i,hi⟩ := br t
    obtain ⟨e,d,sl⟩ := (row_eq i (fun j => r j t)).mp hi
    have Hao : a t.castSucc = r 0 t := ao t
    have Han : a t.succ = r 2 t := an t
    have Hco : c t.castSucc = r 1 t := co t
    have Hcn : c t.succ = r 3 t := cn t
    have hdiv : a t.castSucc/2=a t.succ := by have := i.isLt; omega
    exact ⟨(half_bits (by omega : 2≤a t.castSucc)).trans (congrArg (fun z => bits z+1) hdiv),by omega⟩
  have inv (j : Fin (n+1)) : y + bits (a j) = c j + bits x := by
    induction j using Fin.induction with
    | zero => rw [az,cz]
    | succ k ih => obtain ⟨h₁,h₂⟩ := next k; omega
  have eq := inv (Fin.last n)
  rw [al,cl] at eq
  have hbit : bits tail=1 := by unfold bits; rw [Nat.log2_def,if_neg (by omega)]
  omega

private theorem run_zero (T : TraceTable) (w : ℕ) (s : Fin T.k → ℕ) : T.Run 0 w s s :=
  ⟨fun _ => Fin.elim0,fun _ t => t.elim0,fun t => t.elim0,fun j => ⟨fun _ => s j,rfl,rfl,fun t => t.elim0,fun t => t.elim0⟩⟩

private theorem prependRow {n w : ℕ} (T : TraceTable) {a b c : Fin T.k → ℕ} (s : Fin T.m → ℕ)
    (hs : ∀ j, s j<2^w) (test : ∃ i, Satisfies (T.P i) s) (ha : ∀ j, s (T.old j)=a j)
    (hb : ∀ j, s (T.new j)=b j) (run : T.Run n w b c) : T.Run (n+1) w a c := by
  obtain ⟨r,hr,br,links⟩ := run
  refine ⟨fun j => Fin.cons (s j) (r j),fun j => Fin.cases (hs j) (hr j),Fin.cases test br,fun j => ?_⟩
  obtain ⟨u,uz,ul,uo,un⟩ := links j
  refine ⟨Fin.cons (a j) u,rfl,by simpa only [Fin.cons_last] using ul,?_,?_⟩
  · intro k; refine Fin.cases ?_ (fun i => ?_) k
    · exact (ha j).symm
    · simpa only [Fin.castSucc_succ,Fin.cons_succ] using uo i
  · intro k; refine Fin.cases ?_ (fun i => ?_) k
    · simpa only [Fin.cons_succ,Fin.cons_zero] using uz.trans (hb j).symm
    · simpa only [Fin.cons_succ] using un i

private theorem counter_complete (x w : ℕ) (hx : x<2^w) (hc : bits x<2^w) :
    ∃ tail≤1, counter.Run x.log2 w (pairRegs x (bits x)) (pairRegs tail 1) := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases h : 2≤x
    · let a := x/2
      have ha : a<x := Nat.div_lt_self (by omega) (by decide)
      have hc' : bits x=bits a+1 := half_bits h
      obtain ⟨tail,ht,run⟩ := ih a ha (ha.trans hx) ((FourSquare.bits_mono ha.le).trans_lt hc)
      refine ⟨tail,ht,?_⟩
      rw [Nat.log2_def x,if_pos h]
      let row : Fin 5 → ℕ := ![x,bits x,a,bits a,x-2]
      apply prependRow counter row _ _ _ _ run
      · intro j; change Fin 5 at j; fin_cases j <;> dsimp [row] <;> omega
      · let i : Fin 2 := ⟨x%2,Nat.mod_lt _ (by decide)⟩
        refine ⟨i,(row_eq i row).mpr ?_⟩
        simp [row,i,a] at *; omega
      · intro j; change Fin 2 at j; fin_cases j <;> rfl
      · intro j; change Fin 2 at j; fin_cases j <;> rfl
    · have hl : x.log2=0 := by rw [Nat.log2_def,if_neg h]
      have hb : bits x=1 := by simp [bits,hl]
      refine ⟨x,by omega,?_⟩
      rw [hl,hb]; exact run_zero counter w _

private def wires {σ : Type} (x l : σ) (z : Env (σ⊕Fin 3)) : Env counter.Port
  | .first j => pairRegs (z (.inl x)) (z (.inl l)) j
  | .last j => pairRegs (z (.inr 0)) 1 j
  | .capacity => z (.inr 1)
  | .clock => z (.inr 2)

private def wirePoly {σ : Type} (x l : σ) : counter.Port → MvPolynomial (σ⊕Fin 3) ℕ
  | .first j => ![X (.inl x), X (.inl l)] j
  | .last j => ![X (.inr 0),1] j
  | .capacity => X (.inr 1)
  | .clock => X (.inr 2)

/-- The graph of binary length needs only the globally sound native verifier.
The table's clock contains at most `O(h²)` bits for `h`-bit inputs. -/
theorem Short.nativeLength (native : NativeVerifier) {σ : Type} (x l : σ) :
    Short (fun z : Env σ => z l = bits (z x)) := by
  let S : Relation (σ⊕Fin 3) := fun z => counter.Accepts (wires x l z) ∧ z (.inr 0)≤1
  have sc : Short (fun z => counter.Accepts (wires x l z)) := by
    apply ((counter.run_short native).subst (wirePoly x l)).congr
    intro z
    have e : (fun i => eval z (wirePoly x l i))=wires x l z := by
      funext i; cases i with
      | first j | last j => change Fin 2 at j; fin_cases j <;> simp [wirePoly,wires,pairRegs]
      | capacity | clock => simp [wirePoly,wires]
    rw [e]
  have hS : Short S := sc.and ((Short.lePoly (X (.inr (0 : Fin 3))) 1).congr (fun z => by simp))
  let g := counter.guard
  apply Short.exists_of S hS (Polynomial.X+3+(Polynomial.C g+Polynomial.X+1)*Polynomial.X)
  · rintro z u ⟨⟨n,v,_,_,_,run⟩,ht⟩
    exact counter_sound ht run
  · intro h z hz yes
    let a := z x
    let w := h+1
    let n := a.log2
    have hn : n≤h := by have hh := hz x; change a.log2+1≤h at hh; omega
    have hpow (i) : z i < 2^w := Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) ((hz i).trans (Nat.le_succ h)))
    obtain ⟨t,ht,run⟩ := counter_complete a w (hpow x) (yes ▸ hpow l)
    let u : Env (Fin 3) := ![t,2^w,2^((g+w)*n)]
    refine ⟨u,?_,⟨n,w,rfl,rfl,?_,?_⟩,ht⟩
    · intro i
      have bt : bits t≤1 := (FourSquare.bits_mono ht).trans (by decide)
      have count : (g+(h+1))*n ≤ (g+h+1)*h := by rw [Nat.add_assoc]; exact Nat.mul_le_mul_left _ hn
      fin_cases i
      · change bits t ≤ _; simpa using bt.trans (show 1≤h+3+(g+h+1)*h by omega)
      · simp [u,bits,w]; omega
      · simp [u,bits,w]; omega
    · intro j
      have One : 1<2^w := Nat.one_lt_two_pow (by dsimp [w]; omega)
      change Fin 2 at j; fin_cases j
      · exact ⟨hpow x,ht.trans_lt One⟩
      · exact ⟨hpow l,One⟩
    · change counter.Run n w (pairRegs (z x) (z l)) (pairRegs t 1)
      rwa [yes]

end
end DiophantineNP.BoundedRelation
