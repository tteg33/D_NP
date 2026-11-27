import DiophantineNP.ShortResidue

/-! # Short prime residues of the verifier's actual width modulus

Each of the first n odd primes occurs in 4n+10 rows. Finite integer
division locates its row block and the checked prime-rank formula supplies
the prime itself. The resulting ordinary finite formula evaluates
widthD modulo every prime in the proven short-power range.
-/
namespace DiophantineNP.WidthPrimeResidue
set_option maxHeartbeats 450000
attribute [local irreducible] PrimeFormula.oddPrimeAtVars
open Counting PrimeFormula WidthFormula WidthData FiniteArithmeticGap

private def qr {k : ℕ} (x d q r : Fin k) : Formula k :=
  .ex (andF (mulF q.succ d.succ 0) (andF (addF 0 r.succ x.succ) (ltF r.succ d.succ)))

private theorem qr_true {U k : ℕ} (x d q r : Fin k) (env : Fin k → Fin U) (hd : 0<(env d).val) :
    (qr x d q r).eval env=true ↔ (env q).val=(env x).val/(env d).val ∧ (env r).val=(env x).val%(env d).val := by
  simp only [qr,exists_true,andF_spec,mulF_spec,addF_spec,ltF_true,Fin.cases_succ,Fin.cases_zero]
  constructor
  · rintro ⟨m,hm,he,hr⟩
    rw [show (env x).val=(env r).val+(env d).val*(env q).val by rw [Nat.mul_comm]; omega,
      Nat.add_mul_div_left _ _ hd,Nat.div_eq_of_lt hr,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr,Nat.zero_add]
    exact ⟨rfl,rfl⟩
  · rintro ⟨hq,hr⟩
    have he := Nat.div_add_mod (env x).val (env d).val
    rw [← hq,← hr,Nat.mul_comm] at he
    exact ⟨⟨_,by have := (env x).isLt; omega⟩,rfl,he,hr ▸ Nat.mod_lt _ hd⟩

private def remainder {k : ℕ} (x d r : Fin k) : Formula k := .ex (qr x.succ d.succ 0 r.succ)
private def quotient {k : ℕ} (x d q : Fin k) : Formula k := .ex (qr x.succ d.succ q.succ 0)

private theorem rem_true {U k : ℕ} (x d r : Fin k) (env : Fin k → Fin U) (hd : 0<(env d).val) :
    (remainder x d r).eval env=true ↔ (env r).val=(env x).val%(env d).val := by
  rw [remainder,exists_true]
  have hh (v : Fin U) := qr_true x.succ d.succ 0 r.succ (Fin.cons v env) hd
  constructor
  · rintro ⟨v,h⟩
    exact ((hh v).mp h).2
  · intro h
    let v : Fin U := ⟨_,(Nat.div_le_self (env x).val (env d).val).trans_lt (env x).isLt⟩
    exact ⟨v,(hh v).mpr ⟨rfl,h⟩⟩

private theorem quot_true {U k : ℕ} (x d q : Fin k) (env : Fin k → Fin U) (hd : 0<(env d).val) :
    (quotient x d q).eval env=true ↔ (env q).val=(env x).val/(env d).val := by
  rw [quotient,exists_true]
  have hh (v : Fin U) := qr_true x.succ d.succ q.succ 0 (Fin.cons v env) hd
  constructor
  · rintro ⟨v,h⟩
    exact ((hh v).mp h).1
  · intro h
    let v : Fin U := ⟨_,(Nat.mod_lt (env x).val hd).trans (env d).isLt⟩
    exact ⟨v,(hh v).mpr ⟨h,rfl⟩⟩

private def entryF {k : ℕ} (row col m d p : Fin k) : Formula k :=
  branch (ltF row m)
    (.ex (andF (quotient row.succ d.succ 0) (.ex (andF (oddPrimeAtVars 0 (0 : Fin (k+1)).succ)
      (remainder 0 (up2 p) (up2 col))))))
    (isNat 0 col)

private noncomputable def f (_n m d : ℕ) (r : ℕ) := if r<m then Nat.nth Nat.Prime (r/d+1) else 0

private theorem entryF_eval {n k : ℕ} (r c m d p : Fin k) (env : Fin k → Fin (universeSize n))
    (hd : 0<(env d).val) (hm : (env m).val=n*(env d).val) (hp : 0<(env p).val) :
    (entryF r c m d p).eval env=decide ((env c).val=f n (env m).val (env d).val (env r).val%(env p).val) := by
  apply Bool.eq_iff_iff.mpr
  rw [entryF,branch_eval,decide_eq_true_eq]
  by_cases h : (env r).val < (env m).val
  · have hi : (env r).val/(env d).val<n := (Nat.div_lt_iff_lt_mul hd).mpr (hm ▸ h)
    have htt : (ltF r m).eval env = true := (ltF_true r m env).mpr h
    rw [if_pos htt,f,if_pos h,exists_true]
    change (∃ i : Fin (universeSize n), (andF _ _).eval (Fin.cons i env) = true) ↔ _
    simp only [andF_spec,exists_true]
    constructor
    · rintro ⟨i,hq,q,hp',hv⟩
      have he := (quot_true r.succ d.succ 0 (Fin.cons i env) hd).mp hq
      change i.val=(env r).val/(env d).val at he
      have hprime := (width_prime_vars 0 (0 : Fin (k+1)).succ (Fin.cons q (Fin.cons i env)) (he ▸ hi)).mp hp'
      change q.val=Nat.nth Nat.Prime (i.val+1) at hprime
      have hval := (rem_true 0 (up2 p) (up2 c) (Fin.cons q (Fin.cons i env)) hp).mp hv
      change (env c).val=q.val%(env p).val at hval
      exact hval.trans (congrArg (fun z => z%(env p).val) (hprime.trans (congrArg (fun i => Nat.nth Nat.Prime (i+1)) he)))
    · intro hv
      let i : Fin (universeSize n) := ⟨_,hi.trans (width_parameter_fits n)⟩
      let q : Fin (universeSize n) := ⟨Nat.nth Nat.Prime (i.val+1),(oddPrime_lt_search_limit hi).trans (search_limit_fits n)⟩
      exact ⟨i,(quot_true r.succ d.succ 0 (Fin.cons i env) hd).mpr rfl,q,(width_prime_vars 0 (0 : Fin (k+1)).succ (Fin.cons q (Fin.cons i env)) hi).mpr rfl,
        (rem_true 0 (up2 p) (up2 c) (Fin.cons q (Fin.cons i env)) hp).mpr hv⟩
  · rw [if_neg (mt (ltF_true r m env).mp h),f,if_neg h,Nat.zero_mod,isNat_spec]

private theorem prod_add (f : ℕ → ℕ) (n d : ℕ) :
    productPrefix f (n+d)=productPrefix f n*productPrefix (fun i => f (n+i)) d := by
  induction d with
  | zero => simp [productPrefix]
  | succ d ih => rw [← Nat.add_assoc,product_succ,ih,product_succ,mul_assoc]

private theorem repeated (f : ℕ → ℕ) (d : ℕ) (hd : 0<d) (n : ℕ) :
    productPrefix (fun i => f (i/d)) (n*d) = productPrefix (fun i => (f i)^d) n := by
  induction n with
  | zero => simp [productPrefix]
  | succ n ih =>
    rw [Nat.succ_mul,prod_add,ih,product_succ]
    congr 1
    rw [← product_constant]
    unfold productPrefix
    congr 1
    apply List.map_congr_left
    intro i hi
    change f ((n*d+i)/d)=f n
    rw [Nat.mul_comm n d, Nat.mul_add_div hd, Nat.div_eq_of_lt (List.mem_range.mp hi),Nat.add_zero]

private theorem f_prod (n : ℕ) (d : ℕ) (hd : d=4*n+10) : productPrefix (f n (n*d) d) (n*d) = widthD n := by
  have he : productPrefix (f n (n*d) d) (n*d)=productPrefix (fun i => Nat.nth Nat.Prime (i/d+1)) (n*d) := by
    unfold productPrefix
    congr 1
    apply List.map_congr_left
    intro i hi; simp [f,List.mem_range.mp hi]
  rw [he,repeated (fun i => Nat.nth Nat.Prime (i+1)) d (by omega)]
  subst d; rfl

private def basis : BitTemplate where
  nativeBit := bitAt 0 1
  bit_correct x j := bitAt_eval 0 1 (pairEnv x j)

/-- A concrete finite formula for the actual modulus when the block length
and row count are supplied as finite numerical parameters. -/
noncomputable def description {k : ℕ} (m d p b : Fin k) : Formula k :=
  substitute basis (entryF (0 : Fin (k+1)).succ 0 (up2 m) (up2 d) (up2 p))
    ShortResidue.productResidue ![m,p,b] id

theorem description_correct {k n K : ℕ} (m d p b : Fin k) (env : Fin k → Fin (universeSize n))
    (hd : (env d).val=4*n+10) (hm : (env m).val=n*(env d).val) (hp : (env p).val.Prime)
    (hsize : (env m).val*(env p).val<universeSize n-universeSize n/2) (hK : 2≤K)
    (hpk : (env p).val≤2^K) (hcap : 2^((K+1)*K)<universeSize n) :
    (description m d p b).eval env = true ↔ (env b).val=widthD n%(env p).val := by
  let ff := f n (env m).val (env d).val
  rw [description,substitute_eval]
  have htab (r c : Fin (universeSize n)) := entryF_eval (0 : Fin (k+1)).succ 0 (up2 m) (up2 d) (up2 p)
    (extend c r (env ∘ id)) (by change 0<(env d).val; omega) hm hp.pos
  have ht : (fun r c => (entryF (0 : Fin (k+1)).succ 0 (up2 m) (up2 d) (up2 p)).eval (extend c r (env ∘ id))) =
      fun r c : Fin (universeSize n) => decide (c.val=ff r.val%(env p).val) := funext fun r => funext fun c => htab r c
  rw [ht]
  have he : env ∘ ![m,p,b]=![(env m),(env p),(env b)] := by funext i; fin_cases i <;> rfl
  rw [he, ShortResidue.productResidue_spec _ _ _ ff hp hsize hK hpk hcap]
  dsimp only [ff]
  rw [hm,f_prod n _ hd]

end DiophantineNP.WidthPrimeResidue
