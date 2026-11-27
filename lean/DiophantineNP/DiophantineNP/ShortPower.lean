import DiophantineNP.FiniteArithmeticGap

/-! # Short modular powers in finite arithmetic

A packed certificate for repeated squaring uses one radix digit per bit of
the exponent. Both syntax and the packing estimate are uniform in the
width, base, exponent and modulus (Hesse–Allender–Barrington, Lemma 5.1).
-/
namespace DiophantineNP.ShortPower
open Counting PrimeFormula WidthFormula FiniteArithmeticGap

/-- An arithmetic/majority formula with named variables; quantifiers compile
to the ordinary de Bruijn representation. -/
private structure Rel where
  syntaxF : {k : ℕ} → (ℕ → Fin k) → Formula k
  holds : ℕ → (ℕ → ℕ) → Prop
  valid {k U : ℕ} (σ : ℕ → Fin k) (env : Fin k → Fin U) :
    (syntaxF σ).eval env = true ↔ holds U (fun i => (env (σ i)).val)

private def Rel.and (p q : Rel) : Rel where
  syntaxF σ := andF (p.syntaxF σ) (q.syntaxF σ)
  holds U e := p.holds U e ∧ q.holds U e
  valid σ e := by simp only [andF_spec,p.valid,q.valid]

private def Rel.not (p : Rel) : Rel where
  syntaxF σ := notF (p.syntaxF σ)
  holds U e := ¬p.holds U e
  valid σ e := by simp only [notF_spec,p.valid]

private def Rel.ex (x : ℕ) (p : Rel) : Rel where
  syntaxF σ := .ex (p.syntaxF (Function.update (Fin.succ ∘ σ) x 0))
  holds U e := ∃ t<U, p.holds U (Function.update e x t)
  valid {k U} σ env := by
    rw [exists_true]
    have he (z : Fin U) : (fun i => ((Fin.cases z env : Fin (k+1) → Fin U) (Function.update (Fin.succ ∘ σ) x 0 i)).val) =
        Function.update (fun i => (env (σ i)).val) x z.val := by
      funext i
      by_cases h : i=x
      · subst i; simp
      · simp [h]
    simp_rw [p.valid,he]
    constructor
    · rintro ⟨z,h⟩; exact ⟨z,z.isLt,h⟩
    · rintro ⟨z,hz,h⟩; exact ⟨⟨z,hz⟩,h⟩

private def Rel.all (x : ℕ) (p : Rel) : Rel := (Rel.ex x p.not).not
private def Rel.imp (p q : Rel) : Rel := (p.and q.not).not
private def Rel.or (p q : Rel) : Rel := (p.not.and q.not).not

private def Rel.lit (a : ℕ) (v : ℕ) : Rel where
  syntaxF σ := isNat a (σ v)
  holds _ e := e v = a
  valid _ _ := isNat_spec .. 

private def Rel.add (a b v : ℕ) : Rel where
  syntaxF σ := addF (σ a) (σ b) (σ v)
  holds _ e := e a+e b=e v
  valid _ _ := addF_spec ..

private def Rel.mul (a b v : ℕ) : Rel where
  syntaxF σ := mulF (σ a) (σ b) (σ v)
  holds _ e := e a*e b=e v
  valid _ _ := mulF_spec ..

private def Rel.lt (v w : ℕ) : Rel where
  syntaxF σ := ltF (σ v) (σ w)
  holds _ e := e v < e w
  valid _ _ := ltF_true ..

private def Rel.bit (v w : ℕ) : Rel where
  syntaxF σ := bitAt (σ v) (σ w)
  holds _ e := (e v).testBit (e w) = true
  valid σ e := by rw [bitAt_eval]

private def Rel.pow2 (i v : ℕ) : Rel where
  syntaxF σ := powerAt (σ v) (σ i)
  holds _ e := e v=2^(e i)
  valid _ _ := powerAt_spec ..

/-- Graph of ordinary division with positive divisor. Multiplication and
addition are exact within the universe because their result is at most x. -/
private def divRem {k : ℕ} (x d q r : Fin k) : Formula k :=
  .ex (andF (mulF d.succ q.succ 0)
    (andF (addF 0 r.succ x.succ) (ltF r.succ d.succ)))

private theorem divRem_true {U k : ℕ} (x d q r : Fin k) (env : Fin k → Fin U) :
    (divRem x d q r).eval env = true ↔
      0<(env d).val ∧ (env q).val=(env x).val/(env d).val ∧ (env r).val=(env x).val%(env d).val := by
  simp only [divRem, exists_true,andF_spec,mulF_spec,addF_spec,ltF_true,Fin.cases_succ,Fin.cases_zero]
  constructor
  · rintro ⟨m,hm,he,hr⟩
    have hd : 0<(env d).val := by omega
    have hx : (env x).val=(env r).val+(env d).val*(env q).val := by omega
    rw [hx,Nat.add_mul_div_left _ _ hd,Nat.div_eq_of_lt hr,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
    simp [hd]
  · rintro ⟨hd,hq,hr⟩
    have hh := Nat.div_add_mod (env x).val (env d).val
    rw [← hq, ← hr] at hh
    exact ⟨⟨_,by have := (env x).isLt; omega⟩,rfl,hh,hr ▸ Nat.mod_lt _ hd⟩

private def Rel.modulo (x d r : ℕ) : Rel where
  syntaxF σ := .ex (divRem (σ x).succ (σ d).succ 0 (σ r).succ)
  holds _ e := 0<e d ∧ e r=e x%e d
  valid σ env := by
    simp only [exists_true,divRem_true,Fin.cases_succ,Fin.cases_zero]
    constructor
    · rintro ⟨q,h,_,hr⟩; exact ⟨h,hr⟩
    · rintro ⟨h,hr⟩
      exact ⟨⟨_,(Nat.div_le_self _ _).trans_lt (env (σ x)).isLt⟩,h,rfl,hr⟩

private def packed (B : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => f 0 + B*packed B (fun t => f (t+1)) n

private theorem packed_lt {B : ℕ} (f : ℕ → ℕ) (n : ℕ) (h : ∀ i<n,f i<B) :
    packed B f n < B^n := by
  induction n generalizing f with
  | zero => simp [packed]
  | succ n ih =>
    have hlo := h 0 (by omega)
    have hhi := ih (fun t => f (t+1)) (fun t ht => h (t+1) (by omega))
    have := Nat.mul_le_mul_left B (Nat.succ_le_of_lt hhi)
    rw [pow_succ',packed]
    nlinarith

private theorem packed_digit {B : ℕ} (hB : 0<B) (f : ℕ → ℕ) (n i : ℕ) (hi : i<n) (h : ∀ v<n,f v<B) :
    (packed B f n / B^i)%B = f i := by
  induction n generalizing f i with
  | zero => omega
  | succ n ih =>
    have hlo := h 0 (by omega)
    cases i with
    | zero => simp [packed,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hlo]
    | succ i =>
      rw [pow_succ',← Nat.div_div_eq_div_mul,packed,Nat.add_mul_div_left _ _ hB,Nat.div_eq_of_lt hlo,
        Nat.zero_add]
      exact ih (fun j => f (j+1)) i (by omega) (fun j hj => h _ (by omega))

private theorem power_step (a e p i : ℕ) :
    (a^(e/2^i))%p =
      (if e.testBit i then ((a^(e/2^(i+1))%p)^2*a)%p else (a^(e/2^(i+1))%p)^2%p) := by
  have q : e/2^i = 2*(e/2^(i+1))+(e.testBit i).toNat := by
    rw [Nat.toNat_testBit,pow_succ,← Nat.div_div_eq_div_mul]
    exact (Nat.div_add_mod _ _).symm
  rw [q,pow_add, mul_comm 2, pow_mul]
  cases e.testBit i <;> simp [Nat.mul_mod,Nat.pow_mod]

private def digitF {k : ℕ} (t w i B v : Fin k) : Formula k :=
  .ex (.ex (.ex (.ex (.ex (
    andF (mulF (up4 i).succ (up4 w).succ (0 : Fin (k+1)).succ.succ.succ.succ)
    (andF (powerAt (0 : Fin (k+2)).succ.succ.succ (0 : Fin (k+1)).succ.succ.succ.succ)
    (andF (divRem (up4 t).succ (0 : Fin (k+2)).succ.succ.succ (0 : Fin (k+3)).succ.succ (0 : Fin (k+4)).succ)
      (divRem (0 : Fin (k+3)).succ.succ (up4 B).succ 0 (up4 v).succ))))))))

private theorem digitF_true {k U : ℕ} (t w i B v : Fin k) (env : Fin k → Fin U) :
    (digitF t w i B v).eval env=true ↔
      2^((env i).val*(env w).val)<U ∧ 0<(env B).val ∧
        (env v).val=((env t).val/2^((env i).val*(env w).val))%(env B).val := by
  simp only [digitF,exists_true,andF_spec,mulF_spec,powerAt_spec,divRem_true,Fin.cases_zero,Fin.cases_succ]
  constructor
  · rintro ⟨a,b,q,r,h,ha,hb,⟨_,hq,_⟩,hB,_,hv⟩
    exact ⟨ha ▸ hb ▸ b.isLt,hB,by rw [ha,← hb,← hq]; exact hv⟩
  · rintro ⟨hs,hB,hv⟩
    let a := (env i).val*(env w).val
    let b := 2^a
    have hb : 0<b := Nat.two_pow_pos a
    let q := (env t).val/b
    have ht := (env t).isLt
    have hq : q<U := (Nat.div_le_self _ _).trans_lt ht
    refine ⟨⟨a,(Nat.lt_two_pow_self.trans ?_)⟩,⟨b,hs⟩,⟨q,hq⟩,
      ⟨_,(Nat.mod_lt _ hb).trans hs⟩,⟨_,(Nat.div_le_self _ _).trans_lt hq⟩,
      rfl,rfl,⟨hb,rfl,rfl⟩,hB,rfl,hv⟩
    exact hs

private def Rel.digit (t w i B v : ℕ) : Rel where
  syntaxF σ := digitF (σ t) (σ w) (σ i) (σ B) (σ v)
  holds U e := 2^(e i*e w)<U ∧ 0<e B ∧ e v=(e t/2^(e i*e w))%e B
  valid _ _ := digitF_true ..

private def Step (U a e p w T B i : ℕ) : Prop :=
  ∃ j<U, ∃ v<U, ∃ next<U, ∃ square<U, ∃ cube<U,
    i+1=j ∧
    (2^(i*w)<U ∧ 0<B ∧ v=T/2^(i*w)%B) ∧
    (2^(j*w)<U ∧ 0<B ∧ next=T/2^(j*w)%B) ∧
    next*next=square ∧ square*a=cube ∧
    (((e.testBit i=true) ∧ (0<p ∧ v=cube%p)) ∨ (¬e.testBit i=true) ∧ (0<p ∧ v=square%p))

local infixr:35 " ⋀ " => Rel.and

private def stepR : Rel :=
  Rel.ex 12 <| Rel.ex 13 <| Rel.ex 14 <| Rel.ex 15 <| Rel.ex 16 <|
    Rel.add 11 10 12 ⋀ Rel.digit 6 5 11 7 13 ⋀ Rel.digit 6 5 12 7 14 ⋀
    Rel.mul 14 14 15 ⋀ Rel.mul 15 0 16 ⋀
    Rel.or (Rel.bit 1 11 ⋀ Rel.modulo 16 2 13) ((Rel.bit 1 11).not ⋀ Rel.modulo 15 2 13)

private theorem stepR_holds (U : ℕ) (env : ℕ → ℕ) (hone : env 10=1) :
    stepR.holds U env ↔ Step U (env 0) (env 1) (env 2) (env 5) (env 6) (env 7) (env 11) := by
  classical
  simp [stepR,Step,Rel.ex,Rel.and,Rel.or,Rel.not,Rel.add,Rel.digit,Rel.mul,Rel.bit,Rel.modulo,hone,
    Function.update]
  tauto

private def Certificate (U a e p b : ℕ) : Prop :=
  ∃ L<U, ∃ w<U, ∃ T<U, ∃ B<U, ∃ H<U,
      B=2^w ∧ H=2^L ∧ e<H ∧ 1<p ∧
      (2^(0*w)<U ∧ 0<B ∧ b=T/2^(0*w)%B) ∧
      (2^(L*w)<U ∧ 0<B ∧ 1=T/2^(L*w)%B) ∧
      ∀ i<U, i<L → Step U a e p w T B i

private def program : Rel :=
  Rel.ex 4 <| Rel.ex 5 <| Rel.ex 6 <| Rel.ex 7 <| Rel.ex 8 <|
    Rel.pow2 5 7 ⋀ Rel.pow2 4 8 ⋀ Rel.lt 1 8 ⋀
    (Rel.ex 9 <| Rel.lit 0 9 ⋀ (Rel.ex 10 <| Rel.lit 1 10 ⋀ Rel.lt 10 2 ⋀
      Rel.digit 6 5 9 7 3 ⋀ Rel.digit 6 5 4 7 10 ⋀ Rel.all 11 ((Rel.lt 11 4).imp stepR)))

private theorem program_holds (U : ℕ) (env : ℕ → ℕ) (hp : env 2 < U) :
    program.holds U env ↔ Certificate U (env 0) (env 1) (env 2) (env 3) := by
  classical
  simp [program,Certificate,Rel.ex,Rel.and,Rel.all,Rel.imp,Rel.not,Rel.pow2,Rel.lt,Rel.lit,Rel.digit,
    Function.update,stepR_holds]
  constructor <;> rintro ⟨L,hL,w,hw,T,hT,hB,hH,he,hrest⟩ <;> refine ⟨L,hL,w,hw,T,hT,hB,hH,he,?_⟩ <;> grind

private theorem certificate_sound {U a e p b : ℕ} (hc : Certificate U a e p b) : b=a^e%p := by
  obtain ⟨L,hL,w,_,T,_,B,_,H,_,_,rfl,he,hp,⟨_,_,h0⟩,⟨_,_,htop⟩,hs⟩ := hc
  let v := fun i => T/2^(i*w)%B
  have sound (i : ℕ) (hi : i≤L) : v i=a^(e/2^i)%p := by
    induction hi using Nat.decreasingInduction with
    | self => simpa [v,Nat.div_eq_of_lt he,Nat.mod_eq_of_lt hp] using htop.symm
    | of_succ k hk ih =>
      obtain ⟨j,_,s,_,t,_,sq,_,cu,_,rfl,⟨_,_,rfl⟩,⟨_,_,rfl⟩,rfl,rfl,h⟩ := hs k (hk.trans hL) hk
      change (e.testBit k = true ∧ _ ∧ v k = v (k+1)*v (k+1)*a%p) ∨
             (¬ e.testBit k = true) ∧ _ ∧ v k = v (k+1)*v (k+1)%p at h
      rw [power_step a e p k,← ih,pow_two]
      rcases h with ⟨h,_,h'⟩|⟨h,_,h'⟩ <;> simpa [h] using h'
  simpa [v] using h0.trans (sound 0 (by omega))

private theorem certificate_complete {U a e p K : ℕ} (hK : 2≤K) (ha : a<p) (hp : 1<p)
    (he : e<2^K) (hpK : p≤2^K) (hcap : 2^((K+1)*K)<U) : Certificate U a e p (a^e%p) := by
  let B := 2^K
  let s := fun i => a^(e/2^i)%p
  let T := packed B s (K+1)
  have hb : 0<B := Nat.two_pow_pos _
  have hsf (i : ℕ) : s i < B := (Nat.mod_lt _ (by omega : 0<p)).trans_le hpK
  have hBU : B<U := (Nat.pow_le_pow_right (by decide : 0<2) (by nlinarith : K≤(K+1)*K)).trans_lt hcap
  have hKU : K<U := Nat.lt_two_pow_self.trans hBU
  have hpU := hpK.trans_lt hBU
  have hTU : T<U := (packed_lt s (K+1) (fun i _ => hsf i)).trans_le (by
    simpa only [B,← pow_mul,Nat.mul_comm K (K+1)] using hcap.le)
  have hPU : p^3≤U := calc
    _ ≤ B^3 := Nat.pow_le_pow_left hpK _
    _ ≤ 2^((K+1)*K) := by
      dsimp [B]; rw [← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by nlinarith)
    _ ≤ U := hcap.le
  have hit (i : ℕ) (hi : i≤K) : 2^(i*K)<U := (Nat.pow_le_pow_right (by decide : 0<2)
    (Nat.mul_le_mul_right K (by omega : i≤K+1))).trans_lt hcap
  have hd (i : ℕ) (hi : i≤K) : s i=T/2^(i*K)%B := by
    have h := (packed_digit hb s (K+1) i (by omega) (fun v _ => hsf v)).symm
    simpa only [T,B,← pow_mul,Nat.mul_comm K i] using h
  refine ⟨K,hKU,K,hKU,T,hTU,B,hBU,B,hBU,rfl,rfl,he,hp,⟨hit 0 (by omega),hb,?_⟩,
    ⟨hit K le_rfl,hb,?_⟩,?_⟩
  · simpa [s] using hd 0 (by omega)
  · simpa [s,Nat.div_eq_of_lt he,Nat.mod_eq_of_lt hp] using hd K le_rfl
  · intro i _ hi
    let n := s (i+1)
    have hn : n<p := Nat.mod_lt _ (by omega)
    have hsq := Nat.mul_lt_mul_of_lt_of_le hn hn.le (by omega : 0<p)
    have hc := Nat.mul_lt_mul_of_lt_of_le hsq ha.le (by omega : 0<p)
    have hcu : n*n*a<U := hc.trans_le (by simpa [pow_succ] using hPU)
    have hsu : n*n<U := hsq.trans_le (by
      simpa only [pow_two] using (Nat.pow_le_pow_right (by omega : 0<p) (by decide : 2≤3)).trans hPU)
    refine ⟨i+1,by omega,s i,(hsf _).trans hBU,n,hn.trans hpU,n*n,hsu,n*n*a,hcu,rfl,
      ⟨hit i hi.le,hb,hd i hi.le⟩,⟨hit _ hi,hb,hd _ hi⟩,rfl,rfl,?_⟩
    have hh := power_step a e p i
    cases h : e.testBit i
    · exact Or.inr ⟨by simp,by omega,by simpa [s,n,h,pow_two] using hh⟩
    · exact Or.inl ⟨rfl,by omega,by simpa [s,n,h,pow_two] using hh⟩

/-- One fixed formula for variable-base, variable-exponent modular powers. -/
def formula {k : ℕ} (a e p b : Fin k) : Formula k :=
  program.syntaxF (fun n => if n=0 then a else if n=1 then e else if n=2 then p else b)

theorem formula_sound {k U : ℕ} (a e p b : Fin k) (env : Fin k → Fin U) :
    (formula a e p b).eval env = true → (env b).val=(env a).val^(env e).val%(env p).val := by
  intro h
  let σ := fun n : ℕ => if n=0 then a else if n=1 then e else if n=2 then p else b
  have m := (program.valid σ env).mp h
  exact certificate_sound ((program_holds U (fun n => (env (σ n)).val) (env p).isLt).mp m)

/-- With K bits per operand, (K+1)K bits suffice for the tableau.
The statement applies at every finite width satisfying the displayed bound. -/
theorem formula_correct {k U K : ℕ} (a e p b : Fin k) (env : Fin k → Fin U)
    (hK : 2≤K) (ha : (env a).val<(env p).val) (hp : 1<(env p).val)
    (he : (env e).val<2^K) (hpK : (env p).val≤2^K) (hcap : 2^((K+1)*K)<U) :
    (formula a e p b).eval env = true ↔ (env b).val=(env a).val^(env e).val%(env p).val := by
  refine ⟨formula_sound a e p b env,fun h => ?_⟩
  apply (program.valid _ _).mpr
  let σ := fun n : ℕ => if n=0 then a else if n=1 then e else if n=2 then p else b
  apply (program_holds U (fun n => (env (σ n)).val) (env p).isLt).mpr
  change Certificate U (env a).val (env e).val (env p).val (env b).val
  rw [h]
  exact certificate_complete hK ha hp he hpK hcap

end DiophantineNP.ShortPower
