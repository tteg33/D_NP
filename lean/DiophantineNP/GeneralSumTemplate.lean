import DiophantineNP.SmallSumTemplate
import Init.Data.BitVec.Bitblast

/-! # Fixed word addition for binary-matrix templates

A carry into position j exists exactly when some earlier position generates
a carry and every intervening position propagates it. Thus two query templates
can be added by a single fixed first-order expression independently of width. -/
namespace DiophantineNP.FiniteArithmeticGap
open Counting WidthFormula PrimeFormula

private def useAt {k : ℕ} (p : Template 1) (j : Fin k) : Template k :=
  rewriteMatrix (fun r c => .entry r c) p (fun _ => j)

private theorem useAt_eval {k U : ℕ} (p : Template 1) (j : Fin k) (e : Fin U → Fin U → Bool)
    (env : Fin k → Fin U) : (useAt p j).eval e env = p.eval e (fun _ => env j) :=
  rewriteMatrix_eval _ e e (by intros; rfl) _ _ _

private def tXor {k : ℕ} (a b : Template k) : Template k :=
  .disj (.conj a (.neg b)) (.conj (.neg a) b)

private theorem tXor_eval {k U : ℕ} (a b : Template k) (e : Fin U → Fin U → Bool)
    (env : Fin k → Fin U) : (tXor a b).eval e env = (a.eval e env ^^ b.eval e env) := by
  cases ha : a.eval e env <;> cases hb : b.eval e env <;> simp [tXor, Template.eval, ha, hb]

private theorem tNeg_true {k U : ℕ} (a : Template k) (e : Fin U → Fin U → Bool)
    (env : Fin k → Fin U) : (Template.neg a).eval e env = true ↔ ¬ a.eval e env = true := by
  simp [Template.eval]

private def CarryP (a b : ℕ → Bool) (j : ℕ) : Prop :=
  ∃ i < j, a i = true ∧ b i = true ∧ ∀ t, i<t → t<j → a t=true ∨ b t=true

private theorem carryP_succ (a b : ℕ → Bool) (j : ℕ) :
    CarryP a b (j+1) ↔ (a j=true ∧ b j=true) ∨ (CarryP a b j ∧ (a j=true ∨ b j=true)) := by
  constructor
  · rintro ⟨i,hi,ha,hb,h⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hij|rfl
    · exact Or.inr ⟨⟨i,hij,ha,hb,fun t h1 h2 => h t h1 (by omega)⟩,h j hij (by omega)⟩
    · exact Or.inl ⟨ha,hb⟩
  · rintro (⟨ha,hb⟩|⟨⟨i,hi,ha,hb,h⟩,hab⟩)
    · exact ⟨j,by omega,ha,hb,fun t ht h' => by omega⟩
    · refine ⟨i,by omega,ha,hb,fun t ht h' => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h') with hlt|rfl
      · exact h t ht hlt
      · exact hab

private theorem carryP_bitvec {U : ℕ} (a b : BitVec U) (j : ℕ) :
    BitVec.carry j a b false = true ↔ CarryP a.getLsbD b.getLsbD j := by
  induction j with
  | zero => simp [CarryP]
  | succ j ih =>
    rw [BitVec.carry_succ,carryP_succ,← ih]
    cases a.getLsbD j <;> cases b.getLsbD j <;> cases BitVec.carry j a b false <;> decide

private def carryT {k : ℕ} (a b : Template 1) (j : Fin k) : Template k :=
  .ex (.conj (fromFormula (ltF 0 j.succ)) (.conj (useAt a 0) (.conj (useAt b 0)
    (.neg (.ex (.conj (fromFormula (ltF (0 : Fin (k+1)).succ 0)) (.conj (fromFormula (ltF 0 (up2 j)))
       (.neg (.disj (useAt a 0) (useAt b 0))))))))))

def addWords (a b : Template 1) : Template 1 :=
  tXor a (tXor b (carryT a b 0))

/-- The low U bits are represented, including whenever the sum overflows. -/
theorem addWords_correct {U : ℕ} (a b : Template 1) (e : Fin U → Fin U → Bool)
    (x y : ℕ) (ha : ∀ i : Fin U, a.eval e (fun _ => i) = x.testBit i.val)
    (hb : ∀ i : Fin U, b.eval e (fun _ => i) = y.testBit i.val) (j : Fin U) :
    (addWords a b).eval e (fun _ => j) = (x+y).testBit j.val := by
  have castBit (x : ℕ) (t : Fin U) :
      (BitVec.ofNat U x).getLsbD t.val = x.testBit t.val := by
    simp only [BitVec.getLsbD_ofNat,decide_eq_true t.isLt,Bool.true_and]
  have hc : (carryT a b 0).eval e (fun _ : Fin 1 => j) =
      BitVec.carry j.val (BitVec.ofNat U x) (BitVec.ofNat U y) false := by
    apply Bool.eq_iff_iff.mpr
    rw [carryP_bitvec]
    simp only [carryT,Tex_true,Tconj_true,fromFormula_eval,ltF_true,tNeg_true,Tdisj_true,useAt_eval,
      Fin.cases_succ,Fin.cases_zero,ha,hb]
    constructor
    · rintro ⟨i,hi,hx,hy,h⟩
      refine ⟨i,hi,(castBit x i) ▸ hx,(castBit y i) ▸ hy,fun t ht tj => ?_⟩
      let v : Fin U := ⟨t,tj.trans j.isLt⟩
      have hv : x.testBit v.val = true ∨ y.testBit v.val = true := Classical.byContradiction fun hn => h ⟨v,ht,tj,hn⟩
      simpa only [← castBit x v,← castBit y v] using hv
    · rintro ⟨i,hi,hx,hy,ht⟩
      let v : Fin U := ⟨i,hi.trans j.isLt⟩
      refine ⟨v,hi,(castBit x v) ▸ hx,(castBit y v) ▸ hy,?_⟩
      rintro ⟨t,h1,h2,hn⟩
      exact hn (by simpa only [castBit x t,castBit y t] using ht t.val h1 h2)
  rw [addWords,tXor_eval,tXor_eval,hc,ha,hb]
  have hs := BitVec.getLsbD_add j.isLt (BitVec.ofNat U x) (BitVec.ofNat U y)
  simpa only [← BitVec.ofNat_add,castBit] using hs.symm

private def rowWord (n : ℕ) : Template 1 := .ex (.conj (fromFormula (isNat n 0)) (.entry 0 1))

private theorem rowWord_eval {U : ℕ} (f : ℕ → ℕ) (n : ℕ) (j : Fin U) :
    (rowWord n).eval (fun r c => (f r.val).testBit c.val) (fun _ => j) =
      (if n<U then f n else 0).testBit j.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowWord,Tex_true,Tconj_true,fromFormula_eval,isNat_spec,Tentry_eval,Fin.cases_zero]
  change (∃r : Fin U, r.val=n ∧ (f r.val).testBit j.val=true) ↔ _
  by_cases h : n<U
  · rw [if_pos h]
    constructor
    · rintro ⟨r,hr,hb⟩
      simpa [hr] using hb
    · intro hb; exact ⟨⟨n,h⟩,rfl,hb⟩
  · rw [if_neg h]
    simp only [Nat.zero_testBit,Bool.false_eq_true,iff_false]
    rintro ⟨r,hr,_⟩
    exact h (hr ▸ r.isLt)

/-- The depth of the binary addition tree is logarithmic in the number
of its leaves. This keeps the finite query templates reasonably sized. -/
private def sumTree (leaf : ℕ → Template 1) : (depth start : ℕ) → Template 1
  | 0, start => leaf start
  | d+1, start => addWords (sumTree leaf d start) (sumTree leaf d (start+2^d))

private theorem prefix_mono (f : ℕ → ℕ) {i j : ℕ} (h : i≤j) :
    Readout.prefixSum f i ≤ Readout.prefixSum f j := by
  induction j,h using Nat.le_induction with
  | base => rfl
  | succ j _ ih => exact ih.trans (Nat.le_add_right ..)

private theorem sumTree_eval {U : ℕ} (e : Fin U → Fin U → Bool) (leaf : ℕ → Template 1)
    (f : ℕ → ℕ) (d a : ℕ)
    (h : ∀ n, a≤n → n<a+2^d → ∀ i : Fin U, (leaf n).eval e (fun _ => i) = (f n).testBit i.val)
    (j : Fin U) : (sumTree leaf d a).eval e (fun _ => j) =
      (Readout.prefixSum f (a+2^d)-Readout.prefixSum f a).testBit j.val := by
  induction d generalizing a j with
  | zero =>
    rw [sumTree, h a (by omega) (by norm_num)]
    simp [Readout.prefixSum]
  | succ d ih =>
    have hend : a+2^d+2^d=a+2^(d+1) := by rw [pow_succ]; omega
    rw [sumTree,addWords_correct _ _ _ _ _ (ih a (fun n h1 h2 => h n h1 (by omega)))
      (ih (a+2^d) (fun n h1 h2 => h n (by omega) (by omega)))]
    congr 1
    have h1 := prefix_mono f (Nat.le_add_right a (2^d))
    have h2 := prefix_mono f (Nat.le_add_right (a+2^d) (2^d))
    rw [hend] at *
    omega

private def firstRows := sumTree rowWord 5 0

private theorem firstRows_correct {U : ℕ} (f : ℕ → ℕ) (j : Fin U) :
    firstRows.eval (fun r c => (f r.val).testBit c.val) (fun _ => j) =
      (Readout.prefixSum (fun i => if i<U then f i else 0) 32).testBit j.val := by
  simpa only [firstRows, Nat.zero_add, Readout.prefixSum, Nat.sub_zero] using
    sumTree_eval _ rowWord (fun i => if i<U then f i else 0) 5 0 (fun n _ _ => rowWord_eval f n) j

/-- Eight blocks cover a word of any width. -/
private def blockSize (U : ℕ) := (U+7)/8

private def mulConst {k : ℕ} (n : ℕ) (x z : Fin k) : Formula k :=
  .ex (andF (isNat n 0) (mulF 0 x.succ z.succ))

private theorem mulConst_true {k U : ℕ} (n : ℕ) (hn : n<U) (x z : Fin k) (env : Fin k → Fin U) :
    (mulConst n x z).eval env = true ↔ n*(env x).val=(env z).val := by
  simp only [mulConst,exists_true,andF_spec,isNat_spec,mulF_spec,Fin.cases_zero,Fin.cases_succ]
  constructor
  · rintro ⟨a,ha,h⟩; rwa [ha] at h
  · intro h; exact ⟨⟨n,hn⟩,rfl,h⟩

private def overEight {k : ℕ} (x : Fin k) : Formula k := notF (.ex (mulConst 8 x.succ 0))

private theorem overEight_true {k U : ℕ} (hU : 8 < U) (x : Fin k) (env : Fin k → Fin U) :
    (overEight x).eval env = true ↔ U ≤ 8*(env x).val := by
  simp only [overEight,notF_spec,exists_true,mulConst_true _ hU,Fin.cases_succ,Fin.cases_zero]
  constructor
  · intro h
    by_contra! hn
    exact h ⟨⟨_,hn⟩,rfl⟩
  · rintro h ⟨v,hv⟩
    have := v.isLt
    omega

private def widthT {k : ℕ} (x : Fin k) : Formula k :=
  andF (overEight x) (notF (.ex (andF (overEight 0) (ltF 0 x.succ))))

private theorem widthT_true {k U : ℕ} (hU : 8 < U) (x : Fin k) (env : Fin k → Fin U) :
    (widthT x).eval env = true ↔ (env x).val=blockSize U := by
  simp only [widthT,notF_spec,andF_spec,exists_true,overEight_true hU,ltF_true,Fin.cases_succ,Fin.cases_zero,blockSize]
  constructor
  · rintro ⟨h,hn⟩
    by_contra hne
    exact hn ⟨⟨(U+7)/8,by omega⟩,by dsimp; omega,by dsimp; omega⟩
  · rintro h; exact ⟨by omega,fun ⟨v,hv,hl⟩ => by omega⟩

private def offset {k : ℕ} (n : ℕ) (x : Fin k) : Formula k :=
  .ex (andF (widthT 0) (mulConst n 0 x.succ))

private theorem offset_true {k U : ℕ} (hU : 8<U) (n : ℕ) (hn : n<U) (x : Fin k) (env : Fin k → Fin U) :
    (offset n x).eval env = true ↔ n*blockSize U=(env x).val := by
  simp only [offset,exists_true,andF_spec,widthT_true hU,mulConst_true _ hn,Fin.cases_zero,Fin.cases_succ]
  constructor
  · rintro ⟨w,hw,h⟩; rwa [hw] at h
  · intro h; exact ⟨⟨_,by omega⟩,rfl,h⟩

private def chunk (x n w : ℕ) := x/2^(n*w)%2^w

private def belowWidth {k : ℕ} (x : Fin k) : Formula k :=
  .ex (andF (widthT 0) (ltF x.succ 0))

private theorem belowWidth_true {k U : ℕ} (hU : 8<U) (x : Fin k) (env : Fin k → Fin U) :
    (belowWidth x).eval env = true ↔ (env x).val < blockSize U := by
  simp only [belowWidth,exists_true,andF_spec,widthT_true hU,ltF_true,Fin.cases_zero,Fin.cases_succ]
  constructor
  · rintro ⟨w,hw,h⟩; rwa [hw] at h
  · intro h; exact ⟨⟨_,by omega⟩,rfl,h⟩

private def chunkEntry (n : ℕ) {k : ℕ} (r c : Fin k) : Template k :=
  .conj (fromFormula (belowWidth c))
    (.ex (.ex (.conj (fromFormula (offset n (0 : Fin (k+1)).succ))
      (.conj (fromFormula (addF (0 : Fin (k+1)).succ (up2 c) 0)) (.entry (up2 r) 0)))))

private theorem chunkEntry_eval {U k : ℕ} (f : ℕ → ℕ) (fits : ∀ t<U, f t<2^U) (hU : 8<U) (n : ℕ) (hn : n<U)
    (r c : Fin k) (env : Fin k → Fin U) :
    (chunkEntry n r c).eval (fun r c => (f r.val).testBit c.val) env =
      (chunk (f (env r).val) n (blockSize U)).testBit (env c).val := by
  apply Bool.eq_iff_iff.mpr
  simp only [chunkEntry,Tconj_true,fromFormula_eval,belowWidth_true hU,Tex_true,offset_true hU _ hn,
    addF_spec,Tentry_eval,Fin.cases_zero,Fin.cases_succ,chunk,Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hl,t,b,ht,hb,h⟩
    exact ⟨hl,by rwa [show (env c).val + n*blockSize U = b.val by omega]⟩
  · rintro ⟨hl,h⟩
    have hu : (env c).val+n*blockSize U<U := by
      by_contra! hU'
      have := (Nat.ge_two_pow_of_testBit h).trans_lt (fits _ (env r).isLt)
      have := Nat.pow_le_pow_right (by decide : 0<2) hU'
      omega
    exact ⟨hl,⟨n*blockSize U,by omega⟩,⟨(env c).val+n*blockSize U,hu⟩,rfl,Nat.add_comm _ _,h⟩

private theorem block_bound {U : ℕ} (hU : 32≤U) : U * 2^(blockSize U) ≤ 2^(U/2) := by
  have hw : 3≤blockSize U := by unfold blockSize; omega
  have hscale (m : ℕ) (hm : 3≤m) : 8*m≤(2:ℕ)^(m+m) := by
    induction m,hm using Nat.le_induction with
    | base => decide
    | succ m hm ih =>
      rw [show m+1+(m+1)=m+m+2 by omega,pow_add]
      norm_num
      omega
  have h1 : U≤ 2^(blockSize U + blockSize U) := le_trans (by unfold blockSize; omega : U≤8*blockSize U) (hscale _ hw)
  have h2 : blockSize U + blockSize U + blockSize U ≤ U/2 := by unfold blockSize; omega
  exact (Nat.mul_le_mul_right _ h1).trans (by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) h2)

private theorem chunkSum_fits {U : ℕ} (hU : 32≤U) (f : ℕ → ℕ) (n : ℕ) :
    Readout.prefixSum (fun t => chunk (f t) n (blockSize U)) U < 2^(U/2) := by
  have hb : ∀ m, Readout.prefixSum (fun t => chunk (f t) n (blockSize U)) m ≤ m*(2^(blockSize U)-1) := by
    intro m; induction m with
    | zero => simp [Readout.prefixSum]
    | succ m ih =>
      have hx := Nat.mod_lt (f m / 2^(n*blockSize U)) (Nat.two_pow_pos (blockSize U))
      rw [Readout.prefixSum,Nat.succ_mul]
      exact Nat.add_le_add ih (show chunk (f m) n (blockSize U)≤2^(blockSize U)-1 by unfold chunk; omega)
  exact (hb U).trans_lt (lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left (by have := Nat.two_pow_pos (blockSize U); omega) (by omega)) (block_bound hU))

private def chunkSum (P : ProductTemplate) (n : ℕ) : Template 1 :=
  rewriteMatrix (@chunkEntry n) P.smallSum id

private theorem chunkSum_eval {U : ℕ} (hU : 32≤U) (f : ℕ → ℕ) (fits : ∀ t<U,f t<2^U)
    (P : ProductTemplate) (n : ℕ) (hn : n<U) (j : Fin U) :
    (chunkSum P n).eval (fun r c => (f r.val).testBit c.val) (fun _ => j) =
      (Readout.prefixSum (fun i => chunk (f i) n (blockSize U)) U).testBit j.val := by
  unfold chunkSum
  rw [rewriteMatrix_eval (@chunkEntry n) _ (fun r c : Fin U => (chunk (f r.val) n (blockSize U)).testBit c.val)
    (fun r c env => chunkEntry_eval f fits (by omega) n hn r c env)]
  exact P.smallSum_correct _ (by omega) (chunkSum_fits hU f n) j

private def shiftWord (n : ℕ) (p : Template 1) : Template 1 :=
  .ex (.ex (.conj (fromFormula (offset n 1)) (.conj (fromFormula (addF 1 0 2)) (useAt p 0))))

private theorem shiftWord_eval {U : ℕ} (hU : 8<U) (n : ℕ) (hn : n<U) (p : Template 1)
    (e : Fin U → Fin U → Bool) (x : ℕ) (hp : ∀ i : Fin U, p.eval e (fun _ => i) = x.testBit i.val) (j : Fin U) :
    (shiftWord n p).eval e (fun _ => j) = (2^(n*blockSize U)*x).testBit j.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [shiftWord,Tex_true,Tconj_true,fromFormula_eval,offset_true hU _ hn,addF_spec,useAt_eval,hp,
    Nat.testBit_two_pow_mul,Bool.and_eq_true,decide_eq_true_eq]
  change (∃d v : Fin U, n*blockSize U=d.val ∧ d.val+v.val=j.val ∧ x.testBit v.val=true) ↔ _
  constructor
  · rintro ⟨d,v,hd,hv,h⟩
    exact ⟨by omega, by rwa [show j.val-n*blockSize U=v.val by omega]⟩
  · rintro ⟨hle,h⟩
    exact ⟨⟨_,hle.trans_lt j.isLt⟩,⟨j.val-n*blockSize U,by have := j.isLt; omega⟩,rfl,by dsimp; omega,h⟩

private def blocks (P : ProductTemplate) : Template 1 :=
  sumTree (fun n => shiftWord n (chunkSum P n)) 3 0

private theorem blocks_eval {U : ℕ} (hU : 32≤U) (f : ℕ → ℕ) (fits : ∀ t<U, f t<2^U)
    (P : ProductTemplate) (j : Fin U) :
    (blocks P).eval (fun r c => (f r.val).testBit c.val) (fun _ => j) =
      (Readout.prefixSum (fun k => 2^(k*blockSize U)*Readout.prefixSum (fun i => chunk (f i) k (blockSize U)) U) 8).testBit j.val := by
  let g := fun k => 2^(k*blockSize U)*Readout.prefixSum (fun i => chunk (f i) k (blockSize U)) U
  apply Eq.trans (sumTree_eval _ _ g 3 0 (fun n _ hn => ?_) j) (by rfl)
  have hu : n<U := by norm_num at hn; omega
  exact shiftWord_eval (by omega) _ hu _ _ _ (chunkSum_eval hU f fits P n hu)

private theorem blocks_arithmetic (w : ℕ) (f : ℕ → ℕ) (v n : ℕ) :
    Readout.prefixSum (fun k => 2^(k*w)*Readout.prefixSum (fun i => chunk (f i) k w) v) n =
    Readout.prefixSum (fun i => f i % 2^(n*w)) v := by
  induction n with
  | zero =>
    simp only [Readout.prefixSum,Nat.zero_mul,pow_zero,Nat.mod_one]
    induction v with
    | zero => rfl
    | succ v ih => simpa [Readout.prefixSum] using ih
  | succ n ih =>
    rw [Readout.prefixSum,ih]
    clear ih
    induction v with
    | zero => simp [Readout.prefixSum]
    | succ v ih =>
      simp only [Readout.prefixSum,Nat.mul_add] at ih ⊢
      have step : f v % 2^((n+1)*w) = f v % 2^(n*w)+2^(n*w)*(f v/2^(n*w)%2^w) := by
        rw [Nat.succ_mul,pow_add,Nat.mod_mul]
      rw [step]
      unfold chunk at *
      omega

private theorem blocks_all {U : ℕ} (f : ℕ → ℕ) (fits : ∀ t<U, f t<2^U) :
    Readout.prefixSum (fun k => 2^(k*blockSize U)*Readout.prefixSum (fun i => chunk (f i) k (blockSize U)) U) 8 =
      Readout.prefixSum f U := by
  rw [blocks_arithmetic]
  have hf := fun (t : ℕ) (ht : t<U) => Nat.mod_eq_of_lt ((fits t ht).trans_le
    (Nat.pow_le_pow_right (by decide : 0<2) (show U≤8*blockSize U by unfold blockSize; omega)))
  have aux (n : ℕ) (hn : n≤U) : Readout.prefixSum (fun i => f i%2^(8*blockSize U)) n = Readout.prefixSum f n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [Readout.prefixSum,ih (by omega),hf n (by omega)]
  exact aux U le_rfl

/-- An arbitrary iterated matrix sum requires only the product template.
For U at least 32 we collect eight shifted block sums. For smaller universes
a fixed fold over the first 32 rows suffices. -/
def ProductTemplate.fullSum (P : ProductTemplate) : Template 1 :=
  let large := fromFormula (.ex (isNat 31 0) : Formula 1)
  .disj (.conj large (blocks P)) (.conj (.neg large) firstRows)

theorem ProductTemplate.fullSum_correct (P : ProductTemplate) {U : ℕ} (f : ℕ → ℕ)
    (fits : ∀ t<U, f t<2^U) (j : Fin U) :
    P.fullSum.eval (fun r c => (f r.val).testBit c.val) (fun _ => j) =
      (Readout.prefixSum f U).testBit j.val := by
  have large (env : Fin 1 → Fin U) :
      (Formula.ex (isNat 31 0) : Formula 1).eval env = decide (32≤U) := by
    apply Bool.eq_iff_iff.mpr
    rw [exists_true,decide_eq_true_eq]
    simp only [isNat_spec,Fin.cases_zero]
    constructor
    · rintro ⟨v,h⟩; have := v.isLt; omega
    · intro h; exact ⟨⟨31,by omega⟩,rfl⟩
  by_cases h : 32≤U
  · simp only [ProductTemplate.fullSum, Template.eval.eq_5,Template.eval.eq_6,Template.eval.eq_4,
      fromFormula_eval,large,decide_eq_true h,Bool.true_and,Bool.not_true,Bool.false_and,Bool.or_false]
    rw [blocks_eval h f fits P,blocks_all f fits]
  · simp only [ProductTemplate.fullSum, Template.eval.eq_5,Template.eval.eq_6,Template.eval.eq_4,
      fromFormula_eval,large,decide_eq_false h,Bool.false_and,Bool.not_false,Bool.true_and,Bool.false_or]
    rw [firstRows_correct,sum_pad f (by omega : U≤32)]

def ProductTemplate.toIterated (P : ProductTemplate) : IteratedArithmetic where
  product := P.product
  sum := P.fullSum
  product_correct := P.product_correct
  sum_correct := P.fullSum_correct

end DiophantineNP.FiniteArithmeticGap
