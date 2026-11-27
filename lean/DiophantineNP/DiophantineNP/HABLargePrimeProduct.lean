import DiophantineNP.HABPowerReduction
import DiophantineNP.HABLargePrimeRow

/-! # Products of arbitrarily many represented residues modulo a prime

The row relation supplies a residue for each active row. A primitive root
exists by finite-field arithmetic. The formula need only guess a nonzero
base that covers those rows; least discrete logarithms make the summands
unique even when the guessed base is not a generator. -/
namespace DiophantineNP.HABLargePrimeProduct
open Counting WidthFormula PrimeFormula FiniteArithmeticGap HABPowerReduction Finset

private def numeral {k : ℕ} (n : ℕ) (x : Fin k) : Template k := fromFormula (isNat n x)
private def less {k : ℕ} (x y : Fin k) : Template k := fromFormula (ltF x y)

private theorem num_true {k U : ℕ} (n : ℕ) (x : Fin k) (A : HAB.Matrix U) (e : Fin k → Fin U) :
    (numeral n x).eval A e=true ↔ (e x).val=n := by rw [numeral,fromFormula_eval,isNat_spec]
private theorem less_true {k U : ℕ} (x y : Fin k) (A : HAB.Matrix U) (e : Fin k → Fin U) :
    (less x y).eval A e=true ↔ (e x).val<(e y).val := by rw [less,fromFormula_eval,ltF_true]
private theorem neg_true {k U : ℕ} (q : Template k) (A : HAB.Matrix U) (e : Fin k → Fin U) :
    q.neg.eval A e=true ↔ ¬q.eval A e=true := by simp [Template.eval]

private noncomputable def power (P : ShortProducts) {k : ℕ} (g j p b : Fin k) : Template k :=
  ((HABPowerReduction.source P).rename ![p,g,j,b]).translate

private theorem power_true (P : ShortProducts) {k U : ℕ} (g j p b : Fin k) (A : HAB.Matrix U)
    (e : Fin k → Fin U) (prime : (e p).val.Prime) (hg : (e g).val<(e p).val) :
    (power P g j p b).eval A e=true ↔ (e g).val^(e j).val%(e p).val=(e b).val := by
  rw [power,HAB.Form.translate_correct,HAB.Form.rename_correct]
  have he : e ∘ ![p,g,j,b]=![e p,e g,e j,e b] := by funext i; fin_cases i <;> rfl
  rw [he,HABPowerReduction.source_correct P A _ _ _ _ prime hg]

private noncomputable def hit (P : ShortProducts) {k : ℕ} (d g j p : Fin k) : Template k :=
  .ex (.conj (.entry d.succ 0) (power P g.succ j.succ p.succ 0))

private theorem hit_true (P : ShortProducts) {k U : ℕ} (d g j p : Fin k) (A : HAB.Matrix U)
    (e : Fin k → Fin U) (prime : (e p).val.Prime) (hg : (e g).val<(e p).val)
    {x : ℕ} (hx : x<(e p).val) (row : ∀ y : Fin U, A (e d) y=true ↔ y.val=x) :
    (hit P d g j p).eval A e=true ↔ (e g).val^(e j).val%(e p).val=x := by
  rw [hit,Tex_true]
  simp only [Tconj_true,Tentry_eval,Fin.cases_succ,Fin.cases_zero,row]
  let E (y : Fin U) : Fin (k+1) → Fin U := Fin.cases y e
  have pow (y : Fin U) := power_true P g.succ j.succ p.succ 0 A (E y) prime hg
  exact ⟨fun ⟨y,hy,h⟩ => ((pow y).mp h).trans hy,
    fun h => ⟨⟨_,hx.trans (e p).isLt⟩,rfl,(pow _).mpr h⟩⟩

private def HasLog (g p x : ℕ) := ∃ j<p, g^j%p=x

private noncomputable def logValue (g p x : ℕ) := by
  classical
  exact if h : HasLog g p x then Nat.find h else 0

private theorem log_spec {g p x : ℕ} (has : HasLog g p x) :
    logValue g p x < p ∧ g^(logValue g p x)%p=x ∧
      ∀ j, j<p → g^j%p=x → logValue g p x≤j := by
  classical
  simp only [logValue,dif_pos has]
  exact ⟨(Nat.find_spec has).1,(Nat.find_spec has).2,fun j hj eq => Nat.find_min' has ⟨hj,eq⟩⟩

private noncomputable def has (P : ShortProducts) {k : ℕ} (d g p : Fin k) : Template k :=
  .ex (.conj (less 0 p.succ) (hit P d.succ g.succ 0 p.succ))

private theorem has_true (P : ShortProducts) {k U : ℕ} (d g p : Fin k) (A : HAB.Matrix U)
    (e : Fin k → Fin U) (prime : (e p).val.Prime) (hg : (e g).val<(e p).val)
    {x : ℕ} (hx : x<(e p).val) (row : ∀ y : Fin U, A (e d) y=true ↔ y.val=x) :
    (has P d g p).eval A e=true ↔ HasLog (e g).val (e p).val x := by
  rw [has,Tex_true]
  simp only [Tconj_true,less_true,Fin.cases_succ,Fin.cases_zero]
  let E (y : Fin U) : Fin (k+1) → Fin U := Fin.cases y e
  have chk (j : Fin U) := hit_true P d.succ g.succ 0 p.succ A (E j) prime hg hx row
  exact ⟨fun ⟨j,hj,h⟩ => ⟨j,hj,(chk j).mp h⟩,
    fun ⟨j,hj,h⟩ => ⟨⟨j,hj.trans (e p).isLt⟩,hj,(chk _).mpr h⟩⟩

private noncomputable def first (P : ShortProducts) {k : ℕ} (d g j p : Fin k) : Template k :=
  .conj (less j p) <| .conj (hit P d g j p) <|
    .neg (.ex (.conj (less 0 j.succ) (hit P d.succ g.succ 0 p.succ)))

private theorem first_true (P : ShortProducts) {k U : ℕ} (d g j p : Fin k) (A : HAB.Matrix U)
    (e : Fin k → Fin U) (prime : (e p).val.Prime) (hg : (e g).val<(e p).val)
    {x : ℕ} (hx : x<(e p).val) (row : ∀ y : Fin U, A (e d) y=true ↔ y.val=x)
    (cov : HasLog (e g).val (e p).val x) :
    (first P d g j p).eval A e=true ↔ (e j).val=logValue (e g).val (e p).val x := by
  simp only [first,Tconj_true,less_true,neg_true,Tex_true,Fin.cases_zero,Fin.cases_succ]
  rw [hit_true P d g j p A e prime hg hx row]
  let E (y : Fin U) : Fin (k+1) → Fin U := Fin.cases y e
  have chk (s : Fin U) := hit_true P d.succ g.succ 0 p.succ A (E s) prime hg hx row
  obtain ⟨ltp,eq,least⟩ := log_spec cov
  constructor
  · rintro ⟨lj,ej,minimal⟩
    apply Nat.le_antisymm _ (least _ lj ej)
    apply Nat.le_of_not_gt
    intro lt
    exact minimal ⟨⟨_,ltp.trans (e p).isLt⟩,lt,(chk _).mpr eq⟩
  · intro eqa
    refine ⟨eqa ▸ ltp,eqa ▸ eq,?_⟩
    rintro ⟨s,lt,earlier⟩
    have h := least s ((lt.trans_le eqa.le).trans ltp) ((chk s).mp earlier)
    omega

private noncomputable def covered (P : ShortProducts) {k : ℕ} (m g p : Fin k) : Template k :=
  .neg (.ex (.conj (less 0 m.succ) (.neg (has P 0 g.succ p.succ))))

private theorem covered_true (P : ShortProducts) {k U : ℕ} (m g p : Fin k) (A : HAB.Matrix U)
    (e : Fin k → Fin U) (prime : (e p).val.Prime) (hg : (e g).val<(e p).val) (f : ℕ → ℕ)
    (values : ∀ i<(e m).val,f i<(e p).val)
    (rows : ∀ d y : Fin U, d.val<(e m).val → (A d y=true ↔ y.val=f d.val)) :
    (covered P m g p).eval A e=true ↔ ∀ i<(e m).val, HasLog (e g).val (e p).val (f i) := by
  simp only [covered,neg_true,Tex_true,Tconj_true,less_true,Fin.cases_succ,Fin.cases_zero,
    not_exists,not_and,not_not]
  let E (y : Fin U) : Fin (k+1) → Fin U := Fin.cases y e
  have chk (d : Fin U) (act : d.val<(e m).val) :=
    has_true P 0 g.succ p.succ A (E d) prime hg (values d act) (fun y => rows d y act)
  exact ⟨fun good i act => (chk ⟨i,act.trans (e m).isLt⟩ act).mp (good _ act),
    fun good d act => (chk d act).mpr (good _ act)⟩

private noncomputable def logBits (P : ShortProducts) {k : ℕ} (m g p : Fin k) : Template (k+2) :=
  .conj (less 1 m.succ.succ) (.ex (.conj (first P 2 g.succ.succ.succ 0 p.succ.succ.succ) (.bit 0 1)))

private theorem logBits_correct (P : ShortProducts) {k U : ℕ} (m g p : Fin k) (A : HAB.Matrix U)
    (e : Fin k → Fin U) (prime : (e p).val.Prime) (hg : (e g).val<(e p).val) (f : ℕ → ℕ)
    (values : ∀ i<(e m).val,f i<(e p).val)
    (rows : ∀ d y : Fin U,d.val<(e m).val → (A d y=true ↔ y.val=f d.val))
    (cov : ∀ i<(e m).val, HasLog (e g).val (e p).val (f i)) (d j : Fin U) :
    (logBits P m g p).eval A (extend j d e)=
      (if d.val<(e m).val then logValue (e g).val (e p).val (f d.val) else 0).testBit j.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [logBits,Tconj_true,less_true,Tex_true]
  by_cases act : d.val<(e m).val
  · let E (v : Fin U) : Fin (k+3) → Fin U := Fin.cases v (extend j d e)
    have chk (v : Fin U) := first_true P 2 g.succ.succ.succ 0 p.succ.succ.succ A
      (E v) prime hg (values d act) (fun y => rows d y act) (cov d act)
    rw [if_pos act]
    refine ⟨fun ⟨_,v,hv,bit⟩ => ?_,fun bit => ?_⟩
    · change v.val.testBit j.val=true at bit
      have veq : v.val=logValue (e g).val (e p).val (f d.val) := (chk v).mp hv
      rwa [←veq]
    · have lim := (log_spec (cov d act)).1.trans (e p).isLt
      exact ⟨act,⟨_,lim⟩,(chk _).mpr rfl,bit⟩
  · change (d.val<(e m).val ∧ _) ↔ _
    simp [act]

private theorem pad_sum {m U : ℕ} (hm : m≤U) (f : ℕ → ℕ) :
    (∑ i ∈ range U,if i<m then f i else 0)=∑ i ∈ range m,f i := by
  simp only [←sum_filter]
  congr 1
  ext i
  simp only [mem_filter,mem_range,and_iff_right_iff_imp]
  omega

private theorem residues (g p : ℕ) (f l : ℕ → ℕ) (m : ℕ) (h : ∀ i<m,g^(l i)%p=f i) :
    g^(∑ i ∈ range m,l i) ≡ (∏ i ∈ range m,f i) [MOD p] := by
  induction m with
  | zero => simp [Nat.ModEq]
  | succ m ih =>
    rw [sum_range_succ,prod_range_succ,pow_add]
    exact (ih (fun i hi => h i (by omega))).mul ((Nat.mod_modEq _ _).symm.trans (h m (by omega) ▸ Nat.ModEq.refl _))

private def zeroRow {k : ℕ} (m : Fin k) : Template k :=
  .ex (.conj (less 0 m.succ) (.ex (.conj (numeral 0 0) (.entry 1 0))))

private theorem zero_true {k U : ℕ} (m : Fin k) (A : HAB.Matrix U) (e : Fin k → Fin U)
    (f : ℕ → ℕ) (rows : ∀ d y : Fin U,d.val<(e m).val → (A d y=true ↔ y.val=f d.val)) :
    (zeroRow m).eval A e=true ↔ ∃ i<(e m).val,f i=0 := by
  simp only [zeroRow,Tex_true,Tconj_true,less_true,num_true,Tentry_eval,Fin.cases_succ,Fin.cases_zero]
  constructor
  · rintro ⟨d,act,y,zero,hit⟩
    exact ⟨d,act,((rows d y act).mp hit).symm.trans zero⟩
  · rintro ⟨i,act,z⟩
    let d : Fin U := ⟨i,act.trans (e m).isLt⟩
    let y : Fin U := ⟨0,(Nat.zero_le i).trans_lt d.isLt⟩
    exact ⟨d,act,y,rfl,(rows d y act).mpr z.symm⟩

private noncomputable def result (P : ShortProducts) {k : ℕ} (m g p b : Fin k) : Template k :=
  .ex (.conj (HABIndexSum.formula 0 (logBits P m.succ g.succ p.succ)) (power P g.succ 0 p.succ b.succ))

private theorem result_true (P : ShortProducts) {k U : ℕ} (m g p b : Fin k) (A : HAB.Matrix U)
    (e : Fin k → Fin U) (prime : (e p).val.Prime) (hg : (e g).val<(e p).val) (f : ℕ → ℕ)
    (values : ∀ i<(e m).val,f i<(e p).val)
    (rows : ∀ d y : Fin U,d.val<(e m).val → (A d y=true ↔ y.val=f d.val))
    (cov : ∀ i<(e m).val, HasLog (e g).val (e p).val (f i)) (room : (e m).val*(e p).val<U) :
    (result P m g p b).eval A e=true ↔ (∏ i ∈ range (e m).val,f i)%(e p).val=(e b).val := by
  let l (i : ℕ) := logValue (e g).val (e p).val (f i)
  let v (i : ℕ) := if i<(e m).val then l i else 0
  let s := ∑ i ∈ range (e m).val,l i
  have pad : (∑ i ∈ range U,v i)=s := pad_sum (e m).isLt.le l
  have fits : s<U := calc
    _ ≤ ∑ _i ∈ range (e m).val,(e p).val := sum_le_sum fun i hi => (log_spec (cov i (mem_range.mp hi))).1.le
    _ = (e m).val*(e p).val := by simp
    _ < U := room
  have exactSum (w : Fin U) :
      (HABIndexSum.formula 0 (logBits P m.succ g.succ p.succ)).eval A (Fin.cases w e)=true ↔ w.val=s := by
    let E : Fin (k+1) → Fin U := Fin.cases w e
    have bit := logBits_correct P m.succ g.succ p.succ A E prime hg f values rows cov
    exact (HABIndexSum.formula_correct 0 _ A E v bit (pad ▸ fits)).trans (by rw [pad]; rfl)
  let E (y : Fin U) : Fin (k+1) → Fin U := Fin.cases y e
  have chk (w : Fin U) := power_true P g.succ 0 p.succ b.succ A
    (E w) prime hg
  have cong : (e g).val^s ≡ ∏ i ∈ range (e m).val,f i [MOD (e p).val] :=
    residues _ _ f l _ (fun i hi => (log_spec (cov i hi)).2.1)
  rw [result,Tex_true]
  simp only [Tconj_true,exactSum]
  constructor
  · rintro ⟨w,hw,hit⟩
    have h : (e g).val^w.val%(e p).val=(e b).val := (chk w).mp hit
    exact Eq.trans cong.symm (by rwa [hw] at h)
  · intro final
    exact ⟨⟨s,fits⟩,rfl,(chk _).mpr (Eq.trans cong final)⟩

/-- A residue graph is queried at (row, proposed residue). Free slots are
the row count, prime modulus and proposed answer. -/
noncomputable def formula (P : ShortProducts) : Template 3 :=
  .disj (.conj (zeroRow 0) (numeral 0 2))
    (.ex (.conj (.neg (numeral 0 0)) (.conj (less 0 2) (.conj (covered P 1 0 2) (result P 1 0 2 3)))))

theorem formula_correct (P : ShortProducts) {U : ℕ} (A : HAB.Matrix U) (m p b : Fin U)
    (f : ℕ → ℕ) (prime : p.val.Prime) (values : ∀ i<m.val,f i<p.val)
    (rows : ∀ d y : Fin U,d.val<m.val → (A d y=true ↔ y.val=f d.val)) (room : m.val*p.val<U) :
    (formula P).eval A ![m,p,b]=true ↔ (∏ i ∈ range m.val,f i)%p.val=b.val := by
  let e : Fin 3 → Fin U := ![m,p,b]
  let E (g : Fin U) : Fin 4 → Fin U := Fin.cases g e
  have z := zero_true 0 A e f rows
  have cov (g : Fin U) (hg : g.val<p.val) := covered_true P 1 0 2 A (E g) prime hg f values rows
  have chk (g : Fin U) (hg : g.val<p.val) (ok : ∀ i<m.val,HasLog g.val p.val (f i)) :=
    result_true P 1 0 2 3 A (E g) prime hg f values rows ok room
  change (formula P).eval A e=true ↔ _
  simp only [formula,Tdisj_true,Tconj_true,Tex_true,neg_true,num_true,less_true,z]
  change ((∃ i<m.val,f i=0) ∧ b.val=0 ∨ ∃ g : Fin U, g.val≠0 ∧ g.val<p.val ∧
    (covered P 1 0 2).eval A (E g)=true ∧ (result P 1 0 2 3).eval A (E g)=true) ↔ _
  have vanishes (h : ∃ i<m.val,f i=0) : (∏ i ∈ range m.val,f i)%p.val=0 := by
    obtain ⟨i,hi,zero⟩ := h; rw [prod_eq_zero (mem_range.mpr hi) zero,Nat.zero_mod]
  constructor
  · rintro (⟨h,hb⟩|⟨g,_,lt,c,h⟩)
    · exact (vanishes h).trans hb.symm
    · exact (chk g lt ((cov g lt).mp c)).mp h
  · intro eq
    by_cases hz : ∃ i<m.val,f i=0
    · exact Or.inl ⟨hz,eq.symm.trans (vanishes hz)⟩
    obtain ⟨g,pos,lt,gen⟩ := ShortResidue.primitive_root prime
    let G : Fin U := ⟨g,lt.trans p.isLt⟩
    have allLogs (i : ℕ) (act : i<m.val) : HasLog g p.val (f i) := by
      have posf := Nat.pos_of_ne_zero (fun h => hz ⟨i,act,h⟩)
      obtain ⟨j,hj,he⟩ := gen _ posf (values i act)
      exact ⟨j,hj.trans_le (Nat.sub_le ..),he⟩
    exact Or.inr ⟨G,pos.ne',lt,(cov G lt).mpr allLogs,(chk G lt allLogs).mpr eq⟩

/-- Substitute a parameterized residue graph into the fixed discrete-log
product formula. The graph's prefix slots are the candidate value and row. -/
noncomputable def fromRows (P : ShortProducts) {n : ℕ} (m p b : Fin n)
    (graph : Template (n+2)) : Template n :=
  HABMatrix.bind graph (formula P) id ![m,p,b]

theorem fromRows_correct (P : ShortProducts) {n U : ℕ} (m p b : Fin n) (graph : Template (n+2))
    (A : HAB.Matrix U) (e : Fin n → Fin U) (f : ℕ → ℕ) (prime : (e p).val.Prime)
    (rows : ∀ d y : Fin U, d.val<(e m).val →
      (graph.eval A (extend y d e)=true ↔ y.val=f d.val%(e p).val)) (room : (e m).val*(e p).val<U) :
    (fromRows P m p b graph).eval A e=true ↔ (∏ i ∈ range (e m).val,f i)%(e p).val=(e b).val := by
  rw [fromRows,HABMatrix.bind_spec]
  have args : e ∘ ![m,p,b]=![e m,e p,e b] := by funext i; fin_cases i <;> rfl
  simp only [Function.comp_id] at *
  rw [args,formula_correct P _ (e m) (e p) (e b) (fun i => f i%(e p).val) prime
    (fun _ _ => Nat.mod_lt _ prime.pos) rows room]
  have cong (q : ℕ) : (∏ i ∈ range q,f i%(e p).val) ≡ (∏ i ∈ range q,f i) [MOD (e p).val] := by
    induction q with
    | zero => rfl
    | succ i ih => simpa only [prod_range_succ] using ih.mul (Nat.mod_modEq ..)
  rw [show (∏ i ∈ range (e m).val,f i%(e p).val)%(e p).val =
    (∏ i ∈ range (e m).val,f i)%(e p).val from cong _]

/-- Read raw bits from the input matrix, reduce each row at p, and multiply
all active residues. No restriction on p beyond the integer space for the
two sums applies. -/
noncomputable def binary (P : ShortProducts) {n : ℕ} (m w p b : Fin n) : Template n :=
  fromRows P m p b (HABLargePrimeRow.fromShortProducts P 1 w.succ.succ p.succ.succ 0)

theorem binary_correct (P : ShortProducts) {n U : ℕ} (m w p b : Fin n)
    (A : HAB.Matrix U) (e : Fin n → Fin U) (f : ℕ → ℕ) (prime : (e p).val.Prime)
    (rowRoom : (e m).val*(e p).val<U) (bitRoom : (e w).val*(e p).val<U)
    (fits : ∀ i<(e m).val, f i<2^(e w).val)
    (bits : ∀ i j : Fin U, i.val<(e m).val → j.val<(e w).val → A i j=(f i.val).testBit j.val) :
    (binary P m w p b).eval A e=true ↔ (∏ i ∈ range (e m).val,f i)%(e p).val=(e b).val := by
  apply fromRows_correct P m p b _ A e f prime _ rowRoom
  intro d y act
  let E : Fin (n+2) → Fin U := extend y d e
  exact HABLargePrimeRow.fromShortProducts_correct P 1 w.succ.succ p.succ.succ 0 A E prime bitRoom
    (fits d act) (fun j hj => bits d j act hj)


open HABPairInterpretation

private def corner : Input := fun rh rl ch cl =>
  .conj (numeral 0 rh) (.conj (numeral 0 ch) (.entry rl cl))

private theorem corner_correct {U k : ℕ} (A : HAB.Matrix U) (rh rl ch cl : Fin k) (e : Fin k → Fin U) :
    (corner rh rl ch cl).eval A e=HABSpacePadding.widen A (code (e rh) (e rl)) (code (e ch) (e cl)) := by
  apply Bool.eq_iff_iff.mpr
  simp [corner,Tconj_true,num_true,HABSpacePadding.widen,code,and_assoc]

private noncomputable def body (P : ShortProducts) {k : ℕ} (z o p b : Fin k) : Template k :=
  compileTemplate @corner (binary P (0:Fin 3) 0 1 2) ![o,z,z] ![z,p,b]

private theorem body_correct (P : ShortProducts) {U k : ℕ} (z o p b : Fin k) (A : HAB.Matrix U)
    (e : Fin k → Fin U) (zero : (e z).val=0) (one : (e o).val=1) (prime : (e p).val.Prime) :
    (body P z o p b).eval A e=true ↔ (∏ i : Fin U,HAB.rowWord (A i))%(e p).val=(e b).val := by
  let B := HABSpacePadding.widen A
  let N := code (e o) (e z)
  let q := code (e z) (e p)
  let s := code (e z) (e b)
  have nv : N.val=U := by simp [N,code,zero,one]
  have qv : q.val=(e p).val := by simp [q,code,zero]
  have sv : s.val=(e b).val := by simp [s,code,zero]
  have qp : q.val.Prime := qv ▸ prime
  have args : (fun i : Fin 3 => code (e (![o,z,z] i)) (e (![z,p,b] i)))=![N,q,s] := by
    funext i; fin_cases i <;> rfl
  let f (i : ℕ) := if hi : i<U then HAB.rowWord (A ⟨i,hi⟩) else 0
  have fit (i : ℕ) (hi : i<N.val) : f i<2^N.val := by
    rw [nv] at hi ⊢
    simpa only [f,dif_pos hi] using HAB.rowWord_bound (A ⟨i,hi⟩)
  have bits (i j : Fin (U*U)) (hi : i.val<N.val) (hj : j.val<N.val) :
      B i j=(f i.val).testBit j.val := by
    rw [nv] at hi hj
    rw [show (f i.val).testBit j.val=A ⟨i.val,hi⟩ ⟨j.val,hj⟩ from HAB.rowWord_bit _ ⟨j.val,hj⟩
      |> fun he => by simpa only [f,dif_pos hi] using he]
    apply Bool.eq_iff_iff.mpr
    rw [show B i j=true ↔ _ from HABSpacePadding.matrix_true A 1 i j]
    exact ⟨fun ⟨r,c,⟨hr,hc⟩,ok⟩ =>
      (show r=⟨i.val,hi⟩ from Fin.ext hr) ▸ ((show c=⟨j.val,hj⟩ from Fin.ext hc) ▸ ok),
      fun ok => ⟨⟨i.val,hi⟩,⟨j.val,hj⟩,⟨rfl,rfl⟩,ok⟩⟩
  have room : N.val*q.val<U*U := by
    rw [nv,qv]
    exact Nat.mul_lt_mul_of_pos_left (e p).isLt (Fin.pos (e p))
  have step := binary_correct P (0:Fin 3) 0 1 2 B ![N,q,s] f qp room room fit bits
  rw [body,compileTemplate_correct @corner _ _ _ A B e (fun rh rl ch cl en => corner_correct A rh rl ch cl en),args]
  refine step.trans ?_
  change (∏ i ∈ range N.val,f i)%q.val=s.val ↔ _
  rw [nv,qv,sv,←Fin.prod_univ_eq_prod_range]
  simp [f]

/-- Product of every input row at its full universe width, at any represented
prime. The pair (1,0) denotes the original domain size inside the square
interpretation. No padding parameters appear in the source query. -/
noncomputable def source (P : ShortProducts) {k : ℕ} (p b : Fin k) : HAB.Form k :=
  HAB.toSource (.ex (.ex (.conj (numeral 1 0) (.conj (numeral 0 1)
    (body P 1 0 p.succ.succ b.succ.succ)))))

theorem source_correct (P : ShortProducts) {k U : ℕ} (p b : Fin k) (A : HAB.Matrix U)
    (e : Fin k → Fin U) (prime : (e p).val.Prime) :
    (source P p b).Holds A e ↔ (∏ i : Fin U,HAB.rowWord (A i))%(e p).val=(e b).val := by
  let E (z o : Fin U) : Fin (k+2) → Fin U := extend o z e
  have chk (z o : Fin U) (zero : z.val=0) (one : o.val=1) :=
    body_correct P 1 0 p.succ.succ b.succ.succ A (E z o) zero one prime
  simp only [source,HAB.toSource_correct,Tex_true,Tconj_true,num_true,Fin.cases_zero]
  constructor
  · rintro ⟨z,o,one,zero,ok⟩; exact (chk z o zero one).mp ok
  · intro ok
    have hU := prime.one_lt.trans (e p).isLt
    exact ⟨⟨0,by omega⟩,⟨1,hU⟩,rfl,rfl,(chk _ _ rfl rfl).mpr ok⟩

end DiophantineNP.HABLargePrimeProduct
