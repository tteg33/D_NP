import DiophantineNP.RegisterPathBound
import DiophantineNP.TraceTable
import DiophantineNP.JonesRegisterVerifier

/-! # The fixed affine transition table of a mathlib TM2 verifier -/
namespace DiophantineNP.Classes.Jones.Machine
open Turing JMTableau
open scoped Classical
attribute [local instance] FinTM2.kFin FinTM2.σFin FinTM2.ΛFin
noncomputable section

abbrev Port (tm : FinTM2) := Option tm.K
abbrev Control (tm : FinTM2) := Option tm.Λ × tm.σ
abbrev Branch (tm : FinTM2) := (l : tm.Λ) × (s : tm.σ) × Fin (variants tm (tm.m l) s).length

def variant (tm : FinTM2) (i : Branch tm) := (variants tm (tm.m i.1) i.2.1).get i.2.2
abbrev Width (tm : FinTM2) (i : Branch tm) := cellCount tm (variant tm i).ops.length
abbrev World (tm : FinTM2) := (Bool × Port tm) ⊕ ((i : Branch tm) × Fin (Width tm i))
abbrev Global (tm : FinTM2) := Fin (Fintype.card (World tm))

def index (tm : FinTM2) := Fintype.equivFin (World tm)
def endIndex (tm : FinTM2) (isNew : Bool) (k : Port tm) : Global tm := index tm (.inl (isNew,k))
def internal (tm : FinTM2) (i : Branch tm) (j : Fin (Width tm i)) : Global tm := index tm (.inr ⟨i,j⟩)

def ctrlCode (tm : FinTM2) (c : Control tm) := (Fintype.equivFin (Control tm) c).val

def snapshot (tm : FinTM2) (A : Registers tm) : Port tm → ℕ
  | none => ctrlCode tm (A.label,A.state)
  | some k => A.stack k

def decode (tm : FinTM2) (x : Port tm → ℕ) : Registers tm :=
  let c := if h : x none < Fintype.card (Control tm) then
    (Fintype.equivFin (Control tm)).symm ⟨x none,h⟩ else (none,tm.initialState)
  ⟨c.1,c.2,fun k => x (some k)⟩

private theorem decode_ctrl (tm : FinTM2) (x : Port tm → ℕ) (c : Control tm) (h : x none = ctrlCode tm c) :
    decode tm x = ⟨c.1,c.2,fun k => x (some k)⟩ := by
  have hl : x none < Fintype.card (Control tm) := h ▸ (Fintype.equivFin (Control tm) c).isLt
  unfold decode
  rw [dif_pos hl]
  simp only [h,ctrlCode,Fin.eta,Equiv.symm_apply_apply]

@[simp] theorem decode_snapshot (tm : FinTM2) (A : Registers tm) : decode tm (snapshot tm A) = A :=
  decode_ctrl tm _ (A.label,A.state) rfl

def renamed {m n : ℕ} (f : Fin m → Fin n) (p : Affine m) : Affine n :=
  ⟨p.offset,fun i => ∑ j, if f j = i then p.coeff j else 0⟩

@[simp] theorem renamed_eval {m n} (f : Fin m → Fin n) (p : Affine m) (x : Fin n → ℕ) :
    (renamed f p).eval x = p.eval (x ∘ f) := by
  simp only [Affine.eval,renamed,Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]; simp

private def controlCheck (tm : FinTM2) (isNew : Bool) (c : Control tm) : Equation (Fintype.card (World tm)) :=
  (linear (endIndex tm isNew none) 1 0,linear (endIndex tm isNew none) 0 (ctrlCode tm c))

private def copies (tm : FinTM2) (i : Branch tm) (isNew : Bool) (t : Fin ((variant tm i).ops.length+1)) :
    List (Equation (Fintype.card (World tm))) := Finset.univ.toList.map fun k =>
      (linear (endIndex tm isNew (some k)) 1 0,linear (internal tm i (rowCell tm t k)) 1 0)

def branchEquations (tm : FinTM2) (i : Branch tm) : List (Equation (Fintype.card (World tm))) :=
  controlCheck tm false (some i.1,i.2.1) :: controlCheck tm true ((variant tm i).label,(variant tm i).state) ::
    (copies tm i false 0 ++ copies tm i true (Fin.last _) ++
      (pathEquations tm (variant tm i).ops).map (fun p => (renamed (internal tm i) p.1,renamed (internal tm i) p.2)))

private theorem branchEquations_iff (tm : FinTM2) (i : Branch tm) (x : Global tm → ℕ) :
    Satisfies (branchEquations tm i) x ↔
      x (endIndex tm false none) = ctrlCode tm (some i.1,i.2.1) ∧
      x (endIndex tm true none) = ctrlCode tm ((variant tm i).label,(variant tm i).state) ∧
      (∀ k, x (endIndex tm false (some k)) = x (internal tm i (rowCell tm 0 k))) ∧
      (∀ k, x (endIndex tm true (some k)) = x (internal tm i (rowCell tm (Fin.last _) k))) ∧
      Satisfies (pathEquations tm (variant tm i).ops) (x ∘ internal tm i) := by
  have app (U V : List (Equation (Fintype.card (World tm)))) :
      Satisfies (U++V) x ↔ Satisfies U x ∧ Satisfies V x := by
    simp only [Satisfies,List.mem_append,or_imp,forall_and]
  have cons (p : Equation (Fintype.card (World tm))) (U) :
      Satisfies (p::U) x ↔ p.1.eval x = p.2.eval x ∧ Satisfies U x := by simp [Satisfies]
  simp only [branchEquations,cons,app,and_assoc]
  have ren (P : List (Equation (Width tm i))) : Satisfies
      (P.map fun p => (renamed (internal tm i) p.1,renamed (internal tm i) p.2)) x ↔
        Satisfies P (x ∘ internal tm i) := by
    constructor
    · intro h p hp
      simpa only [renamed_eval] using h _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
    · intro h p hp
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp
      simpa only [renamed_eval] using h z hz
  rw [ren]
  simp [Satisfies,copies,controlCheck]

/-- The same numeric table serves all macrosteps, including intermediate
scratch cells of branches of different lengths. -/
def machineTable (tm : FinTM2) : TraceTable where
  m := Fintype.card (World tm)
  b := Fintype.card (Branch tm)
  k := Fintype.card (Port tm)
  P i := branchEquations tm ((Fintype.equivFin (Branch tm)).symm i)
  old j := endIndex tm false ((Fintype.equivFin (Port tm)).symm j)
  new j := endIndex tm true ((Fintype.equivFin (Port tm)).symm j)

def tableSnapshot (tm : FinTM2) (A : Registers tm) : Fin (machineTable tm).k → ℕ :=
  snapshot tm A ∘ (Fintype.equivFin (Port tm)).symm

/-- Every row passing a branch's checks executes the actual macrostep. -/
theorem tableStep_sound (tm : FinTM2) (i : Branch tm) (x : Global tm → ℕ)
    (h : Satisfies (branchEquations tm i) x) :
    regStep tm (decode tm (x ∘ endIndex tm false)) = some (decode tm (x ∘ endIndex tm true)) := by
  obtain ⟨hc₀,hc₁,h₀,h₁,hpath⟩ := (branchEquations_iff tm i x).mp h
  rw [decode_ctrl tm _ (some i.1,i.2.1) hc₀,decode_ctrl tm _ ((variant tm i).label,(variant tm i).state) hc₁]
  apply (regStep_affine_iff ..).mpr
  refine ⟨i.1,rfl,variant tm i,List.get_mem ..,rfl,rfl,x ∘ internal tm i,?_,?_,hpath⟩
  · exact funext fun k => (h₀ k).symm
  · exact funext fun k => (h₁ k).symm

/-- This fixed multiplier bounds all honest intermediate cells of the machine,
including the encoding of its label and local state. -/
def machineFactor (tm : FinTM2) :=
  (Finset.univ.sup (fun i : Branch tm => pathFactor tm (variant tm i).ops)) + Fintype.card (Control tm) + 1

theorem tableStep_complete (tm : FinTM2) (A C : Registers tm) {M : ℕ} (hm : 0 < M)
    (hA : ∀ k, A.stack k ≤ M) (hC : ∀ k, C.stack k ≤ M) (h : regStep tm A = some C) :
    ∃ (i : Branch tm) (x : Global tm → ℕ),
      x ∘ endIndex tm false = snapshot tm A ∧ x ∘ endIndex tm true = snapshot tm C ∧
      Satisfies (branchEquations tm i) x ∧ ∀ j, x j ≤ M*machineFactor tm := by
  obtain ⟨l,hl,v,hv,hL,hS,y,hy₀,hy₁,hy⟩ := (regStep_affine_iff tm A C).mp h
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hv
  let i : Branch tm := ⟨l,A.state,j⟩
  have hi : variant tm i = v := hj
  have chain := (pathEquations_exact tm v.ops A.stack C.stack).mpr ⟨y,hy₀,hy₁,hy⟩
  rw [← hi] at chain
  obtain ⟨y,y₀,y₁,yh,yB⟩ := boundedPathAssignment tm _ _ _ hm hA chain
  let scratch : (b : Branch tm) → Fin (Width tm b) → ℕ := Function.update (fun _ _ => 0) i y
  let valu : World tm → ℕ := Sum.elim (fun ⟨b,k⟩ => if b then snapshot tm C k else snapshot tm A k)
    (fun ⟨b,j⟩ => scratch b j)
  let x := valu ∘ (index tm).symm
  have h₀ (k) : x (endIndex tm false k) = snapshot tm A k := by simp [x,endIndex,valu]
  have h₁ (k) : x (endIndex tm true k) = snapshot tm C k := by simp [x,endIndex,valu]
  have hy' : x ∘ internal tm i = y := by funext j; simp [x,internal,valu,scratch]
  refine ⟨i,x,funext h₀,funext h₁,(branchEquations_iff tm i x).mpr ?_,?_⟩
  · refine ⟨by simp [h₀,snapshot,hl,i],by simp [h₁,snapshot,hi,hL,hS],fun k => ?_,fun k => ?_,hy' ▸ yh⟩
    · exact (h₀ _).trans ((congrFun y₀ k).symm.trans (congrFun hy' _).symm)
    · exact (h₁ _).trans ((congrFun y₁ k).symm.trans (congrFun hy' _).symm)
  · have hfactor : pathFactor tm (variant tm i).ops ≤ machineFactor tm :=
      (Finset.le_sup (f := fun b => pathFactor tm (variant tm b).ops) (Finset.mem_univ i)).trans (by unfold machineFactor; omega)
    have hF : 0 < machineFactor tm := by unfold machineFactor; omega
    have hMF := Nat.le_mul_of_pos_right M hF
    have hc (c : Control tm) : ctrlCode tm c ≤ M*machineFactor tm := by
      have h' := (Fintype.equivFin (Control tm) c).isLt
      exact (show ctrlCode tm c ≤ machineFactor tm by unfold ctrlCode machineFactor; omega).trans (Nat.le_mul_of_pos_left _ hm)
    intro p; change valu ((index tm).symm p) ≤ _
    cases (index tm).symm p with
    | inl z =>
      obtain ⟨b,k⟩ := z
      cases b <;> cases k
      · exact hc _
      · exact (hA _).trans hMF
      · exact hc _
      · exact (hC _).trans hMF
    | inr z =>
      obtain ⟨b,k⟩ := z
      by_cases eq : b=i
      · subst b; simpa [valu,scratch] using (yB k).trans (Nat.mul_le_mul_left M hfactor)
      · simp [valu,scratch,Function.update_of_ne eq]

/-- A table run between encoded configurations lifts to an actual run of the
register program, without any assumption on the supplied width. -/
theorem tableRun_sound (tm : FinTM2) {n v : ℕ} (A C : Registers tm)
    (h : (machineTable tm).Run n v (tableSnapshot tm A) (tableSnapshot tm C)) :
    ∃ row : Fin (n+1) → Registers tm, row 0 = A ∧ row (Fin.last n) = C ∧
      IsTrace (regStep tm) row := by
  obtain ⟨r,_,ht,hadj⟩ := h
  choose val h₀ hn hold hnew using hadj
  let e := Fintype.equivFin (Port tm)
  let y (t : Fin (n+1)) (k : Port tm) := val (e k) t
  have ha : y 0 = snapshot tm A := by
    funext k; simpa [y,e,tableSnapshot] using h₀ (e k)
  have hc : y (Fin.last n) = snapshot tm C := by
    funext k; simpa [y,e,tableSnapshot] using hn (e k)
  refine ⟨fun t => decode tm (y t),by simp [ha],by simp [hc],fun t => ?_⟩
  obtain ⟨i,hi⟩ := ht t
  let x (j : Global tm) := r j t
  have ho : y t.castSucc = x ∘ endIndex tm false := by
    funext k; simpa [y,e,x,machineTable] using hold (e k) t
  have hn : y t.succ = x ∘ endIndex tm true := by
    funext k; simpa [y,e,x,machineTable] using hnew (e k) t
  change regStep tm (decode tm (y t.castSucc)) = some (decode tm (y t.succ))
  rw [ho,hn]
  exact tableStep_sound tm _ x hi

/-- An honest machine trace has a table certificate whose width exceeds its
native register-space bound by a fixed machine-dependent number of bits. -/
theorem tableRun_complete (tm : FinTM2) {n S : ℕ} (row : Fin (n+1) → Registers tm)
    (h : IsTrace (regStep tm) row) (hS : ∀ t k, ((row t).stack k).size ≤ S) :
    (machineTable tm).Run n (S+bits (machineFactor tm))
      (tableSnapshot tm (row 0)) (tableSnapshot tm (row (Fin.last n))) := by
  have hr (t k) := (Nat.size_le.mp (hS t k)).le
  choose i x ho hn he hB using fun t => tableStep_complete tm _ _ (Nat.two_pow_pos S)
    (hr t.castSucc) (hr t.succ) (h t)
  refine ⟨fun j t => x t j,fun j t => ?_,fun t => ?_,fun j => ?_⟩
  · rw [pow_add]
    exact (hB t j).trans_lt (Nat.mul_lt_mul_of_pos_left Nat.lt_log2_self (Nat.two_pow_pos _))
  · exact ⟨Fintype.equivFin (Branch tm) (i t),by simpa only [machineTable,Equiv.symm_apply_apply] using he t⟩
  · refine ⟨fun t => tableSnapshot tm (row t) j,rfl,rfl,fun t => ?_,fun t => ?_⟩
    · exact (congrFun (ho t) _).symm
    · exact (congrFun (hn t) _).symm

/-- The same bit bound covers endpoint control codes, including zero-step runs. -/
theorem tableSnapshot_lt (tm : FinTM2) (A : Registers tm) (S : ℕ) (h : ∀ k, (A.stack k).size ≤ S)
    (j : Fin (machineTable tm).k) : tableSnapshot tm A j < 2^(S+bits (machineFactor tm)) := by
  unfold tableSnapshot Function.comp
  cases (Fintype.equivFin (Port tm)).symm j with
  | none =>
    rw [pow_add]
    have hctrl : snapshot tm A none ≤ machineFactor tm := by
      have := (Fintype.equivFin (Control tm) (A.label,A.state)).isLt
      change (Fintype.equivFin (Control tm) (A.label,A.state)).val ≤ machineFactor tm
      unfold machineFactor; omega
    exact (hctrl.trans_lt Nat.lt_log2_self).trans_le (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  | some k => exact (Nat.size_le.mp (h k)).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..))

end
end DiophantineNP.Classes.Jones.Machine
