import DiophantineNP.MachineStackModel

/-! # Composition and loops for finite stack programs -/
namespace DiophantineNP.Classes.StackModel

variable {K : Type} {Γ : K → Type} {Q R : Type}

def heads (s : Memory Γ) : Heads Γ := fun k => (s k).head?
def applyEdits (ed : (k : K) → Move (Γ k)) (s : Memory Γ) : Memory Γ :=
  fun k => (ed k).run (s k)

@[simp] theorem applyEdits_idle (s : Memory Γ) : applyEdits (fun _ => idle) s = s := rfl

/-- A finite transition path, allowing a stop at an arbitrary continuation. -/
inductive Path (c : Code Q Γ) : Option Q → Memory Γ → Option Q → Memory Γ → ℕ → Prop where
  | refl (l s) : Path c l s l s 0
  | cons {q s l t n} (h : Path c (c q (heads s)).next (applyEdits (c q (heads s)).edit s) l t n) :
      Path c (some q) s l t (n+1)

theorem Path.trans {c : Code Q Γ} {l s m t n u z k} (a : Path c l s m t n)
    (b : Path c m t u z k) : Path c l s u z (n+k) := by
  induction a with
  | refl => simpa using b
  | cons _ ih => simpa [Nat.add_right_comm] using Path.cons (ih b)

/-- Redirect the exit of one finite program to an arbitrary continuation. -/
def labelMap (f : Q → R) (exit : Option R) : Option Q → Option R
  | none => exit
  | some q => some (f q)

def Action.redirect (a : Action Q Γ) (f : Q → R) (exit : Option R) : Action R Γ :=
  ⟨labelMap f exit a.next, a.edit⟩

theorem Path.lift {c : Code Q Γ} {d : Code R Γ} {l s m t n} (a : Path c l s m t n)
    (f : Q → R) (exit : Option R) (hc : ∀ q h, d (f q) h = (c q h).redirect f exit) :
    Path d (labelMap f exit l) s (labelMap f exit m) t n := by
  induction a with
  | refl => exact .refl _ _
  | cons h ih =>
    apply Path.cons
    rw [hc]
    exact ih

theorem Path.iterate {c : Code Q Γ} {l s m t n} (p : Path c l s m t n) :
    (flip Bind.bind (step c))^[n] (some (⟨l,s⟩ : Config Q Γ)) = some ⟨m,t⟩ := by
  induction p with
  | refl => rfl
  | cons a ih => rw [Function.iterate_succ_apply]; exact ih

structure Block (Γ : K → Type) where
  Label : Type
  [finite : Fintype Label]
  entry : Label
  code : Code Label Γ
attribute [instance] Block.finite

abbrev Block.Runs (p : Block Γ) (s t : Memory Γ) (n : ℕ) :=
  Path p.code (some p.entry) s none t n

/-- An atomic parallel edit inspecting finitely many top symbols. -/
def atomic (ed : Heads Γ → (k : K) → Move (Γ k)) : Block Γ where
  Label := Unit
  entry := ()
  code _ h := ⟨none, ed h⟩

theorem run_atomic (ed : Heads Γ → (k : K) → Move (Γ k)) (s : Memory Γ) :
    (atomic ed).Runs s (applyEdits (ed (heads s)) s) 1 := .cons (.refl _ _)

def Block.seq (a b : Block Γ) : Block Γ where
  Label := Sum a.Label b.Label
  entry := .inl a.entry
  code
    | .inl l, h => (a.code l h).redirect .inl (some (.inr b.entry))
    | .inr l, h => (b.code l h).redirect .inr none

theorem run_seq {a b : Block Γ} {s t u : Memory Γ} {m n : ℕ}
    (ha : a.Runs s t m) (hb : b.Runs t u n) : (a.seq b).Runs s u (m+n) :=
  (ha.lift (d := (a.seq b).code) Sum.inl (some (.inr b.entry)) (fun _ _ => rfl)).trans
    (hb.lift Sum.inr none (fun _ _ => rfl))

/-- Sequential control implemented by ordinary disjoint finite label types. -/
def choose (cond : Heads Γ → Bool) (a b : Block Γ) : Block Γ where
  Label := Option (Sum a.Label b.Label)
  entry := none
  code
    | none, h => ⟨some (some (if cond h then .inl a.entry else .inr b.entry)), fun _ => idle⟩
    | some (.inl l), h => (a.code l h).redirect (fun x => some (.inl x)) none
    | some (.inr l), h => (b.code l h).redirect (fun x => some (.inr x)) none

theorem run_choose_true {cond : Heads Γ → Bool} {a b : Block Γ} {s t : Memory Γ} {n : ℕ}
    (h : cond (heads s) = true) (ha : a.Runs s t n) : (choose cond a b).Runs s t (n+1) := by
  apply Path.cons
  change Path _ (some (some (if cond (heads s) then _ else _))) s none t n
  rw [h,if_pos rfl]
  exact ha.lift (d := (choose cond a b).code) (fun x => some (.inl x)) none (fun _ _ => rfl)

theorem run_choose_false {cond : Heads Γ → Bool} {a b : Block Γ} {s t : Memory Γ} {n : ℕ}
    (h : cond (heads s) = false) (hb : b.Runs s t n) : (choose cond a b).Runs s t (n+1) := by
  apply Path.cons
  change Path _ (some (some (if cond (heads s) then _ else _))) s none t n
  rw [h,if_neg Bool.false_ne_true]
  exact hb.lift (d := (choose cond a b).code) (fun x => some (.inr x)) none (fun _ _ => rfl)

def loop (cond : Heads Γ → Bool) (body : Block Γ) : Block Γ where
  Label := Option body.Label
  entry := none
  code
    | none, h => ⟨if cond h then some (some body.entry) else none, fun _ => idle⟩
    | some l, h => (body.code l h).redirect some (some none)

theorem run_loop_stop {cond : Heads Γ → Bool} {body : Block Γ} {s : Memory Γ}
    (h : cond (heads s) = false) : (loop cond body).Runs s s 1 := by
  apply Path.cons
  change Path _ (if cond (heads s) then _ else none) s none s 0
  rw [h,if_neg Bool.false_ne_true]
  exact .refl _ _

theorem run_loop_step {cond : Heads Γ → Bool} {body : Block Γ} {s t u : Memory Γ} {m n : ℕ}
    (h : cond (heads s) = true) (hb : body.Runs s t m) (hr : (loop cond body).Runs t u n) :
    (loop cond body).Runs s u ((m+n)+1) := by
  apply Path.cons
  change Path _ (if cond (heads s) then _ else none) s none u (m+n)
  rw [h,if_pos rfl]
  exact (hb.lift (d := (loop cond body).code) some (some none) (by intros; rfl)).trans hr

end DiophantineNP.Classes.StackModel
