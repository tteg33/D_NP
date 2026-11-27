import DiophantineNP.HABPolylogRange
import DiophantineNP.HABGroupPower
import DiophantineNP.HABSumParameters

/-! # Width of a product of a short list of group elements -/
namespace DiophantineNP.HABShortWidth
open Counting WidthFormula PrimeFormula FiniteArithmeticGap ShortResidue
open ShortResidue.Predicate

def width (len p : ℕ) := (len+1)*(p.log2+1)

private def program : Predicate :=
  ex 3 <| ex 4 <| ex 5 <| ex 6 <| ex 7 <| ex 8 <|
    (HABSumParameters.powAt 3 4).both <| (le 4 1).both <| (add 4 4 5).both <| (lt 1 5).both <|
    (eqN 6 1).both <| (add 0 6 7).both <| (add 3 6 8).both (mul 7 8 2)

def formula {k : ℕ} (len p m : Fin k) : Template k :=
  program.syntaxF (fun i=>if i=0 then len else if i=1 then p else m)

private theorem semantics (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (hp : 0<e 1) :
    program.holds U t e →
      e 2=width (e 0) (e 1) := by
  simp only [program,ex,both,HABSumParameters.powAt,le,lt,neg,add,eqN,mul]
  norm_num [Function.update]
  rintro l _ _ _ _ _ _ _ _ _ _ _ rfl lo rfl hi rfl rfl rfl he
  have hl : l=(e 1).log2 := Nat.le_antisymm ((Nat.le_log2 hp.ne').mpr lo)
    (Nat.le_of_lt_succ ((Nat.log2_lt hp.ne').mpr (by simpa [pow_succ,Nat.mul_two] using hi)))
  simpa only [hl,width] using he.symm

private theorem complete (U : ℕ) (t : ℕ→ℕ→Bool) (e : ℕ→ℕ) (hp : 0<e 1) (hm : e 2<U)
    (cap : 2*e 1<U) (he : e 2=width (e 0) (e 1)) : program.holds U t e := by
  simp only [program,ex,both,HABSumParameters.powAt,le,lt,neg,add,eqN,mul]
  norm_num [Function.update]
  let l := (e 1).log2
  have low : 2^l≤e 1 := Nat.log2_self_le hp.ne'
  have high : e 1<2^l+2^l := by simpa [l,pow_succ,Nat.mul_two] using (Nat.lt_log2_self (n:=e 1))
  have hlen : e 0+1≤e 2 := by rw [he]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hlog : l+1≤e 2 := by rw [he];exact Nat.le_mul_of_pos_left _ (by omega)
  exact ⟨l,by omega,_,by omega,_,by omega,1,by omega,_,by omega,_,by omega,rfl,low,rfl,high,rfl,rfl,rfl,he.symm⟩

private def table {U : ℕ} (A : HAB.Matrix U) (r c : ℕ) : Bool :=
  if h : r<U ∧ c<U then A ⟨r,h.1⟩ ⟨c,h.2⟩ else false

theorem formula_sound {k U : ℕ} (len p m : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U)
    (hp : (e p).val.Prime) :
    (formula len p m).eval A e=true → (e m).val=width (e len).val (e p).val := by
  have hA : A=fun r c => table A r.val c.val := by funext r c;simp [table,r.isLt,c.isLt]
  rw [hA,formula,program.valid _ (table A)]
  exact semantics _ _ _ hp.pos

theorem formula_spec {k U : ℕ} (len p m : Fin k) (A : HAB.Matrix U) (e : Fin k→Fin U)
    (hp : (e p).val.Prime) (cap : 2*(e p).val<U) :
    (formula len p m).eval A e=true ↔ (e m).val=width (e len).val (e p).val := by
  refine ⟨formula_sound _ _ _ _ _ hp,?_⟩
  have hA : A=fun r c => table A r.val c.val := by funext r c;simp [table,r.isLt,c.isLt]
  rw [hA,formula,program.valid _ (table A)]
  exact complete U (table A) (fun i => (e (if i=0 then len else if i=1 then p else m)).val) hp.pos (e m).isLt cap

theorem bounds {U len p : ℕ} (large : HABPolylogRange.threshold 60≤U) (hp : p.Prime)
    (fit : p<U) (short : len≤(HABGroupPower.primeBound (p-1))^2+1) :
    width len p+1≤U.log2^26 ∧ (width len p+1)^2+(width len p+1)<U ∧
    (width len p+1)^2<U.log2^60 ∧ p<2^(width len p+1) := by
  let L := U.log2
  have hL : 2≤L := (Nat.le_log2 (by omega)).mpr ((Nat.pow_le_pow_right (n:=2) (by decide) (Nat.one_lt_two_pow (show 8*(60+2)^2+10≠0 by decide)) : 2^2≤HABPolylogRange.threshold 60).trans large)
  have hmono {a : ℕ} (ha : a≠0) (le : a≤U) : a.log2≤L :=
    (Nat.le_log2 (by omega)).mpr ((Nat.log2_self_le ha).trans le)
  have hpp := hp.two_le
  have plog := hmono hp.ne_zero fit.le
  have nlog := hmono (a:=p-1) (by omega) (by omega)
  have hK : HABGroupPower.primeBound (p-1)≤L^11 := calc
    _ ≤ 32*(4*L)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ = 2^9*L^2 := by ring
    _ ≤ L^9*L^2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hL _)
    _ = L^11 := (pow_add ..).symm
  have hlen : len+1≤2*L^22 := by
    have q := Nat.pow_le_pow_left hK 2
    change _≤(L^11)^2 at q
    rw [←pow_mul] at q
    norm_num1 at q
    have one := Nat.pow_le_pow_left hL 22
    change 2^22≤L^22 at one
    omega
  have hwidth : width len p+1≤L^26 := calc
    _ ≤ (2*L^22)*(2*L)+1 := Nat.add_le_add_right (Nat.mul_le_mul hlen (by omega)) 1
    _ ≤ L^23*L^3 := by
      have h3 : 8≤L^3 := Nat.pow_le_pow_left hL 3
      have bound := Nat.mul_le_mul_left (L^23) h3
      have pos : 0<L^23 := pow_pos (by omega) _
      nlinarith [show L^22*L=L^23 by ring]
    _ = L^26 := (pow_add ..).symm
  have hsq : (width len p+1)^2≤L^52 := by simpa only [←pow_mul] using Nat.pow_le_pow_left hwidth 2
  have poly : L^60<U := by
    obtain ⟨hK,hb,cap⟩ := HABPolylogRange.range_covered (p:=L^60) large le_rfl
    exact (hb.trans (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ (by omega)))).trans_lt cap
  have hmore : L^52*2≤L^60 := calc
    _ ≤ L^52*L^8 := Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hL 8).trans' (by decide))
    _ = L^60 := (pow_add ..).symm
  have hsmall : width len p+1≤L^52 := hwidth.trans (Nat.pow_le_pow_right (by omega) (by decide))
  have hbits : p.log2+1≤width len p+1 := by
    have := Nat.le_mul_of_pos_left (p.log2+1) (by omega : 0<len+1)
    dsimp [width];omega
  exact ⟨hwidth,lt_of_le_of_lt (by omega : (width len p+1)^2+(width len p+1)≤L^60) poly,
    hsq.trans_lt (Nat.pow_lt_pow_right (by omega) (by decide)),Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) hbits)⟩

end DiophantineNP.HABShortWidth
