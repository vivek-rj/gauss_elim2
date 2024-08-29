import Mathlib.Data.Matrix.Notation

variable {F : Type} [Field F] [DecidableEq F]

--[0,0,...,0,1,(arbitrary entries)]
structure ReducedRowNz (F : Type) [Field F] [DecidableEq F] where
  z : Nat
  tail : List F

/-- List of k zero's-/
def zeroList (k: Nat) : List F := List.replicate k 0

/--Converts a nonzero reduced row to a list-/
def ReducedRowNz.toList (row : ReducedRowNz F) : List F := (zeroList row.z).append (1::row.tail)

/--Conversion of List to reduced row-/
def List.isReducedRowNz (l : List F) := ∃ r : ReducedRowNz F, r.toList = l

lemma List.anyNz_headZero_tailAnyNz (as : List F) (has : (0::as).any (·≠0)) : as.any (·≠0) := by
  simp at has
  simp [has]

/--Goes through a list which has a nonzero entry, and returns the following:
* The first nonzero entry, as a unit of the field
* Its index, with a proof of it being present at the index
* The elements of the list that come after this entry-/
def List.firstNzElt (l : List F) (hl : l.any (·≠0)) : (x : Fˣ)×{i : Fin l.length // l.get i = x}×(List F) :=
  match l with
  | [] => by contradiction
  | a::as =>
    if ha : a = 0 then
    have has : as.any (·≠0) := anyNz_headZero_tailAnyNz as (ha ▸ hl)
    let ⟨⟨x,xinv,hinv1,hinv2⟩,⟨idx,hidx⟩,t⟩ := as.firstNzElt has
    ⟨⟨x,xinv,hinv1,hinv2⟩,⟨idx.succ,hidx⟩,t⟩
    else
    ⟨⟨a,a⁻¹,CommGroupWithZero.mul_inv_cancel a ha,inv_mul_cancel ha⟩,⟨⟨0,Nat.zero_lt_succ as.length⟩,rfl⟩,as⟩

#eval [0,0,9,4,(10:Rat)].firstNzElt (by simp)

/--A list can be constructed back using its output for the `firstNzElt` function-/
theorem List.firstNzElt_eq_listSplit (l : List F) (hl : l.any (·≠0)) : let ⟨⟨x,_,_,_⟩,⟨idx,_⟩,t⟩ := (l.firstNzElt hl); l = (zeroList idx).append (x::t) := by
  induction l with
  | nil => contradiction
  | cons a as ih =>
    simp [firstNzElt]
    split_ifs with ha
    · rw [dite_cond_eq_true (eq_true ha)]
      dsimp [zeroList]
      simp [ha]
      have has : as.any (·≠0) := anyNz_headZero_tailAnyNz as (ha ▸ hl)
      exact ih has
    · rw [dite_cond_eq_false]
      dsimp [zeroList]
      simp [ha]

/--If the first nonzero element of a list is 1, it can be converted to a reduced row-/
theorem List.firstNzElt_1_isReducedRowNz (l : List F) (hl : l.any (·≠0)) : (l.firstNzElt hl).1 = 1 → l.isReducedRowNz := by
  intro he
  match h : (l.firstNzElt hl) with
  | ⟨⟨x,_,_,_⟩,⟨idx,_⟩,t⟩ =>
  simp at h
  set x := (l.firstNzElt hl).1 with hx
  set idx := (l.firstNzElt hl).2.1 with hidx
  set t := (l.firstNzElt hl).2.2 with ht
  let r : ReducedRowNz F := ⟨idx,t⟩
  use r
  dsimp [ReducedRowNz.toList]
  simp_rw [firstNzElt_eq_listSplit l hl, ← hidx, ← hx, he, ← ht]
  simp

lemma ReducedRowNz.toList_nz (r : ReducedRowNz F) : r.toList.any (·≠0) := by
  unfold toList
  simp
  use 1
  simp

lemma List.zeroList_append_nz (l : List F) (hl : l.any (·≠0)) (n : Nat) : ((zeroList n).append l).any (·≠0) := by
  induction n with
  | zero => dsimp [zeroList]; assumption
  | succ n ih =>
    dsimp [zeroList] at *
    simp at *
    exact ih

lemma List.zeroList_append_firstNzElt (l : List F) (hl : l.any (·≠0)) (n : Nat) : (((zeroList n).append l).firstNzElt (zeroList_append_nz l hl n)).1 = (l.firstNzElt hl).1 := by
  induction n with
  | zero => dsimp [zeroList]
  | succ n ih =>
    dsimp [zeroList,firstNzElt]
    dsimp [zeroList] at ih
    simp
    exact ih

lemma ReducedRowNz.toList_firstNzElt_1 (r : ReducedRowNz F) : (r.toList.firstNzElt (toList_nz r)).1 = 1 := by
  unfold toList
  rw [(1::r.tail).zeroList_append_firstNzElt (by simp)]
  unfold List.firstNzElt
  simp
  trivial

/--If a list can be converted into a reduced row, its first nonzer element has to be 1-/
theorem List.isReducedRowNz_1_firstNzElt (l : List F) (hl : l.any (·≠0)) : l.isReducedRowNz → (l.firstNzElt hl).1 = 1 := by
  intro hr
  rcases hr with ⟨r,hr⟩
  convert r.toList_firstNzElt_1 <;> (symm;exact hr)

/--A list can be converted into a reduced row iff its first nonzer element is 1-/
theorem List.isReducedRowNz_iff (l : List F) (hl : l.any (·≠0)) : l.isReducedRowNz ↔ (l.firstNzElt hl).1 = 1 :=
  ⟨fun a ↦ isReducedRowNz_1_firstNzElt l hl a,fun a ↦ firstNzElt_1_isReducedRowNz l hl a⟩

lemma List.sMul_firstNzElt (l : List F) (hl : l.any (·≠0)) (c : Fˣ) : ((l.map (fun (x:F)=>c*x)).firstNzElt (by simp at *; exact hl)).1 = c*(l.firstNzElt hl).1 := by
  have hc : c.val ≠ 0 := Units.ne_zero c
  induction l with
  | nil => contradiction
  | cons a as ih =>
    dsimp [firstNzElt]
    split_ifs with ha ha' ha''
    · simp
      have has : as.any (·≠0) := anyNz_headZero_tailAnyNz as (by simp at *; simp [ha] at hl; exact hl)
      exact ih has
    · have : c.val*a≠0 := mul_ne_zero hc ha'
      contradiction
    · have : c.val*a=0 := by exact (Units.mul_right_eq_zero c).mpr ha''
      contradiction
    · simp
      exact Units.eq_iff.mp rfl

/--A nonzero list (all of whose elements aren't zero) can always be multiplied by a suitable scalar to
make it convertible into a reduced row-/
theorem List.nz_rowReducible (l : List F) (hl : l.any (·≠0)) : ∃ c : Fˣ, (l.map (fun (x:F)=>c*x)).isReducedRowNz := by
  set a := (l.firstNzElt hl).1 with ha
  use a⁻¹
  rw [isReducedRowNz_iff,sMul_firstNzElt,← ha,inv_mul_eq_one]

def findPivot (rl : List (List F)) : (i : Nat)×(j : Nat)×{p : Fˣ // rl.get i = p} := sorry
-- need a good way to represent matrices as a list of lists - what are the extra hypotheses needed?
