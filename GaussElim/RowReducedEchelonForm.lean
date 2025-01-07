import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fin.Tuple.Reflection
import GaussElim.RowEchelonForm
import GaussElim.ElemOp

variable {F : Type} [Field F] [DecidableEq F]

/--Given an m×n REF `R` and an n-vector `v`, this checks if `v` contains zeros
at all the column indices of `R` that contain pivots-/
def RowEchelonForm.zerosAtPivots (R : RowEchelonForm F m n) (v : Fin n → F) : Prop :=
  match R with
  | nil => True
  | pad R0 => zerosAtPivots R0 (Fin.tail v)
  | extend R0 _ => (v 0 = 0) ∧ (zerosAtPivots R0 (Fin.tail v))

@[instance]
def RowEchelonForm.decidable_zerosAtPivots (R : RowEchelonForm F m n) (v : Fin n → F) : Decidable (R.zerosAtPivots v) :=
  match m,n,R with
  | _,_,nil => .isTrue (trivial)
  | _,_,pad R0 => decidable_zerosAtPivots R0 (Fin.tail v)
  | _,_,extend R0 _ => instDecidableAnd (dq := decidable_zerosAtPivots R0 (Fin.tail v))

lemma RowEchelonForm.zerosAtPivots_l1 {R : RowEchelonForm F m n} {v : Fin n → F} (hv : R.zerosAtPivots v) :
  ∀ ind ∈ R.pivots, v ind.1.2 = 0 := by
  induction R with
  | nil => simp
  | pad R0 ih =>
    simp
    intro i j hij ijpl
    simp [pivots] at ijpl
    match ijpl with
    | ⟨a,b,⟨⟨hab,abpl⟩,_,hbj⟩⟩ =>
      rw [← hbj]
      exact ih (v:=Fin.tail v) hv ⟨(a,b),hab⟩ abpl
  | extend R0 w ih =>
    simp
    intro i j hij ijpl
    simp [pivots] at ijpl
    rcases ijpl with ⟨_,hj⟩|⟨a,b,⟨⟨hab,abpl⟩,_,hbj⟩⟩
    · rw [hj]
      exact hv.1
    · rw [← hbj]
      exact ih (v:=Fin.tail v) hv.2 ⟨(a,b),hab⟩ abpl

/--Checks if an REF satisfies the criteria to be in Row-Reduced Echelon Form (abbreviated as RREF):
* The trivial REF (`nil`) is, by default, in RREF
* If a new REF is formed by padding an REF `R0`, then it checks if `R0` is in RREF
* If a new REF is formed by extending an REF `R0` with a vector `w`, it checks if `w` contains zeros
  at all the column indices of `R0` that contain pivots, along with checking if `R0` is in RREF.-/
def RowEchelonForm.isReduced : RowEchelonForm F m n → Prop
  | nil => True
  | pad R0 => R0.isReduced
  | extend R0 w => (R0.zerosAtPivots w) ∧ (R0.isReduced)

@[instance]
def RowEchelonForm.decidable_isReduced (R : RowEchelonForm F m n) : Decidable (R.isReduced) :=
  match R with
  | .nil => .isTrue (trivial)
  | .pad R0 => R0.decidable_isReduced
  | .extend R0 v => instDecidableAnd (dq := R0.decidable_isReduced)

/--A custom Type for all matrices in RREF.-/
def RowReducedEchelonForm (F : Type) [Field F] (m n : Nat) := {R : RowEchelonForm F m n // R.isReduced}

-- def mat3 : Matrix _ _ Rat := !![1,0,2;0,1,-15/2]
-- #eval mat3.toRowEchelonForm.toMatrix
-- #eval mat3.toRowEchelonForm.isReduced

--in RREF.toMatrix, any entry above the pivot in the pivot column is 0
lemma RowReducedEchelonForm.l1 (R : RowReducedEchelonForm F m n) : ∀ ind ∈ R.1.pivots, ∀ k < ind.1.1, R.1.toMatrix k ind.1.2 = 0 := by
  intro ⟨(i,j),hij⟩ ijpl k hk
  simp at hij hk
  let ⟨R,hR⟩ := R
  induction R with
  | nil => simp [RowEchelonForm.pivots] at ijpl
  | pad R0 ih =>
    simp [RowEchelonForm.pivots] at ijpl
    simp [RowEchelonForm.toMatrix]
    match ijpl with
    | ⟨a,b,⟨⟨hab,abpl⟩,hai,hbj⟩⟩ =>
      simp [← hbj]
      exact ih ⟨R0,hR⟩ a b k ((Eq.symm hai) ▸ hk) hR hab abpl
  | @extend m n R0 w ih =>
    simp [RowEchelonForm.pivots] at ijpl
    simp [RowEchelonForm.toMatrix]
    rcases ijpl with ⟨hi,hj⟩|⟨a,b,⟨⟨hab,abpl⟩,hai,hbj⟩⟩
    · rw [hi] at hk
      contradiction
    · rw [← hai] at hk
      simp [← hbj]
      cases k using Fin.cases with
      | zero =>
        rw [Matrix.cons_val_zero]
        exact RowEchelonForm.zerosAtPivots_l1 hR.1 ⟨(a,b),hab⟩ abpl
      | succ p =>
        exact ih ⟨R0,hR.2⟩ a b p (Fin.succ_lt_succ_iff.mp hk) hR.2 hab abpl

/--RREF PROPERTY : In RREF.toMatrix, any entry in the pivot column apart from the pivot is 0 -/
theorem RowReducedEchelonForm.t1 (R : RowReducedEchelonForm F m n) : ∀ ind ∈ R.1.pivots, ∀ k ≠ ind.1.1, R.1.toMatrix k ind.1.2 = 0 := by
  intro ind hind k hk
  rw [ne_iff_lt_or_gt] at hk
  rcases hk with hk|hk
  · exact l1 R ind hind k hk
  · exact RowEchelonForm.t1 R.1 ind hind k hk

namespace Nat

/--Iterates a function that takes a term of type `α i` to a term of type `α (i+1)`-/
@[simp]
def iterate_ind {α : ℕ → Sort*} (f : {i : ℕ} → α i → α (i+1)) (n : ℕ) (a : α 0) : α n :=
  match n with
  | 0 => a
  | succ k => iterate_ind f k (f a)

#eval iterate_ind (α:=fun n => RowEchelonForm Rat 3 n) (RowEchelonForm.pad) 4 (RowEchelonForm.nil)

variable {α : ℕ → Sort*} (f : {i : ℕ} → α i → α (i+1)) (n : ℕ)

@[simp]
theorem iterate_ind_succ (n : ℕ) :
  iterate_ind (α:=α) f (n+1) = (iterate_ind f n) ∘ f :=
  rfl

@[simp]
theorem iterate_ind_commute_self (n : ℕ) : (iterate_ind f n) ∘ f = f ∘ (iterate_ind (α:=α) f n) := by
  induction n generalizing f α with
  | zero => rfl
  | succ n ih =>
    rw [iterate_ind_succ,iterate_ind_succ,← Function.comp.assoc]
    refine congrArg (· ∘ f) ?_
    exact (ih f)

end Nat

/--An REF that is formed from iterated paddings is in RREF-/
theorem RowEchelonForm.pad_isReduced : (Nat.iterate_ind (α := fun i => RowEchelonForm F m i) pad k nil).isReduced := by
  induction k with
    | zero => simp; trivial
    | succ n ih => rw [Nat.iterate_ind_succ,Nat.iterate_ind_commute_self,Function.comp_apply,isReduced]; exact ih

-- This match bug is causing a ton of problems
/--Given an RREF `R0` and a vector `v` by which the RREF is to be extended, this function eliminates all the entries in v that
correspond to the pivot columns of R0, using elementary row operations.-/
def RowReducedEchelonForm.eltPivotColEntries (R : RowReducedEchelonForm F m n) (v : Fin n → F) : Fin n → F :=
  match m,n,R with
  | _,_,⟨.nil,_⟩ => v
  | _,_,⟨.pad R0,hR0⟩ => Fin.cons (v 0) (eltPivotColEntries ⟨R0,hR0⟩ (Fin.tail v))
  | _,_,⟨.extend R0 v',hR0⟩ =>
    let w := eltPivotColEntries ⟨R0,hR0.2⟩ (Fin.tail v)
    Fin.cons 0 (w + (-(v 0))•v')

-- def mat6 : Matrix (Fin 2) (Fin 4) Rat := !![0,1,0,2;0,0,1,0]
-- def v6 : (Fin 4) → Rat := ![4,5,6,7]
-- def rref6 : RowReducedEchelonForm Rat 2 4 := ⟨mat6.toRowEchelonForm,sorry⟩
-- #eval rref6.eltPivotColEntries v6

lemma RowEchelonForm.l10 (R : RowEchelonForm F m n) (hv : R.zerosAtPivots v) (hw : R.zerosAtPivots w) (c : F) :
  R.zerosAtPivots (v + c•w) := by
  induction R with
  | nil => dsimp [zerosAtPivots]
  | pad R0 ih =>
    dsimp [zerosAtPivots] at *
    convert ih hv hw
  | extend R0 w' ih =>
    dsimp [zerosAtPivots] at *
    simp [hv,hw]
    convert ih hv.2 hw.2

/--If all the entries of a vector `v` that correspond to the pivot columns of an RREF `R` have been eliminated, then
`R` can be extended by `v` to get a new RREF-/
lemma RowReducedEchelonForm.eltPivotColEntries_rowReduced (R : RowReducedEchelonForm F m n) (v : Fin n → F) :
  (R.1.extend (R.eltPivotColEntries v)).isReduced := by
  match R with
  | ⟨R,hR⟩ =>
    induction R with
    | nil => simp [RowEchelonForm.isReduced,RowEchelonForm.zerosAtPivots]
    | pad R0 ih =>
      simp [RowEchelonForm.isReduced,RowEchelonForm.zerosAtPivots]
      constructor
      · have := ih ⟨R0,hR⟩ (Fin.tail v) hR
        dsimp [RowEchelonForm.isReduced] at this
        simp [eltPivotColEntries]
        exact this.1
      · exact hR
    | extend R0 w ih =>
      simp [RowEchelonForm.isReduced] at hR ⊢
      constructor
      · simp [RowEchelonForm.zerosAtPivots]
        constructor
        · simp [eltPivotColEntries]
        · have := ih ⟨R0,hR.2⟩ (Fin.tail v) hR.2
          dsimp [RowEchelonForm.isReduced] at this
          simp [eltPivotColEntries]
          set v1 := (eltPivotColEntries ⟨R0,hR.2⟩ (Fin.tail v))
          have h1 := this.1
          have h2 := hR.1
          convert R0.l10 h1 h2 (-(v 0)) using 2
          simp
      · exact hR

/--Given an REF `R`, this function performs the back substitution phase of the Row Reduction algorithm:
* It starts by picking the first row (say `v`) and the RREF that lies below it )(say `R0`)
* It eliminates all the entries in `v` that lie in the pivot columns of `R0` using elementary row operations
* It repeats the same process by taking `R0` as the new REF-/
def RowEchelonForm.backSubstitution (R : RowEchelonForm F m n) : RowReducedEchelonForm F m n :=
  match R with
  | nil => ⟨nil,trivial⟩
  | pad R0 => ⟨pad (backSubstitution R0).1,by dsimp [isReduced]; exact (backSubstitution R0).2⟩
  | extend R0 v =>
    let R' := backSubstitution R0
    ⟨R'.1.extend (R'.eltPivotColEntries v),RowReducedEchelonForm.eltPivotColEntries_rowReduced R' v⟩

-- def mat8 : Matrix _ _ Rat := !![1,2,3;4,5,6;7,8,9]
-- #eval mat8.toRowEchelonForm.toMatrix
-- #eval mat8.toRowEchelonForm.backSubstitution.1.toMatrix

-- def mat9 : Matrix _ _ Rat := !![0,-7,-4,2;2,4,6,12;3,1,-1,-2]
-- #eval mat9.toRowEchelonForm.toMatrix
-- #eval mat9.toRowEchelonForm.backSubstitution.1.toMatrix

-- def mat10 : Matrix _ _ Rat := !![2,10,-1;3,15,2]
-- #eval mat10.toRowEchelonForm.toMatrix
-- #eval mat10.toRowEchelonForm.backSubstitution.1.toMatrix



--MAGNUM OPUS : PART 1
def Matrix.toRowReducedEchelonForm (M : Matrix (Fin m) (Fin n) F) : RowReducedEchelonForm F m n := M.toRowEchelonForm.backSubstitution
