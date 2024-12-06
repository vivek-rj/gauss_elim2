import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fin.Tuple.Reflection

variable (F : Type) [Field F] [DecidableEq F]

/--
A custom inductive type for `m×n` matrices over `F` in Row Echelon Form (abbreviated as REF). If `M`
is a term of type `RowEchelonForm F m n`, then a new term of this type can be
constructed by either
* padding a column of zeros to the left of `M`,
* building the `(m+1)×(n+1)` block matrix

  `1 | v`

  `0 | M`

  where v is a vector of size `n`, `0` is a column with m zeros, and `1` is a singleton.
-/
inductive RowEchelonForm : (m n : Nat) → Type where
  /-- this constructor represents the trivial REF with no columns.
      These are the starting point from which other REFs are built. -/
| nil : RowEchelonForm m 0
 /-- Given an REF, this adds a column of zeros to its left. -/
| pad : RowEchelonForm m n → RowEchelonForm m (n+1)
/-- if `M` is in REF and `v` is the vector, this forms the block matrix

  `1 | v`

  `0 | M`

     where `0` represents a column of zeros of size `m` and `1` is a singleton.
     -/
| extend : RowEchelonForm m n → (Fin n → F) → RowEchelonForm (m+1) (n+1)
deriving Repr

def mat := !![1,2,3;4,5,6;7,8,(9:Rat)]
#eval (Matrix.vecCons ![-1,-2,(-3:Rat)] mat)
def v1 := ![0,0,(0:Rat)]
#eval FinVec.map (fun r => (Fin.cons 0 r : Fin _ → _)) mat
#eval FinVec.map (fun r => (Matrix.vecCons 0 r)) mat
#check Fin.append
#check Matrix.of

variable {F} in
/--
Represents a term of type `RowEchelonForm F m n` as an `m×n` matrix.
-/
def RowEchelonForm.toMatrix (R : RowEchelonForm F m n) : Matrix (Fin m) (Fin n) F :=
  match R with
  | nil => fun _ => ![]
  | pad R0 => FinVec.map (fun r => (Matrix.vecCons 0 r)) R0.toMatrix
  | extend R0 v => Matrix.vecCons (Matrix.vecCons 1 v) (FinVec.map (fun r => (Matrix.vecCons 0 r)) R0.toMatrix)

variable {F} in
@[simp] def Fin.allZero (v : Fin m → F) : Prop := ∀ (i : Fin m), v i = 0

section
variable (v : Fin m → F)
instance : Decidable (Fin.allZero v) :=
  inferInstanceAs <| Decidable (∀ (i : Fin m), v i = 0)
end

#eval Fin.allZero v1

variable {F} in
/--
A tuple `v` has all its entries as `0` if and only if its head is `0` and all the
entries of its tail are `0`.
-/
lemma Fin.allZero_head_tail (v : Fin (m+1) → F) : Fin.allZero v ↔ v 0 = 0 ∧ Fin.allZero (Fin.tail v) := by
  constructor
  · intro hv
    constructor
    · simp at hv; exact hv 0
    · contrapose hv
      simp at *
      rcases hv with ⟨i,hi⟩
      exact ⟨i.succ,hi⟩
  · intro ⟨h1,h2⟩
    intro i
    match hi:i.val with
    | 0 =>
      have hi : i=0 := Eq.symm (eq_of_val_eq (id (Eq.symm hi)))
      rw [hi]
      exact h1
    | k+1 =>
      have hk : k.succ < m+1 := lt_of_eq_of_lt (id (Eq.symm hi)) i.2
      have hi : i = ⟨k.succ,hk⟩ := eq_mk_iff_val_eq.mpr hi
      rw [hi]
      show tail v ⟨k,Nat.succ_lt_succ_iff.mp hk⟩ = 0
      exact h2 ⟨k,Nat.succ_lt_succ_iff.mp hk⟩

variable {F} in
/--
Given a tuple where not all of its entries are `0`, this function extracts the
index of a nonzero element, along with a proof that the element at that index is
nonzero.
-/
def Fin.allZero_not_ex_nonzero {v : Fin (m+1) → F} (hv : ¬ Fin.allZero v) :
  {i : Fin (m+1) // v i ≠ 0} := by
  induction m with
  | zero =>
    rw [allZero_head_tail] at hv
    simp at hv
    exact ⟨0,hv⟩
  | succ n ih =>
    rw [allZero_head_tail] at hv
    push_neg at hv
    by_cases h1 : v 0 = 0
    · apply hv at h1
      apply ih at h1
      exact ⟨h1.1.succ,h1.2⟩
    · exact ⟨0,h1⟩

def v2 : Fin 0 → ℚ := ![]

lemma hv2 : (Fin.allZero v2) := by decide
-- #eval Fin.allZero_not_ex_nonzero hv2

variable {F} in
/--
A tuple that doesn't have all of its entries as `0` is of size at least 1.
-/
lemma Fin.allZero_not_length {v : Fin k → F} (hv : ¬Fin.allZero v) : k≥1 := by
  contrapose hv
  push_neg at *
  apply Nat.lt_one_iff.mp at hv
  match k with
  | 0 => simp
  | l+1 => contradiction

/--
`ElemOp F m` is the type of elementary row operations that can be performed on
a matrix over `F` with `m` rows
-/
inductive ElemOp (m : ℕ) : Type where
| scalarMul (c : F) (hc : c≠0) (i : Fin m) : ElemOp m
| rowSwap (i : Fin m) (j : Fin m) : ElemOp m
| rowMulAdd (c : F) (i : Fin m) (j : Fin m) (hij : i≠j) : ElemOp m

namespace ElemOp

variable {F} in
/--
Operates an `E : ElemOp F m` on the `m×n` matrix `A`
-/
@[simp] def onMatrix (E : ElemOp F m) (A : Matrix (Fin m) (Fin k) F) : Matrix (Fin m) (Fin k) F :=
match E with
| scalarMul c _ i => A.updateRow i (c • (A i))
| rowSwap i j => let newr := (A i)
    Matrix.updateRow (Matrix.updateRow A i (A j)) j newr
| rowMulAdd c i j _ => A.updateRow i (A i + (c • (A j)))

end ElemOp

variable {F} in
/--Row recursor for matrices-/
def Matrix.rowRec {motive : {n : Nat} → Matrix (Fin n) α F → Sort _}
  (zero : (M : Matrix (Fin 0) α F) → motive M)
  (succ : {n : Nat} → (ih : (M : Matrix (Fin n) α F) → motive M) → ((M : Matrix (Fin n.succ) α F) → motive M)) :
  {n : Nat} → (M : Matrix (Fin n) α F) → motive M :=
  fun {n} ↦
  match n with
  | 0 => zero
  | _+1 => succ (Matrix.rowRec zero succ)

variable {F} in
/--Extracts the first `k` rows of a matrix-/
def Matrix.firstkRows (M : Matrix (Fin m) (Fin n) F) (k : ℕ) (hk : k ≤ m) : Matrix (Fin k) (Fin n) F :=
  M.submatrix (fun i => i.castLE hk) (fun j => j)

#eval mat.firstkRows 2 (Nat.AtLeastTwo.prop)

/--Appends the given row to the bottom of the matrix-/
def Matrix.append_row (M : Matrix (Fin m) (Fin n) α) (v : (Fin n) → α) : Matrix (Fin (m+1)) (Fin n) α :=
  Fin.append M (row (Fin 1) v)

#check Fin.insertNth

variable {F} in
/--
Given the `(i,j)`th entry of a matrix is 1, this function uses elementary
row operations to clear the entries below this entry in the same column.
-/
def Matrix.eltColBelow (M : Matrix (Fin m) (Fin n) F) (hij : M i j = 1) : Matrix (Fin m) (Fin n) F :=
  Matrix.rowRec (motive := fun {m} M => {i : Fin m} → M i j = 1 → Matrix (Fin m) (Fin n) F)
    (zero := fun M {i} _ => M)
    (succ := fun {k} ih A {i} hij =>
      if hi' : i.val = k then A else
      let B := A.firstkRows k (Nat.le_succ k)
      have hi : i.val < k := Fin.val_lt_last (Ne.symm (Fin.ne_of_val_ne fun a ↦ hi' (id (Eq.symm a))))
      have hb : B ⟨i,hi⟩ j = 1 := by
        unfold_let
        unfold firstkRows
        simp [hij]
      let C := ih B hb
      let D := (ElemOp.rowMulAdd (-(A k j)) k i (by intro h; rw [←h] at hi'; simp at hi')).onMatrix A
      let r := D k
      append_row C r)
    M hij

def matr := !![0,7,8;1,2,3;4,5,(6:Rat)]
#eval matr.eltColBelow (i:=1) (j:=0) (rfl)

def r1 : RowEchelonForm Rat 1 3 := RowEchelonForm.extend (RowEchelonForm.pad (RowEchelonForm.pad RowEchelonForm.nil)) ![3,4]
#eval r1.toMatrix

variable {F} in
/--
Deletes the first row of a matrix
-/
def Matrix.del_1strow (M : Matrix (Fin (m+1)) (Fin n) F) : Matrix (Fin m) (Fin n) F :=
  M.submatrix (fun l => ⟨l+1,Nat.add_lt_of_lt_sub l.2⟩) (·)

variable {F} in
/--
Deletes the first column of a matrix
-/
def Matrix.del_1stcol (M : Matrix (Fin m) (Fin (n+1)) F) : Matrix (Fin m) (Fin n) F :=
  M.submatrix (·) (fun l => ⟨l+1,Nat.add_lt_of_lt_sub l.2⟩)

variable {F} in
/--
Given an `m×n` matrix M over a field `F`, this function performs elementary row
operations on M such that it can be written as a term of type
`RowEchelonForm F m n`.
-/
def Matrix.toRowEchelonForm (M : Matrix (Fin m) (Fin n) F) : RowEchelonForm F m n :=
  match n with
  | 0 => RowEchelonForm.nil
  | n+1 =>
  if hM : (Fin.allZero (M · 0)) then RowEchelonForm.pad ((M.del_1stcol).toRowEchelonForm)
  else
    have := Fin.allZero_not_length hM
    match m with
    | 0 => by contradiction
    | m+1 =>
      let ⟨i,hi⟩ := Fin.allZero_not_ex_nonzero hM
    let M1 := (ElemOp.rowSwap 0 i).onMatrix M
    have hM1 : M1 0 0 ≠ 0 := by
      unfold_let
      simp [updateRow_apply]
      split_ifs with h1
      · rw [h1]; exact hi
      · exact hi
    let p := M1 0 0
    let M2 := (ElemOp.scalarMul (p⁻¹) (inv_ne_zero hM1) 0).onMatrix M1
    have hm2 : M2 0 0 = 1 := by
      unfold_let
      dsimp [ElemOp.onMatrix]
      simp
      exact inv_mul_cancel hM1
    let M3 := eltColBelow M2 hm2
    let v := ((M3.del_1stcol) 0)
    RowEchelonForm.extend (M3.del_1stcol.del_1strow).toRowEchelonForm v

def mat1 : Matrix _ _ Rat := !![1,2,3;0,0,0;0,0,0]
#eval mat1.toRowEchelonForm

variable {F} in
/--
Given an REF `R`, this creates a list containing the coordinates of the pivots in `R`, along with a
proof of their value being 1.
-/
def RowEchelonForm.pivots (R : RowEchelonForm F m n) : List {(i,j) : (Fin m)×(Fin n) | R.toMatrix i j = 1} :=
  match R with
  | nil => []
  | pad M => M.pivots.map (fun ⟨(i,j),hij⟩ => ⟨(i,j.succ),by simp at hij; simp [toMatrix,hij]⟩)
  | extend M _ => ⟨(0,0),by simp [toMatrix]⟩ :: (M.pivots.map (fun ⟨(i,j),hij⟩ => ⟨(i.succ,j.succ),by simp at hij; simp [toMatrix,hij]⟩))

-- in RowEchelonForm.toMatrix,

#check Fin.cases

variable {F} in
/--
Given a matrix in REF, any entry to the left of the pivot in a pivot row is 0
-/
theorem RowEchelonForm.t1 (R : RowEchelonForm F m n) : ∀ ind ∈ R.pivots, ∀ l < ind.1.2, R.toMatrix ind.1.1 l = 0 := by
  intro ⟨(i,j),hij⟩ ijpl k hk
  simp at hij
  induction R with
  | nil => simp [pivots] at ijpl
  | pad R0 ih =>
    simp [pivots] at ijpl
    match ijpl with
    | ⟨a,b,⟨⟨hab,abpl⟩,h1,h2⟩⟩ =>
      simp [toMatrix,Matrix.vecCons,Fin.cons]
      cases k using Fin.cases with
      | zero => rw [Fin.cases_zero]
      | succ p =>
        rw [Fin.cases_succ]
        simp at hk
        have h3 := ih a b hab abpl
        have h4 : p < b := by
          rw [← h2] at hk
          exact Fin.succ_lt_succ_iff.mp hk
        have h5 := h3 p h4
        rw [← h1]
        exact h5
  | extend R0 w ih =>
    simp [pivots] at ijpl
    rcases ijpl with ⟨_,hj⟩|⟨a,b,⟨⟨hab,abpl⟩,hai,hbj⟩⟩
    · simp [hj] at hk
    · simp [toMatrix,←hai]
      cases k using Fin.cases with
      | zero => rw [Matrix.cons_val_zero]
      | succ p =>
        rw [Matrix.cons_val_succ]
        have h1 : p < b := by
          simp at hk
          rw [← hbj] at hk
          exact Fin.succ_lt_succ_iff.mp hk
        exact ih a b hab abpl p h1

variable {F} in
/--
Given a matrix in REF, any entry below the pivot in a pivot column is 0
-/
theorem RowEchelonForm.t2 (R : RowEchelonForm F m n) : ∀ ind ∈ R.pivots, ∀ k > ind.1.1, R.toMatrix k ind.1.2 = 0 := by
  intro ⟨(i,j),hij⟩ ijpl k hk
  simp at hij hk
  induction R with
  | nil => simp [pivots] at ijpl
  | pad R0 ih =>
    simp [pivots] at ijpl
    simp [toMatrix]
    match ijpl with
    | ⟨a,b,⟨⟨hab,abpl⟩,hai,hbj⟩⟩ =>
      simp [← hbj]
      exact ih a b hab abpl k ((Eq.symm hai) ▸ hk)
  | extend R0 w ih =>
    simp [pivots] at ijpl
    simp [toMatrix]
    rcases ijpl with ⟨hi,hj⟩|⟨a,b,⟨⟨hab,abpl⟩,hai,hbj⟩⟩
    · simp [hi,hj]
      rw [hi] at hk
      have h1 : ∃ p : Fin _, k = p.succ := Fin.eq_succ_of_ne_zero (Fin.pos_iff_ne_zero.mp hk)
      rcases h1 with ⟨p,hp⟩
      simp [hp]
    · rw [← hai] at hk
      have h1 : ∃ p : Fin _, k = p.succ := by refine Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hk)
      rcases h1 with ⟨p,hp⟩
      simp [hp]
      have h2 := ih a b hab abpl p (by rw [hp] at hk; exact Fin.succ_lt_succ_iff.mp hk)
      simp [← hbj]
      exact h2

-- if ⟨(i,j),hij⟩ and ⟨(k,l),hkl⟩ ∈ RowEchelonForm.pivots, then i < k ↔ j < l

-- theorem RowEchelonForm.t3 (R : RowEchelonForm F m n) : ∀ inda ∈ R.pivots, ∀ indb ∈ R.pivots, inda.1.1 < indb.1.1 ↔ inda.1.2 < indb.1.2 := by
--   intro ⟨(i,j),hij⟩ ijpl ⟨(k,l),hkl⟩ klpl
--   simp at hij hkl ⊢
--   constructor
--   · intro hik
--     by_contra hjl
--     push_neg at hjl
--     rw [le_iff_eq_or_lt] at hjl
--     rcases hjl with hjl|hjl
--     · have h1 := t2 R ⟨(i,j),hij⟩ ijpl k hik
--       simp [← hjl] at h1
--       rw [hkl] at h1
--       have := one_ne_zero (α:=F)
--       contradiction
--     · sorry
--   · sorry

variable {F} in
def RowEchelonForm.zerosAtPivots (R0 : RowEchelonForm F m n) (w : Fin n → F) : Prop := (R0.pivots.all (fun ⟨(_,j),_⟩ => w j = 0))

@[instance]
def RowEchelonForm.decidable_zerosAtPivots (R : RowEchelonForm F m n) (w : Fin n → F) : Decidable (R.zerosAtPivots w) :=
  inferInstanceAs (Decidable (R.pivots.all (fun ⟨(_,j),_⟩ => w j = 0)))

variable {F} in
/--
Checks if an REF satisfies the criteria to be in Row-Reduced Echelon Form (abbreviated as RREF):
* The trivial REF (`nil`) is, by default, in RREF
* If a new REF is formed by padding an REF `R0`, then it checks if `R0` is in RREF
* If a new REF is formed by extending an REF `R0` with a vector `w`, it checks if `w` contains zeros
  at all the column indices of `R0` that contain pivots, along with checking if `R0` is in RREF.
-/
def RowEchelonForm.isReduced : RowEchelonForm F m n → Prop
  | nil => True
  | pad R0 => R0.isReduced
  | extend R0 w => (R0.zerosAtPivots w) ∧ (R0.isReduced)

/--
A custom Type for all matrices in RREF.
-/
def RowReducedEchelonForm (m n : Nat) := {R : RowEchelonForm F m n // R.isReduced}

@[instance]
def RowEchelonForm.decidable_isReduced (R : RowEchelonForm F m n) : Decidable (R.isReduced) :=
  match R with
  | .nil => .isTrue (trivial)
  | .pad R0 => R0.decidable_isReduced
  | .extend R0 v => instDecidableAnd (dq := R0.decidable_isReduced)

def mat3 : Matrix _ _ Rat := !![1,0,2;0,1,-15/2]
#eval mat3.toRowEchelonForm.toMatrix
#eval mat3.toRowEchelonForm.isReduced

#check Fin.cons

-- in RowReducedEchelonForm.toMatrix, any entry in the pivot column apart from the pivot is 0

section
namespace Nat

/--
Iterates a function that takes a term of type `α i` to a term of type `α (i+1)`
-/
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

variable {F} in
@[simp]
lemma RowEchelonForm.zero_rows_cols_nil (R : RowEchelonForm F 0 0) : R = nil := by
  match R with
  | nil => rfl

variable {F} in
@[simp]
lemma RowEchelonForm.zero_rows_pad (R : RowEchelonForm F 0 n) :
  R = Nat.iterate_ind (α:=fun n => RowEchelonForm F 0 n) pad n (nil) := by
    induction n with
    | zero => simp
    | succ n ih =>
      match R with
      | pad R0 =>
        have h1 := congrArg pad (ih R0)
        rw [Nat.iterate_ind_succ,Nat.iterate_ind_commute_self]
        exact h1

--An REF with its first pivot at (i,j) is fromed from j paddings and an extend

lemma RowEchelonForm.l1 (i : Fin m) (j : Fin n) (R : RowEchelonForm F m (n+j)) (hij : R.toMatrix i (j.castLE (Nat.le_add_right n ↑j)) = 1) (ptail : List {(i,j) | R.toMatrix i j = 1})
  (hplist : R.pivots = ⟨(i,(j.castLE (Nat.le_add_right n ↑j))),by exact hij⟩::ptail) : ∃ (R0 : RowEchelonForm F m n) (v : Fin n → F), R = Nat.iterate_ind (α:=fun x => RowEchelonForm F m (n+x)) pad j R0 := by
  match n with
  | 0 => have := Fin.pos j; contradiction
  | n+1 =>
    induction j using Fin.induction with
    | zero => simp at *
    | succ k ih => sorry

variable {F} in
/--
An REF that is formed from iterated paddings is in RREF
-/
theorem RowEchelonForm.pad_isReduced : (Nat.iterate_ind (α := fun i => RowEchelonForm F m i) pad k nil).isReduced := by
  induction k with
    | zero => simp; trivial
    | succ n ih => rw [Nat.iterate_ind_succ,Nat.iterate_ind_commute_self,Function.comp_apply,isReduced]; exact ih

variable {F} in
/--
Gives the submatrix of an m×n matrix `M` from the `(i,j)`th entry to the `(m,n)`th entry
-/
def Matrix.botRightij (M : Matrix (Fin m) (Fin n) F) (i : Fin m) (j : Fin n) : Matrix (Fin (m-i)) (Fin (n-j)) F :=
  M.submatrix (fun k => ⟨k+i,Nat.add_lt_of_lt_sub k.2⟩) (fun l => ⟨l+j,Nat.add_lt_of_lt_sub l.2⟩)

#check List.indexOf

variable {F} in
def RowReducedEchelonForm.eltAux (R0 : RowReducedEchelonForm F m n) (plist : List {(i,j) : (Fin m)×(Fin n) | R0.1.toMatrix i j = 1}) (v : Fin n → F) : Fin n → F :=
  match plist with
  | [] => v
  | ⟨(i,j),_⟩::tail =>
    let w := eltAux R0 tail v
    (w + (-(w j))•(R0.1.toMatrix i))

variable {F} in
/--Given an RREF `R0` and a vector `v` by which the RREF is to be extended, this function eliminates all the entries in v that
correspond to the pivot columns of R0.-/
def RowReducedEchelonForm.extend_eltPivotColEntries (R0 : RowReducedEchelonForm F m n) (v : Fin n → F) : Fin n → F :=
  eltAux R0 R0.1.pivots v


--Work in progress from here on

def mat6 : Matrix _ _ Rat := !![0,1,0,0;0,0,1,0]
def v6 : _ → Rat := ![4,5,6,7]
def rref6 : RowReducedEchelonForm Rat _ _ := ⟨mat6.toRowEchelonForm,sorry⟩
#eval rref6.extend_eltPivotColEntries v6

-- This match bug is causing a ton of problems
lemma RowReducedEchelonForm.extend_eltPivotColEntries_rowReduced (R : RowReducedEchelonForm F m n) (v : Fin n → F) :
  (R.1.extend (R.extend_eltPivotColEntries v)).isReduced := by
  match m,n,R with
  | _,_,⟨RowEchelonForm.nil,_⟩ =>
    simp [RowEchelonForm.isReduced,RowEchelonForm.zerosAtPivots]
  | _,_,⟨.pad R0,hR⟩ =>
    simp [RowEchelonForm.isReduced]
    constructor
    · simp [RowEchelonForm.zerosAtPivots,RowEchelonForm.pivots]
      intro i j hij i' j' hi'j' hi'j'p hii' hjj'
      simp [extend_eltPivotColEntries,RowEchelonForm.pivots]
      induction R0.pivots with
      | nil =>
      | cons ⟨(k,l),hkl⟩ plist ih => sorry
      -- match hr:R0.pivots with
      -- | [] => rw [hr] at hi'j'p; contradiction
      -- | ⟨(k,l),hkl⟩::plist =>
      --   simp [extend_eltPivotColEntries.eltAux]
    · rwa [RowEchelonForm.isReduced] at hR
  | _,_,⟨.extend R0 w,hR⟩ =>
    simp [RowEchelonForm.isReduced]
    constructor
    · sorry
    · rwa [RowEchelonForm.isReduced] at hR


def mat5 : Matrix _ _ Rat := !![1,0,0;0,1,0;0,0,1]
def rref1 : RowReducedEchelonForm Rat _ _ := ⟨mat5.toRowEchelonForm,sorry⟩
#eval rref1.extend_eltPivotColEntries ![5,6,7]

variable {F} in
def RowEchelonForm.backSubstitution (R : RowEchelonForm F m n) : RowReducedEchelonForm F m n :=
  match R with
  | nil => ⟨nil,trivial⟩
  | pad R0 => ⟨pad (backSubstitution R0).1,sorry⟩
  | extend R0 v =>
    match R0.pivots with
    | [] => ⟨R0.extend v,sorry⟩
    | ⟨(i,j),hij⟩::l =>
      let R1 := R0.backSubstitution
      let M := (ElemOp.rowMulAdd (-(v j)) 0 i (sorry)).onMatrix (R0.extend v).toMatrix
      -- TPT M is in REF
      -- TPT M is in RREF



  -- Matrix.rowRec (motive := fun {m} M => RowReducedEchelonForm F m n)
  -- (sorry)
  -- (sorry)
  -- R.toMatrix

  -- match m with
  -- | 0 => ⟨R,by rw [zero_rows_pad R]; exact pad_isReduced⟩
  -- | k+1 => Matrix.rowRec {motive := fun M => RowEchelonForm F m n → RowReducedEchelonForm F m n}
  --   (sorry)
  --   (sorry)
  --   (R.toMatrix)


    -- let plist := R.pivots.filter (fun ⟨(i,_),_⟩ => i > k)
    -- let M := R.toMatrix
    -- match plist with
    -- | [] =>
    --   have hr : R.isReduced := by

    --let A := (ElemOp.rowMulAdd (-(M k j)) k i (by intro h; rw [←h] at hi'; simp at hi')).onMatrix M
