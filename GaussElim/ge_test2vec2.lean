import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Linarith
import GaussElim.ReducedEchelonForm1

variable (M : Matrix (Fin m) (Fin n) Rat) (hm : m>0) (hn : n>0)

abbrev colVecofMat (M : Matrix (Fin m) (Fin n) F) := (Vector.ofFn M.transpose).map Vector.ofFn

/--
`ElemOp m` is the type of elementary row operations that can be performed on
a matrix with m rows
-/
inductive ElemOp (m : ℕ) : Type where
| scalarMul (c : Rat) (hc : c≠0) (i : Fin m) : ElemOp m
| rowSwap (i : Fin m) (j : Fin m) : ElemOp m
| rowMulAdd (c : Rat) (i : Fin m) (j : Fin m) (hij : i≠j) : ElemOp m
deriving Repr,BEq

-- functions that take matrix to rowReducedEchelonForm inductive type, with property that the image
-- is equal to the elementary move on the original matrix

namespace ElemOp

/--
Operates an `E : ElemOp` on the matrix `A`
-/
def ElemOpOnMatrix (E : ElemOp m) (A : Matrix (Fin m) (Fin k) Rat) : Matrix (Fin m) (Fin k) Rat :=
match E with
| scalarMul c _ i => A.updateRow i (c • (A i))
| rowSwap i j => let newr := (A i)
    Matrix.updateRow (Matrix.updateRow A i (A j)) j newr
| rowMulAdd c i j _ => A.updateRow i (A i + (c • (A j)))

/--
Operates a list of `ElemOp`s on the matrix `A`
-/
def listElemOpOnMatrix (l : List (ElemOp m)) (A : Matrix (Fin m) (Fin k) Rat) : Matrix (Fin m) (Fin k) Rat :=
  match l with
  | [] => A
  | E::as => ElemOpOnMatrix E (listElemOpOnMatrix as A)

/--
The elementary matrix corresponding to an elementary operation, obtained by
operating it on the identity matrix
-/
def elemMat (E : ElemOp m) := ElemOpOnMatrix E (1:Matrix (Fin m) (Fin m) Rat)

lemma findIdx_notExists_of_eq_length (l : List α) (p : α → Bool) (hl : l.findIdx p = l.length) : ∀ x∈l, p x = false := by
  intro x xl
  by_cases h:p x
  have := List.findIdx_lt_length_of_exists ⟨x,xl,h⟩
  have := ne_of_lt this
  contradiction
  simpa using h

lemma findIdx_eq_length_of_notExists (l : List α) (p : α → Bool) (hl : ∀ x∈l, p x = false) : l.findIdx p = l.length := by
  induction' l with a as ih
  · simp
  · simp at hl; have ih' := ih hl.2
    rw [List.findIdx_cons, hl.1, cond_false]; simpa

lemma findIdx_le_length (l : List α) (p : α → Bool) : l.findIdx p ≤ l.length := by
  by_cases h : (∃ x∈l, p x)
  exact le_of_lt (List.findIdx_lt_length_of_exists h)
  push_neg at h; simp at h
  exact le_of_eq (findIdx_eq_length_of_notExists l p h)

--define general inductive function on vectors that finds 1st elt satisfying p, gives its index (Option Fin)
-- and proof that it satisfies p and all elements before it dont satisfy p

--Finds first column of the matrix that has a nonzero entry

lemma vector_toList_get (v : Vector α k) : ∀ i, v.get i = v.toList.get ⟨i,by simp⟩ := by intro i; rfl

/--
Gives the block matrix starting from `(i,j)`th entry to `(m,n)`th entry
-/
def botRightij (i : Fin m) (j : Fin n) : Matrix (Fin (m-i)) (Fin (n-j)) Rat :=
  M.submatrix (fun k => ⟨k+i,Nat.add_lt_of_lt_sub k.2⟩) (fun l => ⟨l+j,Nat.add_lt_of_lt_sub l.2⟩)

/--
Converts a list of `ElemOp`s into a list of elementary matrices
-/
def list_mat_of_ElemOp : List (ElemOp m) → List (Matrix (Fin m) (Fin m) Rat)
  | [] => []
  | a::as => elemMat a :: list_mat_of_ElemOp as

def mat := !![0,2,3;4,5,6;7,8,(9:Rat)]

/- Given a `m×n` matrix and a point `(i,j)` in it, it will find the pivot column and return
elementary matrices that swap the pivot row with the `i`th row and scale the pivot to 1-/
def findPivot_ij (i : Fin m) (j : Fin n) : Option ((Fin m)×{c : Rat // c≠0}×(Fin m)×(Fin m)) :=
  findPivotAux (colVecofMat (botRightij M i j)).toList where
  findPivotAux (l : List (Vector Rat (m-i))) : Option ((Fin m)×{c : Rat // c≠0}×(Fin m)×(Fin m))  :=
    match l with
    | [] => none
    | col::as => match (Vector.indNonzElt col) with
      | none => findPivotAux as
      | some idx =>
          some (i,⟨(1/col.get idx),(one_div_ne_zero idx.2)⟩,i,(idx.1.castLT (Fin.val_lt_of_le idx.1 (Nat.sub_le m ↑i)) + i))

def findPivot_toElemOp (l : Option ((Fin m)×{c : Rat // c≠0}×(Fin m)×(Fin m))) : List (ElemOp m) :=
  match l with
  | none => []
  | some (i1,⟨c,hc⟩,i2,j) => [scalarMul c hc i1,rowSwap i2 j]

-- lemma : if a vector satisfies the conditions of a reduced row, there is a term of type reducedrow
-- that upon conversion to vector gives the same vector

#check List.mem_replicate

theorem Function.const_def {α : Sort u} (β : Sort v) (a : α) :
  Function.const β a = fun _ => a := rfl

theorem Vector.ofFn_zero (f : Fin 0 → α) : Vector.ofFn f = Vector.nil := by
  rw [Vector.eq_iff]
  simp

lemma Vector.replicate_zero (a : α) : Vector.replicate 0 a = Vector.nil := rfl

theorem Vector.ofFn_const :  ∀ (n : ℕ) (c : α), (Vector.ofFn fun _ : Fin n => c) = Vector.replicate n c := by
  intro n c
  rw [Vector.eq_iff]
  simp [Vector.replicate]

example : findPivot_ij 0 i j (m:=m) (n:=n) = none := by
  dsimp [findPivot_ij]
  set l':=(colVecofMat (botRightij 0 i j)).toList with hl
  induction l' with
  | nil => simp [findPivot_ij.findPivotAux]
  | cons a l ih =>
    have ha : a.allZero := by
      simp [botRightij] at hl
      have h1 : Vector.ofFn (0:Fin (m - ↑i) → ℚ) = zeroVec Rat (m-i.1) := by
        simp [zeroVec,Vector.eq_iff,Vector.replicate]
        rw [← List.ofFn_const (m-i.1) 0]
        rfl
      rw [Function.const_def,List.ofFn_const] at hl
      have h2 : a ∈ List.replicate (n - ↑j) (Vector.ofFn 0) := by
        apply List.mem_of_mem_head?
        simp [hl]
        sorry
      have h3 : a = Vector.ofFn (fun x => 0) := by convert (List.mem_replicate.mp h2).2
      rw [Vector.allZero]
      rw [Vector.ofFn_const] at h3
      simp [h3]
      intro x xv
      rw [← Vector.mem_def,Vector.mem_replicate] at xv
      exact xv.2
    rw [findPivot_ij.findPivotAux]
    simp [Vector.indNonzElt_allZero _ _ ha]
    exact ih



example : listElemOpOnMatrix (findPivot_toElemOp (findPivot_ij M i j)) M i j = 1 := by
  dsimp [findPivot_ij,findPivot_toElemOp]


example : ∃ r : ReducedRow Rat n, Vector.ofFn (listElemOpOnMatrix (findPivot_toElemOp (findPivot_ij M i j)) M i) = r.toVector Rat := by


def reduceRow_i (i : Fin m) (j : Fin n) : ReducedRow Rat n :=
  indNonzCol (colVecofMat (botRightij M i j)).toList where
  indNonzCol (l : List (Vector Rat (m-i))) : Fin (m-i) :=
    match l with
    | [] => []
    | col::as => match (indNonzElt col) with
      | none => indNonzCol as
      | some idx => idx

/--Given that the pivot is present at `(i,j)`, it generates a list of elementary matrices that
eliminate entries in the `j`th column below the `i`th row, using the pivot-/
def elimColBelow_ij (i:Fin m) (j:Fin n) : List (ElemOp m) :=
  List.ofFn fun r : Fin (m-i-1) =>
  have h : r.val+(i.val+1)<m := (Nat.add_lt_of_lt_sub (Eq.subst (Nat.sub_sub m i.1 1) (r.2)))
  have h' : ⟨↑r + (↑i + 1), h⟩ ≠ i := by refine Fin.ne_of_val_ne (by refine Nat.ne_of_lt' (by refine Nat.lt_add_left ↑r (by exact Nat.lt_succ_self ↑i)))
  rowMulAdd (-M ⟨r+i+1,h⟩ j) ⟨r+i+1,h⟩ i h'

-- output data reqd to construct rowmuladd, define another function that converts this data into rowmuladds

/-Row reduction algorithm - Part 1 (Row echelon form)
0. Start from (i,j) = (0,0)
1. Find pivot from (i,j) to (m,n) in matrix that has been multiplied with the operations
   upto (i,j)
2. If not found in jth col, find from (i,j+1) to (m,n)
   If found, swap - improve - eliminate, find pivot from (i+1,j+1) to (m,n)
3. End when (i,j) = (m,n)
-/

def rowEchelonStep (i : Fin m) (j : Fin n) : (Matrix (Fin m) (Fin n) Rat) :=
  let M_ij := listElemOpOnMatrix (findPivot_ij M i j) M
  listElemOpOnMatrix (elimColBelow_ij (M_ij) i j) M_ij

--define rowEchelonMatrix as custom structure

def rowEchelonList (A : Matrix (Fin m) (Fin n) Rat) (i : Fin m) (j : Fin n) : (List (ElemOp m)) × (Matrix (Fin m) (Fin n) Rat) :=
  let A_step := rowEchelonStep A i j
  if hi : i.val = m-1 then
    (findPivot_ij A_step ⟨m-1,Nat.sub_one_lt_of_le hm (le_refl m)⟩ j,
     listElemOpOnMatrix (findPivot_ij A_step ⟨m-1,Nat.sub_one_lt_of_le hm (le_refl m)⟩ j) A_step)
  else
    if hj : j.val = n-1 then
      let plist := (findPivot_ij A_step i ⟨n-1,Nat.sub_one_lt_of_le hn (le_refl n)⟩)
      (elimColBelow_ij (listElemOpOnMatrix plist A_step) i j ++ plist,listElemOpOnMatrix (elimColBelow_ij (listElemOpOnMatrix plist A_step) i j ++ plist) A_step)
    else
      have hij : i.val < m-1 ∧ j.val < n-1 := ⟨lt_of_le_of_ne (Nat.le_sub_one_of_lt i.2) hi, lt_of_le_of_ne (Nat.le_sub_one_of_lt j.2) hj⟩
      ((rowEchelonList A_step ⟨i+1,Nat.add_lt_of_lt_sub hij.1⟩ ⟨j+1,Nat.add_lt_of_lt_sub hij.2⟩).1 ++ elimColBelow_ij (listElemOpOnMatrix (findPivot_ij A i j) A) i j ++ (findPivot_ij A i j),
        (rowEchelonList A_step ⟨i+1,Nat.add_lt_of_lt_sub hij.1⟩ ⟨j+1,Nat.add_lt_of_lt_sub hij.2⟩).2)

  termination_by (m-i.val,n-j.val)
  decreasing_by
  simp_wf
  left
  have hi1 : i.val+1 < m := by apply Nat.add_lt_of_lt_sub hij.1
  apply lt_of_tsub_lt_tsub_left (a:=m); rw [Nat.sub_sub_self (le_of_lt i.2), Nat.sub_sub_self (le_of_lt hi1)]; linarith

def elimColAbove_ij (i : Fin m) (j : Fin n) : List (ElemOp m) :=
  List.ofFn fun r : Fin i => rowMulAdd (-M ⟨r,Fin.val_lt_of_le r (le_of_lt i.2)⟩ j) ⟨r,Fin.val_lt_of_le r (le_of_lt i.2)⟩ i (Fin.ne_of_lt r.2)

/-Back substitution:
Start from the bottommost row
Find index of 1
Eliminate column above-/

--make inductive defn if hard to prove
def backSubstitution (A : Matrix (Fin m) (Fin n) Rat) (i : Fin m) : (List (ElemOp m)) :=
  if h' : i = ⟨0,hm⟩ then [] else
    if h : vec_allZero (Vector.ofFn (A i)) then backSubstitution A ⟨i-1,tsub_lt_of_lt i.2⟩ else
      have hl := List.findIdx_lt_length_of_exists (p:=fun x => x≠0) (xs:=(Vector.ofFn (A i)).toList) (by convert nonzVecHasNonz h; simp)
      let listmat := elimColAbove_ij A i ⟨(Vector.ofFn (A i)).toList.findIdx (fun x => x≠0),by convert hl; simp⟩
      (backSubstitution A ⟨i-1,tsub_lt_of_lt i.2⟩) ++ listmat

  termination_by i
  decreasing_by all_goals
  simp_wf
  apply Fin.val_fin_lt.mp; simp
  have : i.val ≠ 0 := by
    convert h'
    constructor
    · exact Fin.eq_mk_iff_val_eq.mpr
    · intro p; exact False.elim (h' p)
  exact Nat.zero_lt_of_ne_zero this

/--
Gives the row-reduced echelon form of a matrix, along with the list of
elementary operations that convert the matrix into this form
-/
def rowReducedEchelonForm : List (ElemOp m) × Matrix (Fin m) (Fin n) Rat :=
  let (l1,M') := rowEchelonList hm hn M ⟨0,hm⟩ ⟨0,hn⟩
  let l2 := backSubstitution hm M' ⟨m-1,Nat.sub_one_lt_of_le hm (le_refl m)⟩
  (l2++l1,listElemOpOnMatrix l2 M')

count_heartbeats in
#eval list_mat_of_ElemOp (rowReducedEchelonForm !![1,2,3;4,5,6;7,8,9] (by linarith) (by linarith)).1

#eval rowReducedEchelonForm !![1,2,3;4,5,6;7,8,9] (by linarith) (by linarith)
#eval (rowReducedEchelonForm !![1,2,3;4,5,6;7,8,9] (by linarith) (by linarith)).2
