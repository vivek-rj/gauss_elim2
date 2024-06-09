import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Linarith
import GaussElim.ReducedEchelon1vec

variable (M : Matrix (Fin m) (Fin n) Rat) (hm : m>0) (hn : n>0)

inductive ElemOp : Type where
| scalarMul (c : Rat) (hc : c≠0) (i : Fin m) : ElemOp
| rowSwap (i : Fin m) (j : Fin m) : ElemOp
| rowMulAdd (c : Rat) (i : Fin m) (j : Fin m) : ElemOp
-- deriving Repr

namespace ElemOp

def ElemOpOnMatrix  (E : ElemOp (m:=m)) (A : Matrix (Fin m) (Fin n) Rat) : Matrix (Fin m) (Fin n) Rat :=
match E with
| scalarMul c _ i => A.updateRow i (c • (A i))
| rowSwap i j => let newr := (A i)
    Matrix.updateRow (Matrix.updateRow A i (A j)) j newr
| rowMulAdd c i j => A.updateRow i (A i + (c • (A j)))

def listElemOpOnMatrix (l : List (ElemOp (m:=m))) (A : Matrix (Fin m) (Fin n) Rat) : Matrix (Fin m) (Fin n) Rat :=
  match l with
  | [] => A
  | E::as => ElemOpOnMatrix E (listElemOpOnMatrix as A)

def elemMat (E : ElemOp (m:=m)) := ElemOpOnMatrix E (Matrix.diagonal (fun _:Fin m => (1:Rat)))

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

lemma nonzVecHasNonz (h : ¬vec_allZero l) : ∃ x∈l.toList, x≠0 := by
  rw [List.all_eq_true] at h
  push_neg at h
  convert h; simp

-- lemma nonzListHasNonz (h : ¬list_allZero l) : ∃ x∈l, x≠0 := by
--   rw [List.all_eq_true] at h
--   push_neg at h
--   convert h; simp

def indNonzCol : Option {idx : Fin n // ∃ x ∈ ((colVecofMat M).get idx).toList,x ≠ 0} :=
  (colVecofMat M).inductionOn
  (none)
  (fun _ {x} => fun
  | none => if h:vec_allZero x then none else some ⟨0,nonzVecHasNonz h⟩
  | some ⟨idx,h'⟩ => if h:vec_allZero x then some ⟨(idx.succ.cast (by simp)),by simp [h']⟩ else some ⟨0,nonzVecHasNonz h⟩)

lemma vector_toList_get (v : Vector α k) : ∀ i, v.get i = v.toList.get ⟨i,by simp⟩ := by intro i; rfl

--Gives the block matrix starting from (i,j)th entry to (m,n)th entry
def botRightij (i : Fin m) (j : Fin n) : Matrix (Fin (m-i)) (Fin (n-j)) Rat :=
  M.submatrix (fun k => ⟨k+i,Nat.add_lt_of_lt_sub k.2⟩) (fun l => ⟨l+j,Nat.add_lt_of_lt_sub l.2⟩)

/- Given a mxn matrix and a point (i,j) in it, it will find the pivot column and return
elementary matrices that swap the pivot row with the ith row and scale the pivot to 1-/
def indNonzElt (v : Vector Rat k) : Option {idx : Fin k // v.get idx ≠ 0} :=
  v.inductionOn none
  fun _ {x} _ a => if h : x ≠ 0 then some ⟨0, h⟩ else a.map fun idx => ⟨idx.1.succ, idx.2⟩

lemma Vector.inductionOn_cons {C : ∀ {n : ℕ}, Vector α n → Sort*} {k : ℕ} (x : α) (v : Vector α k)
    (h_nil : C Vector.nil) (h_cons : ∀ {n : ℕ} {x : α} {w : Vector α n}, C w → C (x ::ᵥ w)) :
    (x ::ᵥ v).inductionOn h_nil h_cons = h_cons (v.inductionOn h_nil h_cons : C v) := by
  rfl

theorem indNonzElt_nil : indNonzElt Vector.nil = none := rfl

theorem indNonzElt_cons_0_none (v : Vector Rat k) (hv : indNonzElt v = none) :
  indNonzElt (Vector.cons 0 v) = none := by
  induction' v using Vector.inductionOn
  · rfl
  · rw [indNonzElt,Vector.inductionOn_cons,← indNonzElt]
    simp [hv]

theorem indNonzElt_cons_non0 (v : Vector Rat k) (x : Rat) (hx : x≠0) :
  indNonzElt (Vector.cons x v) = some ⟨0,by simp [hx]⟩ := by
  rw [indNonzElt,Vector.inductionOn_cons,← indNonzElt]
  simp [hx]

theorem indNonzElt_cons_0_some (v : Vector Rat k) (idx : Fin k) (hidx : v.get idx ≠ 0) (hv : indNonzElt v = some ⟨idx,hidx⟩) :
  indNonzElt (Vector.cons 0 v) = some ⟨idx.1.succ,by simp [hidx]⟩ := by
  rw [indNonzElt,Vector.inductionOn_cons,← indNonzElt]
  simp [hv]

lemma indNonzElt_some_consSome {v : Vector Rat k} {x : Rat} (h : (indNonzElt v).isSome = true) :
(indNonzElt (Vector.cons x v)).isSome = true := by
  induction' v using Vector.inductionOn
  · rw [indNonzElt_nil] at h; simp at h
  · rw [indNonzElt,Vector.inductionOn_cons,← indNonzElt]
    simp
    by_cases hx:x=0
    · simp [hx,h]
    · simp [hx]

lemma indNonzElt_some_ex (v : Vector Rat k) (h : ∃ x ∈ v.toList, x≠0) : (indNonzElt v).isSome = true := by
  induction' v using Vector.inductionOn with k' x w hi
  · simp at h
  · simp at h
    rcases h with h|h
    · rw [indNonzElt,Vector.inductionOn_cons,← indNonzElt]
      simp [h]
    · exact indNonzElt_some_consSome (hi h)

def list_mat_of_ElemOp : List (ElemOp (m:=m)) → List (Matrix (Fin m) (Fin m) Rat)
  | [] => []
  | a::as => elemMat a :: list_mat_of_ElemOp as

def mat := !![0,2,3;4,5,6;7,8,(9:Rat)]

def findPivot_ij (i : Fin m) (j : Fin n) : List (ElemOp (m:=m)) :=
  findPivotAux (colVecofMat (botRightij M i j)).toList where
  findPivotAux (l : List (Vector Rat (m-i))) : List (ElemOp (m:=m)) :=
    match l with
    | [] => []
    | col::as => match (indNonzElt col) with
      | none => findPivotAux as
      | some idx =>
          [scalarMul (1/col.get idx) (one_div_ne_zero idx.2) i, rowSwap i (idx.1.castLT (Fin.val_lt_of_le idx.1 (Nat.sub_le m ↑i)) + i)]

/-Given that the pivot is present at (i,j), it generates a list of elementary matrices that
eliminate entries in the jth column below the ith row, using the pivot-/
def elimColBelow_ij (i:Fin m) (j:Fin n) : List (ElemOp (m:=m)) :=
  List.ofFn fun r : Fin (m-i-1) =>
  have h : r.val+(i.val+1)<m := (Nat.add_lt_of_lt_sub (Eq.subst (Nat.sub_sub m i.1 1) (r.2)))
  rowMulAdd (-M ⟨r+i+1,h⟩ j) ⟨r+i+1,h⟩ i

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

def rowEchelonList (A : Matrix (Fin m) (Fin n) Rat) (i : Fin m) (j : Fin n) : (List (ElemOp (m:=m))) × (Matrix (Fin m) (Fin n) Rat) :=
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

def elimColAbove_ij (i : Fin m) (j : Fin n) : List (ElemOp (m:=m)) :=
  List.ofFn fun r : Fin i => rowMulAdd (-M ⟨r,Fin.val_lt_of_le r (le_of_lt i.2)⟩ j) ⟨r,Fin.val_lt_of_le r (le_of_lt i.2)⟩ i

/-Back substitution:
Start from the bottommost row
Find index of 1
Eliminate column above-/

--make inductive defn if hard to prove
def backSubstitution (A : Matrix (Fin m) (Fin n) Rat) (i : Fin m) : (List (ElemOp (m:=m))) :=
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
  apply Nat.sub_one_lt_of_le (by apply lt_of_le_of_ne (Nat.zero_le i.val) (Ne.symm this)) (le_refl i.val)

def rowReducedEchelonForm : List (ElemOp (m:=m)) × Matrix (Fin m) (Fin n) Rat :=
  let (l1,M') := rowEchelonList hm hn M ⟨0,hm⟩ ⟨0,hn⟩
  let l2 := backSubstitution hm M' ⟨m-1,Nat.sub_one_lt_of_le hm (le_refl m)⟩
  (l2++l1,listElemOpOnMatrix l2 M')

count_heartbeats in
#eval list_mat_of_ElemOp (rowReducedEchelonForm !![1,2,3;4,5,6;7,8,9] (by linarith) (by linarith)).1

#eval list_mat_of_ElemOp (rowReducedEchelonForm !![1,2,3;4,5,6;7,8,9] (by linarith) (by linarith)).1
#eval (rowReducedEchelonForm !![1,2,3;4,5,6;7,8,9] (by linarith) (by linarith)).2
