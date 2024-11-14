import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fin.Tuple.Reflection

variable (F : Type) [Field F] [DecidableEq F]

/--
A custom inductive type for `m×n` matrices over `F` in Row Echelon Form. If `M`
is a term of type `RowEchelonForm F m n`, then a new term of this type can be
constructed by either
* padding a column of zeros to the left of `M`,
* building the `(m+1)×(n+1)` block matrix

  `1 | v`

  `0 | M`

  where v is a vector of size `n`, `0` is a column with m zeros, and `1` is a singleton.
-/
inductive RowEchelonForm : (m n : Nat) → Type where
  /-- this constructor represents the trivial matrices with no columns.
      These are the starting point from which other row reduced matrices are built. -/
| nil : RowEchelonForm m 0
 /-- Given a row reduced matrix, this adds a column of zeros to its left. -/
| pad : RowEchelonForm m n → RowEchelonForm m (n+1)
/-- if `M` is the row-reduced matrix and `v` is the vector, this forms the block matrix

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
theorem Fin.allZero_head_tail (v : Fin (m+1) → F) : Fin.allZero v ↔ v 0 = 0 ∧ Fin.allZero (Fin.tail v) := by
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

/--
`ElemOp F m` is the type of elementary row operations that can be performed on
a matrix over `F` with `m` rows
-/
inductive ElemOp (m : ℕ) : Type where
| scalarMul (c : F) (hc : c≠0) (i : Fin m) : ElemOp m
| rowSwap (i : Fin m) (j : Fin m) : ElemOp m
| rowMulAdd (c : F) (i : Fin m) (j : Fin m) (hij : i≠j) : ElemOp m

namespace ElemOp

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

variable {F} in
/--
Given the `(i,j)`th entry of a matrix is 1, this function uses elementary
row operations to clear the column below this entry.
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
      let D := (ElemOp.rowMulAdd (-(A k j)) k i (by intro h; rw [←h] at hi'; simp at hi')).onMatrix F A
      let r := D k
      append_row C r)
    M hij

def matr := !![(1:Rat),2,3;4,5,6;7,8,9]
#eval matr.eltColBelow (i:=0) (j:=0) (rfl)

def r1 : RowEchelonForm Rat 1 3 := RowEchelonForm.extend (RowEchelonForm.pad (RowEchelonForm.pad RowEchelonForm.nil)) ![3,4]
#eval r1.toMatrix

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
    let M1 := (ElemOp.rowSwap 0 i).onMatrix F M
    have hM1 : M1 0 0 ≠ 0 := by
      unfold_let
      simp [updateRow_apply]
      split_ifs with h1
      · rw [h1]; exact hi
      · exact hi
    let p := M1 0 0
    let M2 := (ElemOp.scalarMul (p⁻¹) (inv_ne_zero hM1) 0).onMatrix F M1
    have hm2 : M2 0 0 = 1 := by
      unfold_let
      dsimp [ElemOp.onMatrix]
      simp
      exact inv_mul_cancel hM1
    let M3 := eltColBelow M2 hm2
    let v := ((M3.del_1stcol) 0)
    RowEchelonForm.extend (M3.del_1stcol.del_1strow).toRowEchelonForm v

def mat2 : Matrix _ _ Rat := !![1,-2,1,-1;2,1,3,8;4,-7,1,-2]
#eval (mat2.toRowEchelonForm).toMatrix

--define RowReducedEcelonForm F m n
--define back substitution function, RowEchelonForm F m n → RowReducedEchelonForm F m n
