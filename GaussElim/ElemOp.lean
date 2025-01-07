import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fin.Tuple.Reflection
import GaussElim.RowEchelonForm

variable {F : Type} [Field F] [DecidableEq F]

variable (F) in
/--`ElemOp F m` is the type of elementary row operations that can be performed on
a matrix over `F` with `m` rows-/
inductive ElemOp (m : ℕ) : Type where
/-- Takes a nonzero `c : F` and multiplies it to the `i`th row-/
| scalarMul (c : F) (hc : c≠0) (i : Fin m) : ElemOp m
/-- Swaps rows `i` and `j`-/
| rowSwap (i j : Fin m) : ElemOp m
/-- Takes the `j`th row, multiplies it with `c : F` and adds it to the `i`th row-/
| rowMulAdd (c : F) (i : Fin m) (j : Fin m) (hij : i≠j) : ElemOp m
deriving Repr

namespace ElemOp

#check Function.update

def elemMat (E : ElemOp F m) : Matrix (Fin m) (Fin m) F :=
  match E with
  | scalarMul c _ i => (1 : Matrix _ _ _).updateRow i (Function.update 0 i c)
  | rowSwap i j => ((1 : Matrix _ _ _).updateRow i (Function.update 0 j 1)).updateRow j (Function.update 0 i 1)
  | rowMulAdd c i j _ => (1 : Matrix _ _ _).updateRow i (Function.update (Function.update 0 i 1) j c)

#eval (scalarMul (m:=4) (-3:Rat) (by norm_num) 1).elemMat
#eval (rowSwap (m:=4) 1 2 (F:=Rat)).elemMat
#eval (rowMulAdd (m:=4) (-5:Rat) 2 0 (by simp)).elemMat

#check Matrix.mul_apply

lemma Finset.split_summation (n : ℕ) (as : Fin n → F) (k : Fin n) :
     (∑i, as i) = as k + (∑i with i≠k, as i) := by
  have : (∑i with i=k, as i) = as k := by rw [Finset.sum_eq_single_of_mem] <;> simp
  rw [← this, ← Finset.univ.sum_filter_add_sum_filter_not (· = k)]

/--Operates an `E : ElemOp F m` on the `m×n` matrix `A`-/
@[simp] def onMatrix (E : ElemOp F m) (A : Matrix (Fin m) (Fin k) F) : {M : Matrix (Fin m) (Fin k) F // E.elemMat*A=M} :=
match E with
| scalarMul c _ i =>
  ⟨A.updateRow i (c • (A i)),by
    dsimp [elemMat]
    apply Matrix.ext
    intro p q
    rw [Matrix.mul_apply]
    by_cases hpi:p=i
    · simp [hpi,Function.update_apply]
    · simp [hpi,Matrix.one_apply]⟩
| rowSwap i j => let newr := (A i)
    ⟨Matrix.updateRow (Matrix.updateRow A i (A j)) j newr,by
    dsimp [elemMat]
    apply Matrix.ext
    intro p q
    rw [Matrix.mul_apply]
    by_cases hpj:p=j
    · simp [hpj,Function.update_apply]
    · simp [hpj]
      by_cases hpi : p=i
      · simp [hpi,Function.update_apply]
      · simp [hpi,Matrix.one_apply]⟩
| rowMulAdd c i j hij =>
  ⟨A.updateRow i (A i + (c • (A j))),by
    dsimp [elemMat]
    apply Matrix.ext
    intro p q
    rw [Matrix.mul_apply]
    by_cases hpi:p=i
    · simp [hpi]
      rw [Finset.split_summation _ _ i]
      simp [Function.update_apply,hij]
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.filter (fun i' ↦ ¬i' = i) Finset.univ) (· = j)]
      have h1 : (∑ x ∈ Finset.filter (fun x ↦ x = j) (Finset.filter (fun i' ↦ ¬i' = i) Finset.univ), if x = j then c * A x q else if x = i then A x q else 0) = c * A j q := by simp [Finset.sum_filter,(Ne.symm hij)]
      simp [h1]
      apply Finset.sum_eq_zero
      intro x hx
      simp at hx
      simp [hx]
    · simp [hpi,Matrix.one_apply]⟩

end ElemOp

/--Extracts the first `k` rows of a matrix-/
def Matrix.firstkRows (M : Matrix (Fin m) (Fin n) F) (k : ℕ) (hk : k ≤ m) : Matrix (Fin k) (Fin n) F :=
  M.submatrix (fun i => i.castLE hk) (fun j => j)

lemma Matrix.firstkRows_l1 (M : Matrix (Fin m) (Fin n) F) (k : ℕ) (hk : k < m) (i : Fin k) : (firstkRows M k (le_of_lt hk)) i = M (i.castLE (le_of_lt hk)) := rfl

def ElemOp.firstkRows_promote_succ (E : ElemOp F m) : ElemOp F m.succ :=
  match E with
  | scalarMul c hc i => scalarMul c hc (i.castLE (Nat.le_succ m))
  | rowSwap i j => rowSwap (i.castLE (Nat.le_succ m)) (j.castLE (Nat.le_succ m))
  | rowMulAdd c i j hij => rowMulAdd c (i.castLE (Nat.le_succ m)) (j.castLE (Nat.le_succ m)) (by simp [hij])

lemma ElemOp.firstkRows_promote_succ_l1 (E : ElemOp F m) (M : Matrix (Fin m.succ) (Fin n) F) :
  ((firstkRows_promote_succ E).onMatrix M).1 m = M m := by
  match E with
  | scalarMul c hc i =>
    have h1 : i.1 ≠ m := Nat.ne_of_lt i.2
    dsimp [firstkRows_promote_succ]
    rw [Matrix.updateRow_ne]
    rw [← Fin.val_ne_iff]
    simp
    apply Ne.symm
    exact h1
  | rowSwap i j =>
    have hi : i.1 ≠ m := Nat.ne_of_lt i.2
    have hjm : j.1 ≠ m := Nat.ne_of_lt j.2
    dsimp [firstkRows_promote_succ]
    rw [Matrix.updateRow_ne,Matrix.updateRow_ne]
    rw [← Fin.val_ne_iff]
    simp
    apply Ne.symm
    assumption
    rw [← Fin.val_ne_iff]
    simp
    apply Ne.symm
    assumption
  | rowMulAdd c i j hij =>
    have hi : i.1 ≠ m := Nat.ne_of_lt i.2
    dsimp [firstkRows_promote_succ]
    rw [Matrix.updateRow_ne]
    rw [← Fin.val_ne_iff]
    simp
    apply Ne.symm
    assumption

theorem Matrix.updateRow_apply' [DecidableEq m] {i' : m} :
    updateRow M i b i' = if i' = i then b else M i' := by
  by_cases h : i' = i
  · rw [h, updateRow_self, if_pos rfl]
  · rw [updateRow_ne h, if_neg h]

lemma ElemOp.firstkRows_promote_succ_l2 (E : ElemOp F m) (M : Matrix (Fin m.succ) (Fin n) F) (i : Fin m) :
  ((firstkRows_promote_succ E).onMatrix M).1 i = (E.onMatrix (M.firstkRows m (Nat.le_succ m))).1 i := by
  match E with
  | scalarMul c hc j =>
    dsimp [firstkRows_promote_succ]
    by_cases hj : j=i
    · simp [hj,Matrix.firstkRows_l1]
      rw [Matrix.updateRow_apply']
      have h1 : i.castSucc = Fin.castLE (Nat.le_succ m) i := by
        rw [← Fin.val_eq_val]
        simp
      simp [h1]
    · have h1 : Fin.castLE (Nat.le_succ m) j ≠ i.castSucc := by
        rw [← Fin.val_ne_iff]
        push_neg at hj
        rw [← Fin.val_ne_iff] at hj
        simp [hj]
      simp [Matrix.updateRow_ne (Ne.symm h1), Matrix.updateRow_ne (Ne.symm hj)]
      rfl
  | rowSwap j k =>
    dsimp [firstkRows_promote_succ]
    by_cases hk : k=i
    · simp [hk]
      have h1 : i.castSucc = Fin.castLE (Nat.le_succ m) i := by
        rw [← Fin.val_eq_val]
        simp
      simp [h1]
      rfl
    · have h1 : Fin.castLE (Nat.le_succ m) k ≠ i.castSucc := by
        rw [← Fin.val_ne_iff]
        push_neg at hk
        rw [← Fin.val_ne_iff] at hk
        simp [hk]
      simp [Matrix.updateRow_ne (Ne.symm h1), Matrix.updateRow_ne (Ne.symm hk)]
      by_cases hj : j=i
      · simp [hj]
        have h1 : i.castSucc = Fin.castLE (Nat.le_succ m) i := by
          rw [← Fin.val_eq_val]
          simp
        simp [h1]
        rfl
      · have h1 : Fin.castLE (Nat.le_succ m) j ≠ i.castSucc := by
          rw [← Fin.val_ne_iff]
          push_neg at hj
          rw [← Fin.val_ne_iff] at hj
          simp [hj]
        simp [Matrix.updateRow_ne (Ne.symm h1), Matrix.updateRow_ne (Ne.symm hj)]
        rfl
  | rowMulAdd c j k hjk =>
    dsimp [firstkRows_promote_succ]
    by_cases hj : j=i
    · simp [hj,Matrix.firstkRows_l1]
      rw [Matrix.updateRow_apply']
      have h1 : i.castSucc = Fin.castLE (Nat.le_succ m) i := by
        rw [← Fin.val_eq_val]
        simp
      simp [h1]
    · have h1 : Fin.castLE (Nat.le_succ m) j ≠ i.castSucc := by
        rw [← Fin.val_ne_iff]
        push_neg at hj
        rw [← Fin.val_ne_iff] at hj
        simp [hj]
      simp [Matrix.updateRow_ne (Ne.symm h1), Matrix.updateRow_ne (Ne.symm hj)]
      rfl

def ElemOp.list_firstkRows_promote_succ (l : List (ElemOp F m)) : List (ElemOp F m.succ) :=
  match l with
  | [] => []
  | E::tail => E.firstkRows_promote_succ::(list_firstkRows_promote_succ tail)

#eval mat.firstkRows 2 (Nat.AtLeastTwo.prop)

abbrev ElemOp.list_onMatrix (l : List (ElemOp F m)) (A : Matrix (Fin m) (Fin n) F) : Matrix (Fin m) (Fin n) F :=
  match l with
  | [] => A
  | E::tail => E.onMatrix (list_onMatrix tail A)

lemma ElemOp.list_firstkRows_promote_succ_l1 (l : List (ElemOp F m)) (M : Matrix (Fin m.succ) (Fin n) F) :
  (list_onMatrix (list_firstkRows_promote_succ l) M) m = M m := by
  induction l with
  | nil => simp [list_firstkRows_promote_succ]
  | cons E tail ih =>
    simp [list_firstkRows_promote_succ]
    rw [list_onMatrix]
    have h : Fin.last m = m := Eq.symm (Fin.natCast_eq_last m)
    rw [h, ← ih]
    apply firstkRows_promote_succ_l1

lemma ElemOp.onMatrix_l1 (E : ElemOp F m) (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin m.succ) (Fin n) F) :
  (∀ i : Fin m, A i = B i.castSucc) → (E.onMatrix A).1 i = (E.onMatrix (B.firstkRows m (Nat.le_succ m))).1 i := by
  intro h
  match E with
  | scalarMul c hc k =>
    by_cases hik : i=k
    · simp [hik,firstkRows_promote_succ,h k]
      rfl
    · simp [hik,firstkRows_promote_succ,h i]
      rfl
  | rowSwap j k =>
    by_cases hik : k=i
    · simp [hik,firstkRows_promote_succ,h j]
      rfl
    · simp [(Ne.symm hik),firstkRows_promote_succ]
      by_cases hij : j=i
      · simp [hij,h k]
        rfl
      · simp [(Ne.symm hij),h i]
        rfl
  | rowMulAdd c j k hjk =>
    by_cases hij : i=j
    · simp [hij,firstkRows_promote_succ,h j,h k]
      rfl
    · simp [hij,firstkRows_promote_succ,h i]
      rfl

lemma ElemOp.list_firstkRows_promote_succ_l2 (l : List (ElemOp F m)) (M : Matrix (Fin m.succ) (Fin n) F) (i : Fin m) :
  (list_onMatrix (list_firstkRows_promote_succ l) M) i = (list_onMatrix l (M.firstkRows m (Nat.le_succ m))) i := by
  revert i
  induction l with
  | nil => intro i; simp [list_firstkRows_promote_succ]; rfl
  | cons E tail ih =>
    simp [list_firstkRows_promote_succ]
    nth_rw 2 [list_onMatrix]
    rw [list_onMatrix]
    simp at ih
    intro i
    have h := firstkRows_promote_succ_l2 E (list_onMatrix (list_firstkRows_promote_succ tail) M) i
    simp only [Fin.coe_eq_castSucc] at h
    rw [h]
    have ih := fun i => Eq.symm (ih i)
    apply ElemOp.onMatrix_l1 E (i:=i) at ih
    symm
    rw [ih]

abbrev ElemOp.list_to_elemMat_list (l : List (ElemOp F m)) : List (Matrix (Fin m) (Fin m) F) :=
  match l with
  | [] => []
  | E::tail => E.elemMat::(list_to_elemMat_list tail)

abbrev Matrix.list_prod_onMatrix (l : List (Matrix (Fin m) (Fin m) F)) (A : Matrix (Fin m) (Fin n) F) : Matrix (Fin m) (Fin n) F :=
  match l with
  | [] => A
  | M::mats => M*(list_prod_onMatrix mats A)

lemma ElemOp.list_onMatrix_eq_elemMat_list_prod (l : List (ElemOp F m)) (A : Matrix (Fin m) (Fin n) F) :
  ElemOp.list_onMatrix l A = Matrix.list_prod_onMatrix (ElemOp.list_to_elemMat_list l) A := by
  induction l with
  | nil => simp
  | cons E tail ih =>
    rw [list_onMatrix,list_to_elemMat_list,Matrix.list_prod_onMatrix,← ih]
    symm
    exact (E.onMatrix (list_onMatrix tail A)).2

/--Given the `(i,j)`th entry of a matrix is 1, this function uses elementary
row operations to clear the entries below this entry in the same column.-/
def Matrix.eltColBelow (A : Matrix (Fin m) (Fin n) F) (hij : A i j = 1) : (Matrix (Fin m) (Fin n) F)×(List (ElemOp F m)) :=
  match m with
  | 0 => (A,[])
  | k+1 =>
    if hi' : i.val = k then (A,[]) else
    let B := A.firstkRows k (Nat.le_succ k)
    have hi : i.val < k := Fin.val_lt_last (Ne.symm (Fin.ne_of_val_ne fun a ↦ hi' (id (Eq.symm a))))
    have hb : B ⟨i,hi⟩ j = 1 := by
      unfold_let
      unfold firstkRows
      simp [hij]
    let C := eltColBelow B hb
    let D := (ElemOp.rowMulAdd (-(A k j)) k i (by intro h; rw [←h] at hi'; simp at hi')).onMatrix A
    let elist := (ElemOp.rowMulAdd (-(A k j)) k i (by intro h; rw [←h] at hi'; simp at hi'))::(ElemOp.list_firstkRows_promote_succ C.2)
    let r := D.1 k
    (append_row C.1 r,elist)

-- def matr : Matrix _ _ Rat := !![1,2,3;4,5,6;7,8,9]
-- #eval matr.eltColBelow (i:=0) (j:=0) (rfl)

lemma Matrix.eltColBelow_l1 (A : Matrix (Fin m) (Fin n) F ) (hij : A i j = 1) : ElemOp.list_onMatrix (eltColBelow A hij).2 A i = A i := by
  induction m with
  | zero => have := Fin.pos i; contradiction
  | succ k ih =>
    dsimp [eltColBelow]
    split_ifs with hik
    · rfl
    · simp
      rw [ElemOp.list_onMatrix]
      dsimp [ElemOp.rowMulAdd]
      rw [Matrix.updateRow_ne]
      · have h1 : A.firstkRows k (Nat.le_add_right k 1) ⟨↑i,Fin.val_lt_last (Ne.symm (Fin.ne_of_val_ne fun a ↦ hik (id (Eq.symm a))))⟩ j = 1 := by simp [firstkRows,hij]
        have h2 := ih (i:=⟨i,Fin.val_lt_last (Ne.symm (Fin.ne_of_val_ne fun a ↦ hik (id (Eq.symm a))))⟩) (A.firstkRows k (Nat.le_add_right k 1)) h1
        have h3 : i.1 < k := Fin.val_lt_last (Ne.symm (Fin.ne_of_val_ne fun a ↦ hik (id (Eq.symm a))))
        simp [h3] at h2
        rw [firstkRows_l1 A k (lt_add_one k) ⟨i,h3⟩] at h2
        simp at h2
        rw [← h2]
        have := ElemOp.list_firstkRows_promote_succ_l2 ((A.firstkRows k ⋯).eltColBelow h1).2 A ⟨i,h3⟩
        convert this
        simp
      · rw [← Fin.val_ne_iff]
        simpa

lemma Matrix.eltColBelow_l3 (A : Matrix (Fin m) (Fin n) F) (hij : A i j = 1) : ElemOp.list_onMatrix (eltColBelow A hij).2 A = (eltColBelow A hij).1 := by
  induction m with
  | zero => have := Fin.pos i; contradiction
  | succ k ih =>
    dsimp [eltColBelow]
    split_ifs with hik
    · rfl
    · -- split into multiple lemmas
      have h1 : A.firstkRows k (Nat.le_add_right k 1) ⟨↑i,Fin.val_lt_last (Ne.symm (Fin.ne_of_val_ne fun a ↦ hik (id (Eq.symm a))))⟩ j = 1 := by simp [firstkRows,hij]
      have h2 := ih (i:=⟨i,Fin.val_lt_last (Ne.symm (Fin.ne_of_val_ne fun a ↦ hik (id (Eq.symm a))))⟩) (A.firstkRows k (Nat.le_add_right k 1)) h1
      simp
      rw [ElemOp.list_onMatrix,← h2]
      set M := ((A.firstkRows k ⋯).eltColBelow h1).2 with hM
      simp [ElemOp.rowMulAdd]
      apply Matrix.row_ext
      intro p
      cases p using Fin.lastCases with
      | last =>
          have h3 : Fin.last k = k := Eq.symm (Fin.natCast_eq_last k)
          rw [h3,append_row_last]
          simp
          congr
          · rw [h3]
            exact ElemOp.list_firstkRows_promote_succ_l1 M A
          · have h4 := eltColBelow_l1 A hij
            unfold_let
            rw [← h4]
            sorry
      | cast q =>
        rw [append_row_castSucc]
        sorry

def r1 : RowEchelonForm Rat 1 3 := RowEchelonForm.extend (RowEchelonForm.pad (RowEchelonForm.pad RowEchelonForm.nil)) ![3,4]
#eval r1.toMatrix

/--Deletes the first row of a matrix-/
abbrev Matrix.del_1stRow (M : Matrix (Fin (m+1)) (Fin n) F) : Matrix (Fin m) (Fin n) F :=
  M.submatrix (fun l => ⟨l+1,Nat.add_lt_of_lt_sub l.2⟩) (·)

/--Deletes the first column of a matrix-/
abbrev Matrix.del_1stCol (M : Matrix (Fin m) (Fin (n+1)) F) : Matrix (Fin m) (Fin n) F :=
  M.submatrix (·) (fun l => ⟨l+1,Nat.add_lt_of_lt_sub l.2⟩)

/--Given an `m×n` matrix M over a field `F`, this function performs elementary row
operations on M such that it can be written as a term of type
`RowEchelonForm F m n`.-/
def Matrix.toRowEchelonForm (M : Matrix (Fin m) (Fin n) F) : RowEchelonForm F m n :=
  match n with
  | 0 => RowEchelonForm.nil
  | n+1 =>
  if hM : (Fin.allZero (M · 0)) then RowEchelonForm.pad ((M.del_1stCol).toRowEchelonForm)
  else
    have := Fin.allZero_not_length hM
    match m with
    | 0 => by contradiction
    | m+1 =>
      let ⟨⟨x,i⟩,⟨hx,hi⟩⟩ := Fin.firstNonzElt (M · 0) hM
    let M1 := ((ElemOp.rowSwap 0 i).onMatrix M).1
    have hM1 : M1 0 0 ≠ 0 := by
      unfold_let
      simp [updateRow_apply]
      split_ifs with h1
      · rw [h1]; exact hi.1 ▸ hx
      · exact hi.1 ▸ hx
    let p := M1 0 0
    let M2 := ((ElemOp.scalarMul (p⁻¹) (inv_ne_zero hM1) 0).onMatrix M1).1
    have hm2 : M2 0 0 = 1 := by
      unfold_let
      dsimp [ElemOp.onMatrix]
      simp
      exact inv_mul_cancel hM1
    let M3 := (eltColBelow M2 hm2).1
    let v := ((M3.del_1stCol) 0)
    RowEchelonForm.extend (M3.del_1stCol.del_1stRow).toRowEchelonForm v

-- def mat1 : Matrix _ _ Rat := !![1,2,3;0,0,0;0,0,0]
-- #eval mat1.toRowEchelonForm
