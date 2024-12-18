import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fin.Tuple.Reflection



variable {F : Type} [Field F] [DecidableEq F]



variable (F) in
/--A custom inductive type for `m×n` matrices over `F` in Row Echelon Form (abbreviated as REF). If `M`
is a term of type `RowEchelonForm F m n`, then a new term of this type can be
constructed by either
* padding a column of zeros to the left of `M`,
* building the `(m+1)×(n+1)` block matrix

  `1 | v`

  `0 | M`

  where v is a vector of size `n`, `0` is a column with m zeros, and `1` is a singleton.-/
inductive RowEchelonForm : (m n : Nat) → Type where
  /-- this constructor represents the trivial REF with no columns.
      These are the starting point from which other REFs are built. -/
| nil : RowEchelonForm m 0
 /-- Given an REF, this adds a column of zeros to its left. -/
| pad : RowEchelonForm m n → RowEchelonForm m (n+1)
/-- if `M` is in REF and `v` is the vector, this forms the block matrix

  `1 | v`

  `0 | M`

     where `0` represents a column of zeros of size `m` and `1` is a singleton.-/
| extend : RowEchelonForm m n → (Fin n → F) → RowEchelonForm (m+1) (n+1)
deriving Repr

namespace RowEchelonForm

/--Represents a term of type `RowEchelonForm F m n` as an `m×n` matrix.-/
def toMatrix (R : RowEchelonForm F m n) : Matrix (Fin m) (Fin n) F :=
  match R with
  | nil => fun _ => ![]
  | pad R0 => FinVec.map (fun r => (Matrix.vecCons 0 r)) R0.toMatrix
  | extend R0 v => Matrix.vecCons (Matrix.vecCons 1 v) (FinVec.map (fun r => (Matrix.vecCons 0 r)) R0.toMatrix)

/--Given an REF `R`, this creates a list containing the coordinates of the pivots in `R`, along with a
proof of their value being 1.-/
def pivots (R : RowEchelonForm F m n) : List {(i,j) : (Fin m)×(Fin n) | R.toMatrix i j = 1} :=
  match R with
  | nil => []
  | pad M => M.pivots.map (fun ⟨(i,j),hij⟩ => ⟨(i,j.succ),by simp at hij; simp [toMatrix,hij]⟩)
  | extend M _ => ⟨(0,0),by simp [toMatrix]⟩ :: (M.pivots.map (fun ⟨(i,j),hij⟩ => ⟨(i.succ,j.succ),by simp at hij; simp [toMatrix,hij]⟩))

/--REF PROPERTY 1 : Given a matrix in REF, any entry below the pivot in a pivot column is 0-/
theorem zerosBelowPivot (R : RowEchelonForm F m n) : ∀ ind ∈ R.pivots, ∀ k > ind.1.1, R.toMatrix k ind.1.2 = 0 := by
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

/--PIVOT PROPERTY 1 : Given a matrix in REF, any entry to the left of the pivot in a pivot row is 0-/
lemma zerosBeforePivot (R : RowEchelonForm F m n) : ∀ ind ∈ R.pivots, ∀ l < ind.1.2, R.toMatrix ind.1.1 l = 0 := by
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

@[simp]
theorem List.head_map (f : α → β) (l : List α) (hl : l ≠ []) : (l.map f).head (by simp [l.length_map]; assumption) = f (l.head hl) := by
  match l with
  | [] => contradiction
  | _::_ => simp

/--In an REF, the 'i' coordinate of the first pivot is always 0-/
lemma pivots_rowOfFirstPivot_eq_firstRow (R : RowEchelonForm F m n) (hR : R.pivots ≠ []) : (R.pivots.head hR).1.1.val = 0 := by
  induction R with
  | nil => simp [pivots] at hR
  | pad R0 ih =>
    have hR : R0.pivots ≠ [] := by simp [pivots] at hR ⊢; assumption
    convert ih hR using 2
    simp [pivots]
    rw [List.head_map]
  | extend R0 w _ =>
    simp [pivots]

lemma pivots_length_le_numRows (R : RowEchelonForm F m n) : R.pivots.length ≤ m := by
  induction R with
  | nil => simp [pivots]
  | pad R0 ih => simp [pivots]; exact ih
  | extend R0 w ih => simp [pivots]; exact ih

/--PIVOT PROPERTY 2 : In an REF, the 'i' coordinates of the pivots are exactly their indices in the pivot list.-/
lemma pivots_pivotInd_eq_pivotRows (R : RowEchelonForm F m n) (x : Fin R.pivots.length) : (R.pivots.get x).1.1 = x.castLE (pivots_length_le_numRows R) := by
  induction R with
  | nil =>
    simp [pivots] at x
    have := Fin.pos x
    contradiction
  | pad R0 ih =>
    convert ih (x.cast (by simp [pivots])) using 1
    simp [pivots]
    rfl
  | extend R0 w ih =>
    cases x using Fin.cases with
    | zero =>
      simp [pivots]
    | succ p =>
      simp [pivots]
      exact ih (p.cast (by simp))

end RowEchelonForm



namespace Fin

/--Function that checks if all the entries in a tuple are zero-/
@[simp] def allZero (v : Fin m → F) : Prop := ∀ (i : Fin m), v i = 0

instance (v : Fin m → F) : Decidable (allZero v) :=
  inferInstanceAs <| Decidable (∀ (i : Fin m), v i = 0)

/--A tuple `v` has all its entries as `0` if and only if its head is `0` and all the
entries of its tail are `0`.-/
lemma allZero_head_tail (v : Fin (m+1) → F) : Fin.allZero v ↔ v 0 = 0 ∧ allZero (tail v) := by
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

/--A tuple that doesn't have all of its entries as `0` is of size at least 1.-/
lemma allZero_not_length {v : Fin k → F} (hv : ¬allZero v) : k≥1 := by
  contrapose hv
  push_neg at *
  apply Nat.lt_one_iff.mp at hv
  match k with
  | 0 => simp
  | l+1 => contradiction

/--Given a tuple, not all of whose elements are 0, this function returns the following:
1. The value of the first nonzero element (say x)
2. The index of x
3. Proof that x is present at the returned index
4. Proof that it is the first nonzero element of the tuple-/
def firstNonzElt (v : Fin n → F) (hv : ¬ allZero v) : {(x,i) : F×(Fin n) | x ≠ 0 ∧ v i = x ∧ ∀ i' < i, v i' = 0} := --{x : F // x ≠ 0}×{i : Fin n // v i = x ∧ ∀ i' < i, v i' = 0} :=
  match n with
  | 0 => by simp at hv
  | k+1 =>
    if hv0 : v 0 = 0 then
      have hvt : ¬ allZero (tail v) := by
        rw [allZero_head_tail] at hv
        simp [hv0] at hv
        simp [hv]
      let ⟨(x,ind),hxi⟩ := firstNonzElt (tail v) hvt
      ⟨(x,ind.succ),by
      simp at hxi ⊢
      constructor
      · exact hxi.1
      · constructor
        · exact hxi.2.1
        · have h1 : ∀ i' < ind, v i'.succ = 0 := fun i' hi' => hxi.2.2 i' hi'
          intro i' hi'
          cases i' using cases with
          | zero => exact hv0
          | succ j' => exact h1 j' (succ_lt_succ_iff.mp hi')⟩
    else ⟨(v 0,0),by simp [hv0]⟩

lemma firstNonzElt_eq (v1 v2 : Fin n → F) (hv1 : ¬ Fin.allZero v1) (hv2 : ¬ Fin.allZero v2) (h : v1 = v2) :
  (Fin.firstNonzElt v1 hv1).1 = (Fin.firstNonzElt v2 hv2).1 := by
  congr
  simp [h]
  rw [← propext (Equiv.cast_eq_iff_heq (congrArg Not (congrArg allZero h)))]

end Fin



namespace RowEchelonForm

/--Given a matrix in REF, the first nonzero entry of any nonzero row is 1-/
lemma row_fistNonzElt_val_eq_1 (R : RowEchelonForm F m n) (i : Fin m) (hrow : ¬ Fin.allZero (R.toMatrix i)) : (Fin.firstNonzElt (R.toMatrix i) hrow).1.1 = 1 := by
  induction R with
  | nil =>
    simp at hrow
  | pad R0 ih =>
    simp [toMatrix] at hrow ⊢
    rcases hrow with ⟨x,hx⟩
    have h1 : ¬ Fin.allZero (R0.toMatrix i) := by
      cases x using Fin.cases with
      | zero =>
        simp at hx
      | succ p =>
        simp at hx
        simp
        use p
    rw [← ih i h1]
    have h2 : (Fin.tail (FinVec.map (fun r ↦ Matrix.vecCons 0 r) R0.toMatrix i)) = R0.toMatrix i := by simp; rfl
    simp [Fin.firstNonzElt]
    congr
    apply Fin.firstNonzElt_eq
    exact h2
  | extend R0 w ih =>
    cases i using Fin.cases with
    | zero => simp [toMatrix,Fin.firstNonzElt]
    | succ p =>
      simp [toMatrix,Fin.firstNonzElt] at hrow ⊢
      rcases hrow with ⟨x,hx⟩
      have h1 : ¬ Fin.allZero (R0.toMatrix p) := by
        cases x using Fin.cases with
        | zero =>
          simp at hx
        | succ p =>
          simp at hx
          simp
          use p
      rw [← ih p h1]
      congr 1
      apply Fin.firstNonzElt_eq
      simp
      rfl

/--REF Property 2 : Given a matrix in REF, the first nonzero entry of any nonzero row is a pivot-/
theorem row_fistNonzElt_eq_pivot (R : RowEchelonForm F m n) (i : Fin m) (hrow : ¬ Fin.allZero (R.toMatrix i)) :
  let data := Fin.firstNonzElt (R.toMatrix i) hrow
  ⟨(i,data.1.2),by simp [data.2.2]; rw [← row_fistNonzElt_val_eq_1 R i hrow]⟩ ∈ R.pivots := by
  induction R with
  | nil => simp [toMatrix] at hrow
  | pad R0 ih =>
    simp [toMatrix] at hrow ⊢
    rcases hrow with ⟨k,hk⟩
    have h1 : ¬ Fin.allZero (R0.toMatrix i) := by
      cases k using Fin.cases with
      | zero =>
        simp at hk
      | succ p =>
        simp at hk
        simp
        use p
    have h2 := ih i h1
    simp [Fin.firstNonzElt]
    simp only [pivots,List.mem_map,Subtype.mk.injEq, Prod.mk.injEq,Fin.succ_inj]
    simp at h2
    use ⟨(i,((Fin.firstNonzElt (R0.toMatrix i) h1)).1.2),by simp [((Fin.firstNonzElt (R0.toMatrix i) h1)).2.2]; exact row_fistNonzElt_val_eq_1 R0 i h1⟩
    simp [h2]
    have h3 : (Fin.tail (FinVec.map (fun r ↦ Matrix.vecCons 0 r) R0.toMatrix i)) = R0.toMatrix i := by simp; rfl
    congr 1
    apply Fin.firstNonzElt_eq
    symm
    exact h3
  | extend R0 w ih =>
    cases i using Fin.cases with
    | zero => simp [toMatrix,Fin.firstNonzElt,pivots]
    | succ p =>
      simp [toMatrix,Fin.firstNonzElt] at hrow ⊢
      rcases hrow with ⟨x,hx⟩
      have h1 : ¬ Fin.allZero (R0.toMatrix p) := by
        cases x using Fin.cases with
        | zero =>
          simp at hx
        | succ p =>
          simp at hx
          simp
          use p
      have h2 := ih p h1
      simp only [pivots,List.mem_map,Subtype.mk.injEq, Prod.mk.injEq,Fin.succ_inj,List.mem_cons]
      right
      use ⟨(p,((Fin.firstNonzElt (R0.toMatrix p) h1)).1.2),by simp [((Fin.firstNonzElt (R0.toMatrix p) h1)).2.2]; exact row_fistNonzElt_val_eq_1 R0 p h1⟩
      simp [h2,Matrix.vecCons]
      congr 1
      apply Fin.firstNonzElt_eq
      simp

/--If `(i,j)` and `(k,l)` `∈` `REF.pivots`, then `i < k → j < l`-/
lemma pivots_colsAscending_if_rowsAscending (R : RowEchelonForm F m n) : ∀ ind_a ∈ R.pivots, ∀ ind_b ∈ R.pivots, ind_a.1.1 < ind_b.1.1 → ind_a.1.2 < ind_b.1.2 := by
  induction R with
  | nil => simp [pivots]
  | pad R0 ih =>
    simp [pivots]
    intro i' j' _ i j hij ijpl hii' hjj' k' l' _ k l hkl klpl hkk' hll' hi'k'
    have := ih ⟨(i,j),hij⟩ ijpl ⟨(k,l),hkl⟩ klpl
    simp at this
    rw [hii',hkk'] at this
    have := this hi'k'
    rw [← hjj',← hll']
    exact Fin.succ_lt_succ_iff.mpr this
  | extend R0 w ih =>
    dsimp [pivots]
    intro ⟨(i,j),hij⟩ ijpl ⟨(k,l),hkl⟩ klpl
    simp at ijpl klpl
    rcases ijpl with ⟨hi,hj⟩|h2
    · rcases klpl with ⟨hk,_⟩|h3
      · simp [hi,hk]
      · simp
        rcases h3 with ⟨a,b,_,_,hbl⟩
        rw [hi,hj]
        intro
        rw [← hbl]
        exact Fin.succ_pos b
    · rcases klpl with ⟨hk,_⟩|h3
      · simp [hk]
      · rcases h2 with ⟨a,b,⟨hab,abpl⟩,hai,hbj⟩
        rcases h3 with ⟨c,d,⟨hcd,cdpl⟩,hck,hdl⟩
        have := ih ⟨(a,b),hab⟩ abpl ⟨(c,d),hcd⟩ cdpl
        simp_rw [← hai,← hbj,← hck,← hdl]
        intro hac
        rw [Fin.succ_lt_succ_iff] at hac ⊢
        exact this hac

/--If `(i,j)` and `(k,l)` `∈` `REF.pivots`, then `j < l → i < k`-/
lemma pivots_rowsAscending_if_colsAscending (R : RowEchelonForm F m n) : ∀ ind_a ∈ R.pivots, ∀ ind_b ∈ R.pivots, ind_a.1.2 < ind_b.1.2 → ind_a.1.1 < ind_b.1.1 := by
  intro ind_a ha ind_b hb h1
  contrapose h1
  push_neg at h1 ⊢
  rcases (lt_or_eq_of_le h1) with h1|h1
  · exact Fin.le_of_lt (pivots_colsAscending_if_rowsAscending R ind_b hb ind_a ha h1)
  · by_contra h2
    push_neg at h2
    have h3 := zerosBeforePivot R ind_b hb ind_a.1.2 h2
    rw [h1] at h3
    have h4 := ind_a.2
    simp at h4
    rw [h3] at h4
    exact zero_ne_one h4

/--If `(i,j)` and `(k,l)` `∈` `REF.pivots`, then `i < k ↔ j < l`-/
lemma pivots_colsAscending_iff_rowsAscending (R : RowEchelonForm F m n) : ∀ ind_a ∈ R.pivots, ∀ ind_b ∈ R.pivots, ind_a.1.1 < ind_b.1.1 ↔ ind_a.1.2 < ind_b.1.2 :=
  fun x hx y hy => ⟨pivots_colsAscending_if_rowsAscending R x hx y hy,pivots_rowsAscending_if_colsAscending R x hx y hy⟩

/--REF PROPERTY 3 : In an REF, the pivot columns are arranged in ascending order-/
theorem pivots_colsAscending (R : RowEchelonForm F m n) (i j : Fin R.pivots.length) (hij : i < j) : (R.pivots.get i).1.2 < (R.pivots.get j).1.2 := by
  have h1 := pivots_pivotInd_eq_pivotRows R i
  have h2 := pivots_pivotInd_eq_pivotRows R j
  rw [← Fin.val_eq_val] at h1 h2
  simp at h1 h2
  rw [Fin.lt_iff_val_lt_val] at hij
  rw [← h1,← h2] at hij
  rw [← Fin.lt_iff_val_lt_val] at hij
  exact pivots_colsAscending_if_rowsAscending R (R.pivots.get i) (List.get_mem _ i.1 i.2) (R.pivots.get j) (List.get_mem _ j.1 j.2) hij

/--REF PROPERTY 3 : Any row that is all zeros is at the bottom of the REF-/
theorem t5 (R : RowEchelonForm F m n) (i j : Fin m) (hi : ¬ Fin.allZero (R.toMatrix i)) (hj : Fin.allZero (R.toMatrix j)) : i < j := by sorry

end RowEchelonForm



/--Row recursor for matrices-/
def Matrix.rowRec {motive : {m : Nat} → Matrix (Fin m) α F → Sort _}
  (zero : (M : Matrix (Fin 0) α F) → motive M)
  (succ : {k : Nat} → (ih : (M : Matrix (Fin k) α F) → motive M) → ((M : Matrix (Fin k.succ) α F) → motive M)) :
  {m : Nat} → (M : Matrix (Fin m) α F) → motive M :=
  fun {m} ↦
  match m with
  | 0 => zero
  | _+1 => succ (Matrix.rowRec zero succ)



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

def elemMat (E : ElemOp F m) : Matrix (Fin m) (Fin m) F :=
  match E with
  | scalarMul c _ i => (1 : Matrix _ _ _).updateRow i (Function.update 0 i c)
  | rowSwap i j => ((1 : Matrix _ _ _).updateRow i (Function.update 0 j 1)).updateRow j (Function.update 0 i 1)
  | rowMulAdd c i j _ => (1 : Matrix _ _ _).updateRow i (Function.update (Function.update 0 i 1) j c)

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

def ElemOp.firstkRows_promote_succ (E : ElemOp F m) : ElemOp F m.succ :=
  match E with
  | scalarMul c hc i => scalarMul c hc (i.castLE (Nat.le_succ m))
  | rowSwap i j => rowSwap (i.castLE (Nat.le_succ m)) (j.castLE (Nat.le_succ m))
  | rowMulAdd c i j hij => rowMulAdd c (i.castLE (Nat.le_succ m)) (j.castLE (Nat.le_succ m)) (by simp [hij])

def ElemOp.list_firstkRows_promote_succ (l : List (ElemOp F m)) : List (ElemOp F m.succ) :=
  match l with
  | [] => []
  | E::tail => E.firstkRows_promote_succ::(list_firstkRows_promote_succ tail)

/--Appends the given row to the bottom of the matrix-/
def Matrix.append_row (M : Matrix (Fin m) (Fin n) α) (v : (Fin n) → α) : Matrix (Fin (m+1)) (Fin n) α :=
  Fin.append M (row (Fin 1) v)

/--Operates a list of `ElemOp`s on a matrix, starting from the rightmost-/
abbrev ElemOp.list_onMatrix (l : List (ElemOp F m)) (A : Matrix (Fin m) (Fin n) F) : Matrix (Fin m) (Fin n) F :=
  match l with
  | [] => A
  | E::tail => E.onMatrix (list_onMatrix tail A)

/--Converts a list of `ElemOp`s into their corresponding elementary matrices-/
abbrev ElemOp.list_to_elemMat_list (l : List (ElemOp F m)) : List (Matrix (Fin m) (Fin m) F) :=
  match l with
  | [] => []
  | E::tail => E.elemMat::(list_to_elemMat_list tail)

/--Performs the product of all matrices in the given list, and then multiplies the product to the left of the given matrix-/
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
  rowRec (F:=F) (motive := fun {m} M => {i : Fin m} → M i j = 1 → (Matrix (Fin m) (Fin n) F)×(List (ElemOp F m)))
    (zero := fun M {i} _ => (M,[]))
    (succ := fun {k} ih A {i} hij =>
      if hi' : i.val = k then (A,[]) else
      let B := A.firstkRows k (Nat.le_succ k)
      have hi : i.val < k := Fin.val_lt_last (Ne.symm (Fin.ne_of_val_ne fun a ↦ hi' (id (Eq.symm a))))
      have hb : B ⟨i,hi⟩ j = 1 := by
        unfold_let
        unfold firstkRows
        simp [hij]
      let C := ih B hb
      let D := (ElemOp.rowMulAdd (-(A k j)) k i (by intro h; rw [←h] at hi'; simp at hi')).onMatrix A
      let elist := (ElemOp.rowMulAdd (-(A k j)) k i (by intro h; rw [←h] at hi'; simp at hi'))::(ElemOp.list_firstkRows_promote_succ C.2)
      let r := D.1 k
      (append_row C.1 r,elist))
    A hij

lemma Matrix.eltColBelow_l1 (A : Matrix (Fin m) (Fin n) F) (hij : A i j = 1) : ElemOp.list_onMatrix (eltColBelow A hij).2 A = (eltColBelow A hij).1 := by
  induction A using Matrix.rowRec with
  | zero M => have := Fin.pos i; contradiction
  | succ ih M => sorry

/--Deletes the first row of a matrix-/
def Matrix.del_1stRow (M : Matrix (Fin (m+1)) (Fin n) F) : Matrix (Fin m) (Fin n) F :=
  M.submatrix (fun l => ⟨l+1,Nat.add_lt_of_lt_sub l.2⟩) (·)

/--Deletes the first column of a matrix-/
def Matrix.del_1stCol (M : Matrix (Fin m) (Fin (n+1)) F) : Matrix (Fin m) (Fin n) F :=
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

-------------------------Row Echelon Form section ends here------------------------------------------------------------------------------------------------------------------------------------
-------------------------Row Reduced Echelon Form section begins here--------------------------------------------------------------------------------------------------------------------------

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

lemma RowEchelonForm.pivots_zerosAtPivots {R : RowEchelonForm F m n} {v : Fin n → F} (hv : R.zerosAtPivots v) :
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

variable (F) in
/--A custom Type for all matrices in RREF.-/
def RowReducedEchelonForm (m n : Nat) := {R : RowEchelonForm F m n // R.isReduced}

--in RREF.toMatrix, any entry above the pivot in the pivot column is 0
lemma RowReducedEchelonForm.zerosAbovePivot (R : RowReducedEchelonForm F m n) : ∀ ind ∈ R.1.pivots, ∀ k < ind.1.1, R.1.toMatrix k ind.1.2 = 0 := by
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
        exact RowEchelonForm.pivots_zerosAtPivots hR.1 ⟨(a,b),hab⟩ abpl
      | succ p =>
        exact ih ⟨R0,hR.2⟩ a b p (Fin.succ_lt_succ_iff.mp hk) hR.2 hab abpl

/--RREF PROPERTY : In RREF.toMatrix, any entry in the pivot column apart from the pivot is 0 -/
theorem RowReducedEchelonForm.zerosAboveAndBelowPivot (R : RowReducedEchelonForm F m n) : ∀ ind ∈ R.1.pivots, ∀ k ≠ ind.1.1, R.1.toMatrix k ind.1.2 = 0 := by
  intro ind hind k hk
  rw [ne_iff_lt_or_gt] at hk
  rcases hk with hk|hk
  · exact zerosAbovePivot R ind hind k hk
  · exact RowEchelonForm.zerosBelowPivot R.1 ind hind k hk

section
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



@[simp]
lemma RowEchelonForm.zero_rows_cols_nil (R : RowEchelonForm F 0 0) : R = nil := by
  match R with
  | nil => rfl

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

/--An REF that is formed from iterated paddings is in RREF-/
theorem RowEchelonForm.pad_isReduced : (Nat.iterate_ind (α := fun i => RowEchelonForm F m i) pad k nil).isReduced := by
  induction k with
    | zero => simp; trivial
    | succ n ih => rw [Nat.iterate_ind_succ,Nat.iterate_ind_commute_self,Function.comp_apply,isReduced]; exact ih

/--Given an RREF `R0` and a vector `v` by which the RREF is to be extended, this function eliminates all the entries in v that
correspond to the pivot columns of R0, using elementary row operations.-/
def RowReducedEchelonForm.eltPivotColEntries (R : RowReducedEchelonForm F m n) (v : Fin n → F) : Fin n → F :=
  match m,n,R with
  | _,_,⟨.nil,_⟩ => v
  | _,_,⟨.pad R0,hR0⟩ => Fin.cons (v 0) (eltPivotColEntries ⟨R0,hR0⟩ (Fin.tail v))
  | _,_,⟨.extend R0 v',hR0⟩ =>
    let w := eltPivotColEntries ⟨R0,hR0.2⟩ (Fin.tail v)
    Fin.cons 0 (w + (-(v 0))•v')

lemma RowEchelonForm.zerosAtPivots_linearCombination (R : RowEchelonForm F m n) (hv : R.zerosAtPivots v) (hw : R.zerosAtPivots w) (c : F) :
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
          convert R0.zerosAtPivots_linearCombination h1 h2 (-(v 0)) using 2
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



def Matrix.toRowReducedEchelonForm (M : Matrix (Fin m) (Fin n) F) : RowReducedEchelonForm F m n := M.toRowEchelonForm.backSubstitution
