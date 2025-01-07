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

def v2 : Fin 0 → ℚ := ![]

lemma hv2 : (allZero v2) := by decide
-- #eval allZero_not_ex_nonzero hv2

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
lemma row_firstNonzElt_eq_one (R : RowEchelonForm F m n) (i : Fin m) (hrow : ¬ Fin.allZero (R.toMatrix i)) : (Fin.firstNonzElt (R.toMatrix i) hrow).1.1 = 1 := by
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

--'let' pattern matching is being very annoying here
/--Given a matrix in REF, the first nonzero entry of any nonzero row is a pivot-/
theorem row_firstNonzElt_eq_pivot (R : RowEchelonForm F m n) (i : Fin m) (hrow : ¬ Fin.allZero (R.toMatrix i)) :
  let data := Fin.firstNonzElt (R.toMatrix i) hrow
  ⟨(i,data.1.2),by simp [data.2.2]; rw [← row_firstNonzElt_eq_one R i hrow]⟩ ∈ R.pivots := by
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
    use ⟨(i,((Fin.firstNonzElt (R0.toMatrix i) h1)).1.2),by simp [((Fin.firstNonzElt (R0.toMatrix i) h1)).2.2]; exact row_firstNonzElt_eq_one R0 i h1⟩
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
      use ⟨(p,((Fin.firstNonzElt (R0.toMatrix p) h1)).1.2),by simp [((Fin.firstNonzElt (R0.toMatrix p) h1)).2.2]; exact row_firstNonzElt_eq_one R0 p h1⟩
      simp [h2,Matrix.vecCons]
      congr 1
      apply Fin.firstNonzElt_eq
      simp

/--if `(i,j)` and `(k,l)` `∈` `REF.pivots`, then `i < k → j < l`-/
lemma pivots_colsAscending_if_rowsAscending (R : RowEchelonForm F m n) : ∀ ind_a ∈ R.pivots, ∀ ind_b ∈ R.pivots, ind_a.1.1 < ind_b.1.1 → ind_a.1.2 < ind_b.1.2 := by
  induction R with
  | nil => simp [pivots]
  | pad R0 ih =>
    simp [pivots]
    intro i' j' hi'j' i j hij ijpl hii' hjj' k' l' hk'l' k l hkl klpl hkk' hll' hi'k'
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
    · rcases klpl with ⟨hk,hl⟩|h3
      · simp [hi,hk]
      · simp
        rcases h3 with ⟨a,b,⟨hab,abpl⟩,hak,hbl⟩
        rw [hi,hj]
        intro hk
        rw [← hbl]
        exact Fin.succ_pos b
    · rcases klpl with ⟨hk,hl⟩|h3
      · simp [hk]
      · rcases h2 with ⟨a,b,⟨hab,abpl⟩,hai,hbj⟩
        rcases h3 with ⟨c,d,⟨hcd,cdpl⟩,hck,hdl⟩
        have := ih ⟨(a,b),hab⟩ abpl ⟨(c,d),hcd⟩ cdpl
        simp_rw [← hai,← hbj,← hck,← hdl]
        intro hac
        rw [Fin.succ_lt_succ_iff] at hac ⊢
        exact this hac

/--if `(i,j)` and `(k,l)` `∈` `REF.pivots`, then `j < l → i < k`-/
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

lemma pivots_colsAscending_iff_rowsAscending (R : RowEchelonForm F m n) : ∀ ind_a ∈ R.pivots, ∀ ind_b ∈ R.pivots, ind_a.1.1 < ind_b.1.1 ↔ ind_a.1.2 < ind_b.1.2 :=
  fun x hx y hy => ⟨pivots_colsAscending_if_rowsAscending R x hx y hy,pivots_rowsAscending_if_colsAscending R x hx y hy⟩

/--REF PROPERTY 2 : In an REF, the pivot columns are arranged in ascending order-/
theorem pivots_colsAscending (R : RowEchelonForm F m n) (i j : Fin R.pivots.length) (hij : i < j) : (R.pivots.get i).1.2 < (R.pivots.get j).1.2 := by
  have h1 := pivots_pivotInd_eq_pivotRows R i
  have h2 := pivots_pivotInd_eq_pivotRows R j
  rw [← Fin.val_eq_val] at h1 h2
  simp at h1 h2
  rw [Fin.lt_iff_val_lt_val] at hij
  rw [← h1,← h2] at hij
  rw [← Fin.lt_iff_val_lt_val] at hij
  exact pivots_colsAscending_if_rowsAscending R (R.pivots.get i) (List.get_mem _ i.1 i.2) (R.pivots.get j) (List.get_mem _ j.1 j.2) hij

def truncation (R : RowEchelonForm F m n) : (a : Nat)×(RowEchelonForm F a n)×{b : Nat // a+b = m} :=
  match R with
  | nil => ⟨0,⟨nil,⟨m,by simp⟩⟩⟩
  | pad R =>
    let ⟨a,⟨R',⟨b,hab⟩⟩⟩ := truncation R
    ⟨a,⟨pad R',⟨b,hab⟩⟩⟩
  | extend R v =>
    let ⟨a,⟨R',⟨b,hab⟩⟩⟩ := truncation R
    ⟨a+1,⟨extend R' v,⟨b,by rw [← hab]; exact Nat.add_right_comm a 1 b⟩⟩⟩

def r2 : RowEchelonForm Rat 3 2 := extend (extend (nil) ![]) ![0]
#eval truncation r2

namespace Nat

/--Iterates a function that takes a term of type `α i` to a term of type `α (i+1)`-/
@[simp]
def iterate_ind {α : ℕ → Sort*} (f : {i : ℕ} → α i → α (i+1)) (n : ℕ) (a : α 0) : α n :=
  match n with
  | 0 => a
  | k+1 => iterate_ind f k (f a)

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
lemma zero_rows_cols_nil (R : RowEchelonForm F m 0) : R = nil := by
  match R with
  | nil => rfl

@[simp]
lemma truncation_nil (R : RowEchelonForm F m 0) : R.truncation = ⟨0,⟨nil,⟨m,by simp⟩⟩⟩ := by simp; rfl

lemma zero_rows_pad (R : RowEchelonForm F 0 n) :
  R = Nat.iterate_ind (α:=fun n => RowEchelonForm F 0 n) pad n (nil) := by
    induction n with
    | zero => simp
    | succ n ih =>
      match R with
      | pad R0 =>
        have h1 := congrArg pad (ih R0)
        rw [Nat.iterate_ind_succ,Nat.iterate_ind_commute_self]
        exact h1

lemma truncation_zero_rows (R : RowEchelonForm F 0 n) : R.truncation = ⟨0,⟨Nat.iterate_ind (α:=fun n => RowEchelonForm F 0 n) pad n (nil),⟨0,rfl⟩⟩⟩ := by
  induction n with
  | zero =>
    rw [zero_rows_cols_nil R,truncation]
    rfl
  | succ n ih =>
    match R with
      | pad R0 =>
        simp only [truncation]
        have h1 := ih R0
        rw [h1,Nat.iterate_ind_succ,Nat.iterate_ind_commute_self,Function.comp_apply]

end RowEchelonForm

/--Appends the given row to the bottom of the matrix-/
def Matrix.append_row (M : Matrix (Fin m) (Fin n) α) (v : (Fin n) → α) : Matrix (Fin (m+1)) (Fin n) α :=
  Fin.snoc M v

#check Fin.lastCases
#check Fin.snoc_last

lemma Matrix.append_row_castSucc (M : Matrix (Fin m) (Fin n) α) (v : (Fin n) → α) (i : Fin m) : (append_row M v) i.castSucc = M i := by
  dsimp [append_row]
  rw [Fin.snoc_castSucc]

lemma Matrix.append_row_last (M : Matrix (Fin m) (Fin n) α) (v : (Fin n) → α) : (append_row M v) m = v := by
  dsimp [append_row]
  simp

abbrev Matrix.append_k_zeroRows (M : Matrix (Fin m) (Fin n) F) (k : Nat) : Matrix (Fin (m+k)) (Fin n) F :=
  match k with
  | 0 => M
  | p+1 => append_row (append_k_zeroRows M p) 0

lemma Matrix.append_k_zeroRows_0 (M : Matrix (Fin m) (Fin n) F) : M.append_k_zeroRows 0 = M := rfl

lemma Matrix.row_ext (M : Matrix m n α) (N : Matrix m n α) : (∀ i : m, M i = N i) → M = N := by
  intro h
  ext i j; revert j
  simp [h]

@[simp]
lemma RowEchelonForm.append_k_zeroRows_nil {k m : ℕ} : (nil (F:=F) (m:=m)).toMatrix.append_k_zeroRows k = (nil (m:=m+k)).toMatrix := by
  induction k with
    | zero => rfl
    | succ p ih =>
      rw [Matrix.append_k_zeroRows,ih,Matrix.append_row]
      apply Matrix.row_ext
      intro i
      cases i using Fin.lastCases with
      | last => simp [toMatrix]
      | cast q => simp [toMatrix]

lemma RowEchelonForm.pad_append_1_zeroRows (R0 : RowEchelonForm F m n) (R : RowEchelonForm F m.succ n) (hR : R.toMatrix = R0.toMatrix.append_k_zeroRows 1) :
  R.pad.toMatrix = R0.pad.toMatrix.append_k_zeroRows 1 := by
  simp [toMatrix]
  rw [hR,Matrix.append_k_zeroRows,Matrix.append_k_zeroRows,Matrix.append_k_zeroRows,Matrix.append_k_zeroRows]
  ext i j
  sorry

abbrev Matrix.cast (h1 : m = k) (h2 : n = l) : Matrix (Fin m) (Fin n) α → Matrix (Fin k) (Fin l) α :=
  match h1,h2 with
  | rfl,rfl => id

lemma Matrix.cast_eq (h1 h3 : m=k) (h2 h4 : n=l) (A : Matrix (Fin m) (Fin n) α) :
  A.cast h1 h2 = A.cast h3 h4 := by rfl

@[simp]
lemma Matrix.cast_append (h1 : m = k) (h2 : n = l) (M : Matrix (Fin m) (Fin n) F) (v : (Fin n) → F) :
  Matrix.cast (congrArg Nat.succ h1) h2 (M.append_row v) = (Matrix.cast h1 h2 M).append_row (fun i => v (i.cast (Eq.symm h2))) := by
  subst h1 h2
  rfl

lemma Matrix.cast_append_k_zeroRows (h1 : m = k) (h2 : n = l) (M : Matrix (Fin m) (Fin n) F) (p : ℕ) :
  Matrix.cast (congrFun (congrArg HAdd.hAdd h1) p) (h2) (M.append_k_zeroRows p) = (M.cast h1 h2).append_k_zeroRows p := by
  induction p with
  | zero => simp
  | succ q ih => rw [Matrix.cast_append,ih]; rfl

#check Fin.val_eq_of_eq

lemma RowEchelonForm.nonZeroRows_l1 (R : RowEchelonForm F m n) :
  R.toMatrix = (Matrix.append_k_zeroRows R.truncation.2.1.toMatrix R.truncation.2.2).cast (R.truncation.2.2.2) (rfl) := by
  induction R with
  | @nil k =>
    rw [truncation]
    simp only [SubMulAction.subtype_eq_val]
    induction k with
    | zero => rfl
    | succ p ih =>
      rw [Matrix.append_k_zeroRows,Matrix.cast_append,← ih,Matrix.append_row]
      apply Matrix.row_ext
      intro i
      cases i using Fin.lastCases with
      | last => simp [toMatrix]; exact List.ofFn_inj.mp rfl
      | cast q => simp [toMatrix]
  | @pad k l R0 ih => -- split into multiple lemmas
    induction k with
    | zero =>
      simp [truncation]
      have h1 := truncation_zero_rows R0
      conv =>
        enter [2]
      have h2 : R0.toMatrix = (((Nat.iterate_ind (α:=fun n => RowEchelonForm F 0 n) (fun {i} ↦ pad) l nil)).toMatrix.append_k_zeroRows 0) := by
        -- have := Matrix.cast_append_k_zeroRows _ (rfl) (R0.truncation.snd.1.toMatrix) (↑R0.truncation.snd.2)
        have h3 : Matrix.cast (by simp [h1]; rfl) (rfl) (R0.truncation.snd.1.toMatrix.append_k_zeroRows ↑R0.truncation.snd.2) = ((R0.truncation.snd.1.toMatrix.cast (by simp [h1]) (rfl)).append_k_zeroRows ↑R0.truncation.snd.2) :=
          Matrix.cast_append_k_zeroRows _ (rfl) (R0.truncation.snd.1.toMatrix) (↑R0.truncation.snd.2)
        rw [ih]
        have h4 : R0.truncation.2.2.1 = 0 := by rw [h1]
        have h5 : 0 + R0.truncation.2.2.1 = 0 := by simp [h4]
        sorry
      sorry
    | succ p ih => sorry
  | extend R0 w ih => -- extend and append_k_zerorows commute
    sorry

-- def mat := !![1,2,3;4,5,6;7,8,(9:Rat)]
-- #eval (Matrix.vecCons ![-1,-2,(-3:Rat)] mat)
-- def v1 := ![0,0,(0:Rat)]
-- #eval FinVec.map (fun r => (Fin.cons 0 r : Fin _ → _)) mat
-- #eval FinVec.map (fun r => (Matrix.vecCons 0 r)) mat
