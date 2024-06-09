import GaussElim.ge_test2vec
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection

/-
Preliminary lemmas
1.
2. when a matrix is multiplied by the list of elementary matrices outputted by
  the rref function, it gives the same result as the 2nd output of the rref function (How?)
3. each element of the list is an elementary matrix
4.
-/

/-
Proving that a matrix that goes through the row-reduced echelon form algorithm is in its
row-reduced echelon form

1. Show that the result is row-reduced
  a. each row is either all 0 or has its first nonzero entry as 1
    aa. The nonzero entry corresponding to the first nonzero column is the first nonzero
      entry of the corresponding row
    ab. multiplication of M with findpivot_ij i j makes it so that the (i,j)th entry is
      either 0 or 1
    ac. the (i,j)th step of rowEchelonStep does not change the rows and columns before i
      and j
    ad. the (i,j)th step of rowEchelonStep makes the (i,j)th entry as 0 or 1 and every
      entry below it 0


2. Show that the zero rows are last

3. Show that the columns corresponding to the nonzero rows are in increasing order

-/

open BigOperators
namespace ElemOp

variable (M : Matrix (Fin m) (Fin n) Rat) (hm : m > 0) (hn : n > 0)

lemma rval_ival_lt (i : Fin m) (r : Fin (m-i-1)) : r.1+i.1+1 < m :=
  Nat.add_assoc _ _ _ ▸ (Nat.add_lt_of_lt_sub (Eq.subst (Nat.sub_sub m i.1 1) (r.2)))

lemma elimEltBelow (hpiv : M i j = 1) (r : Fin (m-i-1)) :
  (ElemOpOnMatrix (rowMulAdd (-M ⟨r+i+1,rval_ival_lt i r⟩ j) ⟨r+i+1,rval_ival_lt i r⟩ i) M) ⟨r+i+1,rval_ival_lt i r⟩ j = 0 := by
  rw [ElemOpOnMatrix]; simp [hpiv]

lemma elt_elimColBelow_eq_rowMulAdd : E ∈ elimColBelow_ij M i j → ∃ r, rowMulAdd (-M ⟨↑r+↑i+1,rval_ival_lt i r⟩ j) ⟨↑r+↑i+1,rval_ival_lt i r⟩ i = E := by
  unfold elimColBelow_ij
  rw [List.mem_ofFn]
  simp

theorem elimColBelow_length : (elimColBelow_ij M i j).length = m-i-1 := by
  rw [elimColBelow_ij]; simp

lemma elimColBelow_get_eq_rowMulAdd (i : Fin m) (j : Fin n) (r : Fin (m-i-1)) :
  (elimColBelow_ij M i j).get (r.cast (Eq.symm (elimColBelow_length M))) = rowMulAdd (-M ⟨↑r+↑i+1,rval_ival_lt i r⟩ j) ⟨↑r+↑i+1,rval_ival_lt i r⟩ i := by
  unfold elimColBelow_ij
  simp

lemma elimColbelow_get_elim_r (i : Fin m) (j : Fin n) (r : Fin (m-i-1)) (hpiv : M i j = 1) :
  (ElemOpOnMatrix ((elimColBelow_ij M i j).get (r.cast (Eq.symm (elimColBelow_length M)))) M) ⟨r+i+1,rval_ival_lt i r⟩ j = 0 := by
  rw [elimColBelow_get_eq_rowMulAdd,elimEltBelow _ hpiv]

lemma elimColBelow_get_elim_notr (i : Fin m) (j : Fin n) (r : Fin (m-i-1)) (s : Fin (m-i-1)) (hsr : s≠r) :
  (ElemOpOnMatrix ((elimColBelow_ij M i j).get (r.cast (Eq.symm (elimColBelow_length M)))) M) ⟨s+i+1,rval_ival_lt i s⟩ j = M ⟨s+i+1,rval_ival_lt i s⟩ j := by
  rw [elimColBelow_get_eq_rowMulAdd]
--Need to prove rowmuladd doesnt affect other rows

example (i : Fin m) (j : Fin n) (r : Fin (m-i-1)) (hpiv : M i j = 1) :
  (listElemOpOnMatrix (elimColBelow_ij M i j) M) ⟨r+i+1,rval_ival_lt i r⟩ j = 0 := by
  induction' hl : elimColBelow_ij M i j with elt l hi
  · rw [elimColBelow_ij] at hl; simp at hl
    have h1 := rval_ival_lt i r
    rw [Nat.sub_sub,Nat.sub_eq_iff_eq_add] at hl
    simp_rw [hl] at h1
    simp at h1
    exact Nat.add_le_of_le_sub hm (Nat.le_sub_one_of_lt i.2)
  · unfold listElemOpOnMatrix
    have h1 : elt ∈ elimColBelow_ij M i j := by simp [hl]
    obtain ⟨s,helt⟩ := elt_elimColBelow_eq_rowMulAdd M h1
    rw [← helt, ElemOpOnMatrix]; simp






lemma rval_ival_lt (i : Fin m) (r : Fin (m-i-1)) : r.1+(i.1+1) < m :=
  (Nat.add_lt_of_lt_sub (Eq.subst (Nat.sub_sub m i.1 1) (r.2)))

#check Finset.fin
#check Finset.univ
#check Finset (Fin m)
def s : Finset (Fin m) := Finset.univ
#check ⟨0,hm⟩ ∈ s

def I:Matrix (Fin m) (Fin m) Rat := 1

example : ∑ j : Fin m, 1 = ∑ j ∈ (Finset.univ : Finset (Fin m)), 1 := by simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

example (i : Fin m) (j : Fin n) (hpiv : M i j = 1) (r : Fin (m - i - 1)) :
  ((elemMat (rowMulAdd (-M ⟨r.1+i+1,rval_ival_lt i r⟩ j) ⟨r.1+i+1,rval_ival_lt i r⟩ i)) * M) ⟨r.1+i+1,rval_ival_lt i r⟩ j = 0 := by
  have hri : ↑r + ↑i + 1 < m := (rval_ival_lt i r)
  unfold elemMat ElemOpOnMatrix
  simp [-Matrix.diagonal_one]
  rw [Matrix.diagonal_one,Matrix.mul_apply]
  set I:Matrix (Fin m) (Fin m) Rat := 1
  have h1 : I.updateRow ⟨↑r + ↑i + 1,hri⟩ (I ⟨↑r + ↑i + 1,hri⟩ + -M ⟨↑r + ↑i + 1,hri⟩ j • I i) ⟨↑r + ↑i + 1,hri⟩ = (I ⟨↑r + ↑i + 1,hri⟩ + -M ⟨↑r + ↑i + 1,hri⟩ j • I i) := Matrix.updateRow_self
  have h0 : ∀ (k : Fin m), k ≠ i ∧ k ≠ ⟨↑r+↑i+1,hri⟩ → Matrix.updateRow I ⟨↑r + ↑i + 1,_⟩ (((I ⟨↑r + ↑i + 1,_⟩) + -(M ⟨↑r + ↑i + 1,_⟩ j) • (I i))) ⟨↑r+↑i+1,hri⟩ k = 0 := by
    intro k ⟨kni,knri⟩
    set c := M ⟨↑r + ↑i + 1, _⟩ j
    have h2 : (I ⟨↑r + ↑i + 1,hri⟩ + -M ⟨↑r + ↑i + 1,hri⟩ j • I i) k = 0 := by
      rw [Pi.add_apply,Pi.smul_apply]
      have p1 : I ⟨↑r + ↑i + 1, hri⟩ k = 0 := by unfold_let; apply Matrix.one_apply_ne (Ne.symm knri)
      have p2 : I i k = 0 := by unfold_let; apply Matrix.one_apply_ne (Ne.symm kni)
      rw [p1,p2]; simp
    have := congrFun h1 k
    rw [h2] at this
    exact this
  have h0' : I.updateRow ⟨↑r + ↑i + 1, ⋯⟩ (I ⟨↑r + ↑i + 1, ⋯⟩ + -(M ⟨↑r + ↑i + 1, ⋯⟩ j • I i)) ⟨↑r + ↑i + 1, ⋯⟩ i * M i j
            + I.updateRow ⟨↑r + ↑i + 1, ⋯⟩ (I ⟨↑r + ↑i + 1, ⋯⟩ + -(M ⟨↑r + ↑i + 1, ⋯⟩ j • I i)) ⟨↑r + ↑i + 1, ⋯⟩ ⟨↑r + ↑i + 1, ⋯⟩ * M ⟨↑r + ↑i + 1, ⋯⟩ j = 0 := by
    rw [hpiv]
    have h2 : I.updateRow ⟨↑r + ↑i + 1,hri⟩ (I ⟨↑r + ↑i + 1,hri⟩ + -(M ⟨↑r + ↑i + 1,hri⟩ j • I i)) ⟨↑r + ↑i + 1,hri⟩ i = M ⟨↑r + ↑i + 1,hri⟩ j := by
      unfold_let









example (i : Fin m) (j : Fin n) (hpiv : M i j = 1) (r : Fin (m - i - 1)) (k : Fin m) (hk : k > (r.val+i.val+1)) :
  ((elemMat (rowMulAdd (-M ⟨r.1+i+1,rval_ival_lt i r⟩ j) ⟨r.1+i+1,rval_ival_lt i r⟩ i)) * M) k j = 0 := by
  have hri : ↑r + ↑i + 1 < m := (rval_ival_lt i r)
  unfold elemMat ElemOpOnMatrix
  simp [-Matrix.diagonal_one]
  rw [Matrix.diagonal_one,Matrix.mul_apply]
  set I:Matrix (Fin m) (Fin m) Rat := 1
  have h1 : I.updateRow ⟨↑r + ↑i + 1,hri⟩ (I ⟨↑r + ↑i + 1,hri⟩ + -M ⟨↑r + ↑i + 1,hri⟩ j • I i) k = I k := Matrix.updateRow_ne (M:=I) (ne_of_gt hk)
  -- have h0 : ∀ (l : Fin m), l ≠ k ∧ l ≠ ⟨↑r+↑i+1,hri⟩ → Matrix.updateRow I ⟨↑r + ↑i + 1,_⟩ (((I ⟨↑r + ↑i + 1,_⟩) + -(M ⟨↑r + ↑i + 1,_⟩ j) • (I i))) k l = 0 := by
  --   intro l ⟨lnk,lnri⟩
  --   set c := M ⟨↑r + ↑i + 1, _⟩ j
  --   have h2 : I k l = 0 := by unfold_let; apply Matrix.one_apply_ne (Ne.symm lnk)
  --   exact h2 ▸ congrFun h1 l
  have h0 : ∀ (l : Fin m), l ≠ i ∧ l ≠ k → Matrix.updateRow I ⟨↑r + ↑i + 1,_⟩ (((I ⟨↑r + ↑i + 1,_⟩) + -(M ⟨↑r + ↑i + 1,_⟩ j) • (I i))) k l = 0 := by
    intro l ⟨lnk,lni⟩
    set c := M ⟨↑r + ↑i + 1, _⟩ j
    have h2 : I k l = 0 := by unfold_let; apply Matrix.one_apply_ne (Ne.symm lnk)
    exact h2 ▸ congrFun h1 l
  -- have h2 : I.updateRow ⟨↑r + ↑i + 1, hri⟩ (I ⟨↑r + ↑i + 1, hri⟩ + -(M ⟨↑r + ↑i + 1, hri⟩ j • I i)) k k * M k j
  --   + I.updateRow ⟨↑r + ↑i + 1, hri⟩ (I ⟨↑r + ↑i + 1, hri⟩ + -(M ⟨↑r + ↑i + 1, hri⟩ j • I i)) k ⟨↑r + ↑i + 1, hri⟩ * M ⟨↑r + ↑i + 1, hri⟩ j = 0 := by
  --     have h3 : I.updateRow ⟨↑r + ↑i + 1,hri⟩ (I ⟨↑r + ↑i + 1,hri⟩ + -(M ⟨↑r + ↑i + 1,hri⟩ j • I i)) k k = 1 := by
  --       have h4 := congrFun h1 k
  --       unfold_let I at h4 ⊢
  --       rw [Matrix.one_apply_eq] at h4
  --       convert h4 using 3; simp
  --     rw [h3]; simp
  have h2 : I.updateRow ⟨↑r + ↑i + 1, hri⟩ (I ⟨↑r + ↑i + 1, hri⟩ + -(M ⟨↑r + ↑i + 1, hri⟩ j • I i)) k k * M k j
    + I.updateRow ⟨↑r + ↑i + 1, hri⟩ (I ⟨↑r + ↑i + 1, hri⟩ + -(M ⟨↑r + ↑i + 1, hri⟩ j • I i)) k i * M i j = 0 := by
    have h3 : I.updateRow ⟨↑r + ↑i + 1,hri⟩ (I ⟨↑r + ↑i + 1,hri⟩ + -(M ⟨↑r + ↑i + 1,hri⟩ j • I i)) k k = 1 := by
      have h4 := congrFun h1 k
      unfold_let I at h4 ⊢
      rw [Matrix.one_apply_eq] at h4
      convert h4 using 3; simp
    have h5 : I.updateRow ⟨↑r + ↑i + 1, hri⟩ (I ⟨↑r + ↑i + 1, hri⟩ + -(M ⟨↑r + ↑i + 1, hri⟩ j • I i)) k i


  -- show ∑ l' ∈ (Finset.univ : Finset (Fin m)), I.updateRow ⟨↑r + ↑i + 1, ⋯⟩ (I ⟨↑r + ↑i + 1, ⋯⟩ + -(M ⟨↑r + ↑i + 1, ⋯⟩ j • I i)) k l' * M l' j = 0
  let s := ((Finset.univ : Finset (Fin m)).erase k).erase ⟨↑r + ↑i + 1, hri⟩
  have hkin : k ∈ (Finset.univ : Finset (Fin m)) := by simp
  have h3 := Finset.add_sum_erase (Finset.univ : Finset (Fin m)) (fun j_1 => I.updateRow ⟨↑r + ↑i + 1, ⋯⟩ (I ⟨↑r + ↑i + 1, ⋯⟩ + -(M ⟨↑r + ↑i + 1, ⋯⟩ j • I i)) k j_1 * M j_1 j) hkin
  have hrin : ⟨↑r + ↑i + 1,hri⟩ ∈ Finset.univ := by simp
  have h3' := Finset.add_sum_erase (Finset.univ : Finset (Fin m)) (fun j_1 => I.updateRow ⟨↑r + ↑i + 1, ⋯⟩ (I ⟨↑r + ↑i + 1, ⋯⟩ + -(M ⟨↑r + ↑i + 1, ⋯⟩ j • I i)) k j_1 * M j_1 j) hrin
  rw [h3']
  -- have : ∑ j_1 : Fin m, I.updateRow ⟨↑r + ↑i + 1, ⋯⟩ (I ⟨↑r + ↑i + 1, ⋯⟩ + -(M ⟨↑r + ↑i + 1, ⋯⟩ j • I i)) k j_1 * M j_1 j
  --       = I.updateRow ⟨↑r + ↑i + 1, ⋯⟩ (I ⟨↑r + ↑i + 1, ⋯⟩ + -(M ⟨↑r + ↑i + 1, ⋯⟩ j • I i)) k k * M k j
  --         + I.updateRow ⟨↑r + ↑i + 1, ⋯⟩ (I ⟨↑r + ↑i + 1, ⋯⟩ + -(M ⟨↑r + ↑i + 1, ⋯⟩ j • I i)) k ⟨↑r + ↑i + 1, hri⟩ * M ⟨↑r + ↑i + 1, hri⟩ j
  --         + ∑ j_1 ∈ s, I.updateRow ⟨↑r + ↑i + 1, ⋯⟩ (I ⟨↑r + ↑i + 1, ⋯⟩ + -(M ⟨↑r + ↑i + 1, ⋯⟩ j • I i)) k j_1 * M j_1 j := by

  -- have h3 : ∑ j_1 : Fin m, I.updateRow ⟨↑r + ↑i + 1, ⋯⟩ (I ⟨↑r + ↑i + 1, ⋯⟩ + -(M ⟨↑r + ↑i + 1, ⋯⟩ j • I i)) k j_1 * M j_1 j
  --   = I.updateRow ⟨↑r + ↑i + 1, ⋯⟩ (I ⟨↑r + ↑i + 1, ⋯⟩ + -(M ⟨↑r + ↑i + 1, ⋯⟩ j • I i)) k k * M k j
  --     + I.updateRow ⟨↑r + ↑i + 1, ⋯⟩ (I ⟨↑r + ↑i + 1, ⋯⟩ + -(M ⟨↑r + ↑i + 1, ⋯⟩ j • I i)) k ⟨↑r + ↑i + 1, hri⟩ * M ⟨↑r + ↑i + 1, hri⟩ j
  --     + ∑ j_1 : Fin m, j_1 ≠ k ∧ j_1 ≠ ⟨↑r + ↑i + 1, hri⟩


--(Nat.add_assoc _ _ _) ▸ (rval_ival_lt i r)

theorem elimColBelow_ij_allZeroBelow (i : Fin m) (j : Fin n) (hpiv : M i j = 1) :
  List.IsSuffix (List.replicate (m-j) 0) (List.ofFn (((elimColBelow_ij M i j).prod * M) · j)) := by
  unfold elimColBelow_ij


theorem rowEchelonStep_reduceRow (i : Fin m) (j : Fin n) :
  (rowEchelonStep M i j) i j = 0 ∨ (rowEchelonStep M i j) i j = 1 := by
  cases h : findPivot_ij M i j with
  | none =>
    unfold rowEchelonStep
    simp [h]
    let M' := botRightij M i j
    have h1 : findNonzCol M' = (colVecofMat M').length := by
      unfold findPivot_ij at h
      unfold_let at h
      rw [dite_eq_left_iff] at h
      contrapose h
      push_neg
      use h
      simp
    unfold findNonzCol at h1
    simp_rw [← Vector.toList_length (colVecofMat M')] at h1
    have h2 := findIdx_notExists_of_eq_length _ _ h1
    simp at h2
    have hi := Nat.zero_lt_sub_of_lt i.2
    have hj := Nat.zero_lt_sub_of_lt j.2
    have h3 := h2 ⟨0,hj⟩ ⟨0,hi⟩
    have h4 : M' ⟨0,hi⟩ ⟨0,hj⟩ = M i j := by
      unfold_let
      unfold botRightij
      simp
    rw [h3] at h4; left; symm; exact h4
  | some l =>
    right
    unfold rowEchelonStep
    simp [h]
    let M' := botRightij M i j
