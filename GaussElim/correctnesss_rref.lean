import GaussElim.ge_test2vec
-- import Mathlib.Algebra.BigOperators.Basic

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

--lemma elemMat_eq_ElemOpOn_I (e : ElemOp (m:=m)) : elemMat e = ElemOpOnMatrix e 1 := by rfl

#check List.prod_cons

lemma ElemOpOnMatrix_mul (e : ElemOp (m:=m)) (A : Matrix (Fin m) (Fin m) Rat) :
  (ElemOpOnMatrix e A)*M = (ElemOpOnMatrix e (A*M)) := by
  apply Matrix.ext
  intro i j
  induction' e with c hc p p q c p q
  · unfold ElemOpOnMatrix
    simp
    by_cases hi:i=p
    · rw [hi]
      simp
      rw [Matrix.mul_apply]
      simp
      rw [Matrix.mul_apply,mul_comm]
      rw [Finset.sum_mul Finset.univ (fun x => A p x * M x j) c]
      simp_rw [mul_comm _ c,mul_assoc]
    · rw [Matrix.updateRow_ne hi,Matrix.mul_apply,Matrix.updateRow_ne hi, Matrix.mul_apply]
  · unfold ElemOpOnMatrix
    simp
    rw [Matrix.mul_apply]
    by_cases hi:i=q
    · simp [hi,Matrix.mul_apply]
    · simp [Matrix.updateRow_ne hi]
      by_cases hi':i=p
      · simp [hi',Matrix.mul_apply]
      · simp [Matrix.updateRow_ne hi',Matrix.mul_apply]
  · unfold ElemOpOnMatrix
    simp [neg_mul]
    rw [Matrix.mul_apply]
    by_cases hi:i=p
    · simp [hi]
      rw [Matrix.mul_apply]
      simp_rw [Rat.add_mul,Finset.sum_add_distrib,Matrix.mul_apply]
      rw [mul_comm,Finset.sum_mul Finset.univ (fun x => A q x * M x j) c]
      simp_rw [mul_comm _ c, mul_assoc]
    · simp [hi]
      rw [Matrix.mul_apply]

theorem ElemOpOnMatrix_eq_elemMatMul (e : ElemOp) : ElemOpOnMatrix e M = (elemMat e)*M := by
  rw [elemMat,ElemOpOnMatrix_mul,Matrix.one_mul]

theorem listElemOpOnMatrix_eq_listprod (l : List (ElemOp (m:=m))) :
  listElemOpOnMatrix l M = (list_mat_of_ElemOp l).prod*M := by
  induction' l with E as ih
  · rw [listElemOpOnMatrix,list_mat_of_ElemOp,List.prod_nil,Matrix.one_mul]
  · rw [listElemOpOnMatrix,list_mat_of_ElemOp,ih,ElemOpOnMatrix_eq_elemMatMul,← Matrix.mul_assoc,List.prod_cons]

lemma rval_ival_lt (i : Fin m) (r : Fin (m-i-1)) : r.1+i.1+1 < m :=
  Nat.add_assoc _ _ _ ▸ (Nat.add_lt_of_lt_sub (Eq.subst (Nat.sub_sub m i.1 1) (r.2)))

lemma elt_elimColBelow_eq_rowMulAdd : E ∈ elimColBelow_ij M i j → ∃ r, E = rowMulAdd (-M ⟨↑r+↑i+1,rval_ival_lt i r⟩ j) ⟨↑r+↑i+1,rval_ival_lt i r⟩ i := by
  unfold elimColBelow_ij
  rw [List.mem_ofFn]
  simp

example (s : Finset α) (f g : α → ℕ) : f = g → ∑ x ∈ s, f x = ∑ x ∈ s, g x := by
  intro h
  apply Finset.sum_congr (rfl:s=s) (fun y _ => congrFun h y)

lemma elimColBelow_elt_commute (e e' : ElemOp) (he : e ∈ elimColBelow_ij M i j) (he' : e' ∈ elimColBelow_ij M i j) (hee' : e ≠ e') :
  e.elemMat * e'.elemMat = e'.elemMat * e.elemMat := by
  obtain ⟨r,hr⟩ := elt_elimColBelow_eq_rowMulAdd M he
  obtain ⟨s,hs⟩ := elt_elimColBelow_eq_rowMulAdd M he'
  set cr := M ⟨↑r + ↑i + 1, ⋯⟩ j with hcr
  set cs := M ⟨↑s + ↑i + 1, ⋯⟩ j with hcs
  rw [hr,hs] at hee' ⊢
  apply Matrix.ext
  intro p q
  rw [Matrix.mul_apply,Matrix.mul_apply]
  have hrs : r.1+i+1≠s+i+1 := by
    simp only [ne_eq, rowMulAdd.injEq, neg_inj, Fin.mk.injEq, add_left_inj, and_true, not_and'] at hee'
    by_cases h0 : r=s
    · have h1 := hee' h0
      rw [hcr,hcs,h0] at h1
      contradiction
    · simp [Fin.val_ne_of_ne h0]
  by_cases hp:p=⟨↑r + ↑i + 1,rval_ival_lt i r⟩
  · have hrs' : Fin.mk (↑r + ↑i + 1) (rval_ival_lt i r) ≠ ⟨↑s + ↑i + 1,rval_ival_lt i s⟩ := by simp [hrs]
    simp_rw [hp,elemMat,ElemOpOnMatrix,Matrix.updateRow_self,Matrix.updateRow_ne hrs']
    apply Finset.sum_congr rfl
    intro x hxin
    --by_cases hx:x= r or s



    -- have h1 : i.1 ≠ r+i+1 := by simp_rw [add_comm,add_assoc]; exact Nat.ne_of_lt (Nat.lt_add_of_pos_right (Nat.zero_lt_succ ↑r))
    -- have hri : i ≠ ⟨↑r + ↑i + 1,rval_ival_lt i r⟩ := Fin.ne_of_val_ne h1
    -- have h2 : i.1 ≠ s+i+1 := by simp_rw [add_comm,add_assoc]; exact Nat.ne_of_lt (Nat.lt_add_of_pos_right (Nat.zero_lt_succ ↑s))
    -- have hsi : i ≠ ⟨↑s + ↑i + 1,rval_ival_lt i s⟩ := Fin.ne_of_val_ne h2
    -- simp [Matrix.updateRow_ne hri, Matrix.updateRow_ne hsi]
    -- apply Finset.sum_congr rfl
    -- intro x hx'
    -- by_cases hx:x=i
    -- · simp [hx,hsi,hri]
    -- · simp
    --   right
    --   exact Matrix.one_apply_ne (Ne.symm hx)



  --simp_rw [elemMat,ElemOpOnMatrix_mul,Matrix.one_mul]









lemma elimEltBelow (hpiv : M i j = 1) (r : Fin (m-i-1)) :
  (ElemOpOnMatrix (rowMulAdd (-M ⟨r+i+1,rval_ival_lt i r⟩ j) ⟨r+i+1,rval_ival_lt i r⟩ i) M) ⟨r+i+1,rval_ival_lt i r⟩ j = 0 := by
  rw [ElemOpOnMatrix]; simp [hpiv]

theorem elimColBelow_length : (elimColBelow_ij M i j).length = m-i-1 := by
  rw [elimColBelow_ij]; simp

lemma elimColBelow_get_eq_rowMulAdd (i : Fin m) (j : Fin n) (r : Fin (m-i-1)) :
  (elimColBelow_ij M i j).get (r.cast (Eq.symm (elimColBelow_length M))) = rowMulAdd (-M ⟨↑r+↑i+1,rval_ival_lt i r⟩ j) ⟨↑r+↑i+1,rval_ival_lt i r⟩ i := by
  unfold elimColBelow_ij
  simp

lemma elimColbelow_get_elim_r (i : Fin m) (j : Fin n) (r : Fin (m-i-1)) (hpiv : M i j = 1) :
  (ElemOpOnMatrix ((elimColBelow_ij M i j).get (r.cast (Eq.symm (elimColBelow_length M)))) M) ⟨r+i+1,rval_ival_lt i r⟩ j = 0 := by
  rw [elimColBelow_get_eq_rowMulAdd,elimEltBelow _ hpiv]

lemma rowMulAdd_otherRows (i j : Fin m) (k : Fin m) (hk : k ≠ i) (c : Rat) :
  (ElemOpOnMatrix (rowMulAdd c i j) M) k = M k := by
  rw [ElemOpOnMatrix]; simp; exact Matrix.updateRow_ne hk

lemma elimColBelow_get_elim_notr (i : Fin m) (j : Fin n) (r : Fin (m-i-1)) (s : Fin (m-i-1)) (hsr : s≠r) :
  (ElemOpOnMatrix ((elimColBelow_ij M i j).get (r.cast (Eq.symm (elimColBelow_length M)))) M) ⟨s+i+1,rval_ival_lt i s⟩ j = M ⟨s+i+1,rval_ival_lt i s⟩ j := by
  rw [elimColBelow_get_eq_rowMulAdd,rowMulAdd_otherRows]
  simp [Fin.val_ne_of_ne hsr]

#check Fin.eq_iff_veq

lemma elimColBelow_elt_commute (e e' : ElemOp) (he : e ∈ elimColBelow_ij M i j) (he' : e' ∈ elimColBelow_ij M i j) (hee' : e ≠ e') :
  listElemOpOnMatrix [e,e'] M = listElemOpOnMatrix [e',e] M := by
    obtain ⟨r,hr⟩ := elt_elimColBelow_eq_rowMulAdd M he
    obtain ⟨s,hs⟩ := elt_elimColBelow_eq_rowMulAdd M he'
    rw [← hr,← hs] at hee' ⊢
    simp only [ne_eq, rowMulAdd.injEq, neg_inj, Fin.mk.injEq,add_left_inj, and_true, not_and'] at hee'
    unfold listElemOpOnMatrix listElemOpOnMatrix listElemOpOnMatrix --ElemOpOnMatrix
    by_cases hrs:r=s
    · have := hee' (congrArg Fin.val hrs)
      rw [hrs] at this
      contradiction
    · have hrsi : r.1+↑i+1≠↑s+↑i+1 := by simp [Fin.val_ne_of_ne hrs]
      set cr := M ⟨↑r + ↑i + 1, ⋯⟩ j
      set cs := M ⟨↑s + ↑i + 1, ⋯⟩ j
      set M' := ((rowMulAdd (-cs) ⟨↑s + ↑i + 1, ⋯⟩ i).ElemOpOnMatrix M)
      simp



      -- have h1 := rowMulAdd_otherRows ((rowMulAdd (-cs) ⟨↑s + ↑i + 1,rval_ival_lt i s⟩ i).ElemOpOnMatrix M) ⟨↑r + ↑i + 1,rval_ival_lt i r⟩ i ⟨↑s + ↑i + 1,rval_ival_lt i s⟩ (Fin.ne_of_val_ne (id (Ne.symm hrsi))) (-cr)
      -- have h2 := rowMulAdd_otherRows M ⟨↑s + ↑i + 1,rval_ival_lt i s⟩ i ⟨↑r + ↑i + 1,rval_ival_lt i r⟩ (Fin.ne_of_val_ne (id hrsi)) cr




lemma listElemOpOnMatrix_cons (E : ElemOp) (l : List ElemOp) :
  ElemOpOnMatrix E (listElemOpOnMatrix l M) = (listElemOpOnMatrix (E::l) M) := by
  induction' l <;> simp [listElemOpOnMatrix]

#check List.splitOn

-- lemma listElemOpOnMatrix_elt (E : ElemOp) (l : List ElemOp) (hE : E ∈ l) :
--   listElemOpOnMatrix l M =

#check DecidableEq
#check Nat

-- def listElemOp_erase (l : List ElemOp) (E : ElemOp)

example (Er : ElemOp) (hEr : Er ∈ elimColBelow_ij M i j) :
  listElemOpOnMatrix (elimColBelow_ij M i j) M = listElemOpOnMatrix ((elimColBelow_ij M i j).erase Er) (ElemOpOnMatrix Er M) := by
  unfold listElemOpOnMatrix elimColBelow_ij
  simp

-- #check List.map

example (i : Fin m) (j : Fin n) (r : Fin (m-i-1)) (hpiv : M i j = 1) :
  (listElemOpOnMatrix (elimColBelow_ij M i j) M) ⟨r+i+1,rval_ival_lt i r⟩ j = 0 := by
  unfold listElemOpOnMatrix elimColBelow_ij











-- def listElemOpOnMatrix'_aux (l : List (ElemOp (m:=m))) (A : Matrix (Fin m) (Fin n) Rat) (r : Fin l.length) :=
  -- match r with
  -- | ⟨0,h0⟩ => ElemOpOnMatrix (l.get ⟨0,h0⟩) A
  -- -- | ⟨i+1,hi⟩ => ElemOpOnMatrix (l.get ⟨i+1,hi⟩) (listElemOpOnMatrix'_aux l A ⟨i,Nat.lt_of_succ_lt hi⟩)
  -- | ⟨i+1,hi⟩ => listElemOpOnMatrix'_aux l (ElemOpOnMatrix (l.get ⟨i+1,hi⟩) A) ⟨i,Nat.lt_of_succ_lt hi⟩
  -- ElemOpOnMatrix (l.get r) (listElemOpOnMatrix'_aux l A (r+1))
  -- have : l.length-r > 0 := Nat.zero_lt_sub_of_lt (r.isLt)

-- def listElemOpOnMatrix' (l : List (ElemOp (m:=m))) (A : Matrix (Fin m) (Fin n) Rat) : Matrix (Fin m) (Fin n) Rat :=
--   match h:l with
--   | [] => A
--   | E::as => listElemOpOnMatrix'_aux l A ⟨l.length.pred,by rw [h]; exact Nat.lt.base (E :: as).length.pred⟩
    -- where listElemOpOnMatrix'_aux (l : List (ElemOp (m:=m))) (A : Matrix (Fin m) (Fin n) Rat) (r : Fin l.length) := match r with
    --   | ⟨0,h0⟩ => ElemOpOnMatrix (l.get ⟨0,h0⟩) A
    --   | ⟨i+1,hi⟩ => ElemOpOnMatrix (l.get ⟨i+1,hi⟩) (listElemOpOnMatrix'_aux l A ⟨i,Nat.lt_of_succ_lt hi⟩)

-- def listElemOpOnMatrix' (l : List (ElemOp (m:=m))) (A : Matrix (Fin m) (Fin n) Rat) : Matrix (Fin m) (Fin n) Rat :=
--   match l with
--   | [] => A
--   | E::as =>

/-
def matt := !![1,0,0;1,(0:Rat),0;1,0,0]
#eval elimColBelow_ij matt 0 0
#eval listElemOpOnMatrix' (elimColBelow_ij matt 0 0) matt
#eval listElemOpOnMatrix' [] matt

lemma listElemOpOnMatrix'_aux_cons (E : ElemOp) (a : ElemOp) (l : List (ElemOp)) :
  E.ElemOpOnMatrix (listElemOpOnMatrix'_aux (a::l) M ⟨l.length,by simp⟩) = listElemOpOnMatrix'_aux (E :: a :: l) M ⟨(a::l).length,by simp⟩ := by
  unfold listElemOpOnMatrix'_aux
  simp

lemma listElemOpOnMatrix'_cons (E : ElemOp) (l : List (ElemOp)) :
  E.ElemOpOnMatrix (listElemOpOnMatrix' l M) = listElemOpOnMatrix' (E :: l) M := by
  nth_rw 2 [listElemOpOnMatrix']
  unfold listElemOpOnMatrix'_aux
  simp
  rw [listElemOpOnMatrix']
  induction' l with a as ih
  · rfl
  · simp


theorem listElemOpOnMatrix_eq (l : List (ElemOp)) :
  listElemOpOnMatrix l M = listElemOpOnMatrix' l M := by
  induction' l with E as hi
  · rfl
  -- · unfold listElemOpOnMatrix listElemOpOnMatrix' listElemOpOnMatrix'.listElemOpOnMatrix'_aux
  · rw [listElemOpOnMatrix,hi,listElemOpOnMatrix'_cons]




--example : listElemOpOnMatrix (elimColBelow_ij i j) is equal to something with get
-/

-- lemma elimColBelow_cycle (hl : elimColBelow_ij M i j = elt::l) :
--   elt.ElemOpOnMatrix (listElemOpOnMatrix l M) = listElemOpOnMatrix l (elt.ElemOpOnMatrix M) := by
--   unfold listElemOpOnMatrix
--   have h1 : elt ∈ elimColBelow_ij M i j := by simp [hl]
--   obtain ⟨s,helt⟩ := elt_elimColBelow_eq_rowMulAdd M h1
--   rw [← helt, ElemOpOnMatrix]; simp
--   induction' l with a as ih
--   · simp [ElemOpOnMatrix]
--   · simp

example (a : Fin 0) : False := Fin.elim0 a

example (i : Fin m) : i ≤ m-1 := Nat.le_sub_one_of_lt (i.2)

example (i : Fin m) (j : Fin n) (r : Fin (m-i-1)) (hpiv : M i j = 1) :
  (listElemOpOnMatrix (elimColBelow_ij M i j) M) ⟨r+i+1,rval_ival_lt i r⟩ j = 0 := by
  -- have h1 : (ElemOpOnMatrix ((elimColBelow_ij M i j).get (r.cast (Eq.symm (elimColBelow_length M)))) M) ⟨r+i+1,rval_ival_lt i r⟩ j = 0 :=
  --   elimColbelow_get_elim_r  _ _ _ _ hpiv
  -- have h2 : ∀ s≠r, (ElemOpOnMatrix ((elimColBelow_ij M i j).get (r.cast (Eq.symm (elimColBelow_length M)))) M) ⟨s+i+1,rval_ival_lt i s⟩ j = M ⟨s+i+1,rval_ival_lt i s⟩ j :=
  --   elimColBelow_get_elim_notr _ _ _ _
  unfold listElemOpOnMatrix elimColBelow_ij
  rcases lt_or_eq_of_le (Nat.le_sub_one_of_lt (i.2)) with hi|heq
  ·
  · apply Fin.elim0 (r.cast (by rw [heq]; exact Eq.symm (Nat.eq_sub_of_add_eq' (Eq.symm (Nat.sub_sub_self hm)))))
  -- induction' r using Fin.inductionOn


  -- induction' hl : elimColBelow_ij M i j with elt l hi
  -- · rw [elimColBelow_ij] at hl; simp at hl
  --   have h1 := rval_ival_lt i r
  --   rw [Nat.sub_sub,Nat.sub_eq_iff_eq_add] at hl
  --   simp_rw [hl] at h1
  --   simp at h1
  --   exact Nat.add_le_of_le_sub hm (Nat.le_sub_one_of_lt i.2)
  -- · unfold listElemOpOnMatrix
    -- have : elt.ElemOpOnMatrix (listElemOpOnMatrix l M)
    --       = listElemOpOnMatrix l (elt.ElemOpOnMatrix M) := by
    --   unfold listElemOpOnMatrix


    -- have h1 : elt ∈ elimColBelow_ij M i j := by simp [hl]
    -- obtain ⟨s,helt⟩ := elt_elimColBelow_eq_rowMulAdd M h1
    -- rw [← helt, ElemOpOnMatrix]; simp






  -- unfold elimColBelow_ij
  -- induction' hl : (List.ofFn fun r ↦ rowMulAdd (-M ⟨↑r + ↑i + 1,_⟩ j) ⟨↑r + ↑i + 1,_⟩ i) with elt l hi
  -- · have h1 := rval_ival_lt i r
  --   simp at hl
  --   rw [Nat.sub_sub,Nat.sub_eq_iff_eq_add (Nat.add_le_of_le_sub hm (Nat.le_sub_one_of_lt i.2))] at hl
  --   simp_rw [hl] at h1
  --   simp at h1
  -- ·






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
