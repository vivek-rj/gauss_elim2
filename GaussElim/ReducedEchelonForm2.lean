import Mathlib.Data.Matrix.Notation

/--
Two vectors are equal iff their corresponding lists are equal
-/
theorem Vector.eq_iff (a1 a2 : Vector α n) : a1 = a2 ↔ toList a1 = toList a2 := by
  constructor
  intro h; rw [h]
  intro h; exact Vector.eq _ _ h

variable {F : Type} [Field F] [DecidableEq F]

-- structure ReducedRow0 (n : Nat)

/--
The type of Vectors that would be rows in a row-reduced matrix with `n` columns in the field `F`.
It is of the form `[0,0,...,0,1,(arbitrary entries)]`

If `row : ReducedRowN0 F n`:
* `row.z` gives the leading zeros, or `none` if the row is all zeros
* `row.k` gives the length of the arbitrary part
* `row.tail` gives the arbitrary part
* `row.h` is a proof that if the row isn't all zeros, then
  `row.z` + `row.k` + 1 = n
-/
structure ReducedRowN0 (F : Type) [Field F] [DecidableEq F] (n : Nat) where
  z : Fin n
  k : Nat
  tail : Vector F k
  h : n = z + k + 1

-- def ReducedRow (F : Type) [Field F] [DecidableEq F] (n : Nat) := Sum (ReducedRow0 n) (ReducedRowN0 F n)

def zeroVec (k: Nat) : Vector F k := Vector.replicate k 0

-- def ReducedRow0.toVector (_ : ReducedRow0 n): Vector F n := zeroVec n

/--
Form a Vector from the data stored in the `ReducedRow` type
-/
def ReducedRowN0.toVector (row : ReducedRowN0 F n): Vector F n := ((zeroVec row.z).append (Vector.cons 1 row.tail)).congr (Eq.symm row.h)

-- def ReducedRow.toVector (row : ReducedRow F n): Vector F n :=
--   match row with
--   | .inl row0 => row0.toVector
--   | .inr rowN0 => rowN0.toVector

def Vector.isReducedRowN0 (v : Vector F n) : Prop := ∃ r : ReducedRowN0 F n, v = r.toVector

def Vector.any (v : Vector F n) (p : F → Bool) := v.toList.any p

@[simp] theorem Vector.any_def (v : Vector F n) (p : F → Bool) : v.any p = v.toList.any p := rfl

/--
Given a vector that has a nonzero element, this function returns these values as a tuple :
* The first nonzero element in the vector, with a proof of it being nonzero
* The index at which it is present
* The elements of the vector to the right of this element.
-/
def Vector.firstNonzElt (v : Vector F n) (h: v.any (· ≠ 0)) : {x:F // x≠0}×(i : Fin n)×(Vector F (n-i-1)) :=
  match v with
  | ⟨[],hv⟩ => by simp at h
  | ⟨x::ys,ha⟩ =>
    have hn : n > 0 := by rw [← ha]; simp
    if hx:x ≠ 0
    then (⟨x, hx⟩, ⟨⟨0,hn⟩,⟨ys,by simp_rw [← ha];simp⟩⟩)
    else
      by
      have ys_nontriv: ys.any (· ≠ 0) := by
        simp at hx
        simp [List.any_cons, hx] at h
        simp [h]
      let (value, ⟨index, tail⟩) := firstNonzElt (⟨ys,by simp at ha; rw [← ha]; simp⟩ : Vector F (n-1)) ys_nontriv
      exact (value, ⟨index.succ.cast (by simp [Nat.sub_add_cancel hn]),tail.congr (by simp [Nat.Simproc.sub_add_eq_comm n (↑index) 1])⟩)

-- theorem Vector.firstNonzElt_cons_non0 {v : Vector F n} {x : F} (hx : x ≠0) :
--   (Vector.cons x v).firstNonzElt (by simp [hx]) = (⟨x,hx⟩,⟨⟨0,by simp⟩,v⟩) := by sorry
--   -- induction' v using Vector.inductionOn with _ x w hw
--   -- ·
--   -- · sorry

def v : Vector Rat 5 := ⟨[0,0,4,2,3],rfl⟩
#eval v.firstNonzElt (by decide)

lemma Vector.eq_firstNonzEltAppend (v : Vector F n) (h: v.any (· ≠ 0)) :
  let (⟨x,hx⟩,⟨i,t⟩) := v.firstNonzElt h; v = ((Vector.replicate i 0).append (t.cons x)).congr (sorry) := by
    induction' v using Vector.inductionOn with _ x w hw
    · simp at h
    · sorry
      -- rw [firstNonzElt]
      -- split_ifs
      -- · sorry
      -- · sorry

theorem Vector.congr_toListEq {n m : ℕ} (h : n = m) (v : Vector α n) :
  v.toList = (v.congr h).toList := rfl

lemma Vector.cons_eq_listCons (a : α) (l : List α) : ⟨a::l,by simp⟩ = Vector.cons a ⟨l,rfl⟩ := rfl

theorem Vector.append_def {n m : Nat} (v : Vector α n) (w : Vector α m) :
  v.append w = ⟨v.toList++w.toList,by simp⟩ := rfl

#check HEq.subst

/--
Appending an all zero vector of length `p` to the left of a vector increases the index of its
first nonzero element by `p`
-/
lemma Vector.firstNonzElt_zeroVecAppend {p : Nat} {w : Vector F n} (hw : w.any (.≠0)) :
  (((zeroVec p).append w).firstNonzElt (by simp at hw ⊢; rcases hw with ⟨x,hx⟩; use x; exact ⟨Or.inr hx.1,hx.2⟩)).2.1 = p+(w.firstNonzElt hw).2.1 := by
  induction p with
  | zero =>
    simp [zeroVec,replicate,append_def]
    have := w.mk_toList (w.toList_length)
    congr 4 <;> try simp
    · rw [Fin.heq_fun_iff]; simp; simp
    · rw [Fin.heq_fun_iff]; simp; simp
    · convert heq_of_eq this
      · rw [Nat.zero_add]; rfl
      · rw [Nat.zero_add]
  | succ q ih =>
    simp [zeroVec,replicate,append_def] at ih ⊢
    -- have := (cons_eq_listCons 0 (List.replicate q 0 ++ w.toList))
    -- have : (⟨0 :: (List.replicate (List.replicate q 0).length 0 ++ w.toList), sorry⟩ : Vector F (q+w.toList.length+1)) =
    -- 0 ::ᵥ ⟨List.replicate (List.replicate q 0).length 0 ++ w.toList, sorry⟩ := List.length_replicate q 0
    sorry

/-
A vector is in reduced row form iff its first nonzero element is 1
--/
theorem Vector.isreducedRowN0_iff_firstNonzElt1 (v : Vector F n) (h: v.any (· ≠ 0)) :
  (v.firstNonzElt h).1 = ⟨1,by norm_num⟩ ↔ v.isReducedRowN0 := by
  constructor
  · intro hv
    set x := (v.firstNonzElt h).1.1
    set hx := (v.firstNonzElt h).1.2
    set i := (v.firstNonzElt h).2.1.1 with hi
    set hi' := (v.firstNonzElt h).2.1.2
    set t := (v.firstNonzElt h).2.2.1 with ht
    set ht' := (v.firstNonzElt h).2.2.2
    let r : ReducedRowN0 F n := ⟨⟨i,hi'⟩,(n-i-1),⟨t,ht'⟩,by simp [add_assoc]; refine (Nat.sub_eq_iff_eq_add' (le_of_lt hi')).mp (by rw [← hi]; refine Eq.symm (Nat.sub_add_cancel (Nat.le_sub_of_add_le' hi')))⟩
    use r
    dsimp [ReducedRowN0.toVector,zeroVec]
    have h1 : (v.firstNonzElt h).1.1 = 1 := by simp [hv]
    have h2 : (replicate (↑(v.firstNonzElt h).2.fst) (0:F)) = replicate i 0 := by simp
    have h3 : (v.firstNonzElt h).2.snd = ⟨t,ht'⟩ := by simp [ht]
    rw [eq_firstNonzEltAppend v h,h1,h2,h3]
  · intro hv
    rcases hv with ⟨r,hv⟩
    rw [ReducedRowN0.toVector,zeroVec,replicate,append_def] at hv
    set rt := r.tail with hrt
    let ⟨t,ht⟩ := rt
    simp [cons] at hv
    sorry

def Vector.Mem (a : α) : Vector α n → Prop := fun v => v.toList.Mem a

instance : Membership α (Vector α n) where
  mem := Vector.Mem

theorem Vector.mem_def (v : Vector α n) : a ∈ v ↔ a ∈ v.toList := Iff.rfl

instance [DecidableEq α] (a : α) (v : Vector α n) : Decidable (a ∈ v) :=
  inferInstanceAs <| Decidable (a ∈ v.toList)

/--
Checks if the new reduced row has zeros wherever the other reduced rows have a leading one
-/
def ReducedRowN0.zerosSelf (row : ReducedRowN0 F n) (R : Vector (ReducedRowN0 F n) m) : Prop :=
  ∀ r ∈ R, row.toVector.get r.z = 0

/--
Checks if the number of leading zeros in the new reduced row is less than the number of zeros
in the first row of the list
-/
def ReducedRowN0.leadingZerosLT (row : ReducedRowN0 F n) (R : Vector (ReducedRowN0 F n) m) :=
  match R.toList.head? with | none => true | some r => row.z < r.z

section
variable (row : ReducedRowN0 F n) (R : Vector (ReducedRowN0 F n) m)
instance : Decidable (row.zerosSelf R) :=
  inferInstanceAs <| Decidable ((∀ r ∈ R.toList, row.toVector.get r.z = 0))
end

/--
A function that inductively checks if a list of reduced rows is in row-reduced echelon form
by checking for these conditions in every new row that gets added to the start of the list:
1. The new reduced row has zeros wherever the other reduced rows have a leading one
2. The number of leading zeros in the new reduced row is less than the number of zeros
in the first row of the list
-/
inductive RowReducedEchelonFormN0 : (R : Vector (ReducedRowN0 F n) m) → Prop where
| nil : RowReducedEchelonFormN0 Vector.nil
| cons : (row : ReducedRowN0 F n) → RowReducedEchelonFormN0 R →
          row.zerosSelf R →
          row.leadingZerosLT R →
          RowReducedEchelonFormN0 (R.cons row)

theorem Vector.cons_eq_cons {a b : α} {v v' : Vector α n} : v.cons a = v'.cons b ↔ a = b ∧ v = v' := by
  obtain ⟨l,_⟩ := v
  obtain ⟨l',_⟩ := v'
  simp [Vector.cons,Vector.eq_iff]

lemma myLemma1 (l : Vector (ReducedRowN0 F n) m) (l' : Vector (ReducedRowN0 F n) (m+1)) (hl' : l' = l.cons row) (h : RowReducedEchelonFormN0 l') :
  (RowReducedEchelonFormN0 l) ∧ (row.zerosSelf l) ∧ (row.leadingZerosLT l) := by
  cases h with
  | cons row H0 H1 H2 => have ⟨h1,h2⟩ := Vector.cons_eq_cons.mp hl'; subst h1 h2; exact ⟨H0,H1,H2⟩

lemma myLemma2 {l : Vector (ReducedRowN0 F n) m} (hl : RowReducedEchelonFormN0 (l.cons row)) :
  (RowReducedEchelonFormN0 l) ∧ (row.zerosSelf l) ∧ (row.leadingZerosLT l) :=
  myLemma1 l (l.cons row) rfl hl

instance : Decidable (RowReducedEchelonFormN0 (F:=F) R) :=
  R.inductionOn
  (.isTrue (RowReducedEchelonFormN0.nil))
  (fun _ {row} {l} ih => match ih with
    | isTrue hl =>
      if hr : (row.zerosSelf l) ∧ (row.leadingZerosLT l)
      then .isTrue (RowReducedEchelonFormN0.cons row hl hr.1 hr.2)
      else .isFalse (by
        intro h
        rw [Decidable.not_and_iff_or_not_not] at hr
        have h0 := myLemma2 h
        rcases hr with h1|h2
        · exact absurd h0.2.1 h1
        · exact absurd h0.2.2 h2)
    | isFalse hl => .isFalse (by intro h; exact absurd (myLemma2 h).1 hl))

abbrev Matrix.rowList (M : Matrix (Fin m) (Fin n) F) := (List.ofFn M).map Vector.ofFn

#check decPropToBool

-- def isRowReducedEchelonForm (M : Matrix (Fin m) (Fin n) F) :=
--   ∃ z : Fin m, (M.rowList.splitAt z).1.all (fun r => r.isReducedRowN0)
