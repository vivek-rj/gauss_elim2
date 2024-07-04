import Mathlib.Data.Matrix.Notation
import Mathlib.Data.List.Indexes

variable (F : Type) [Field F] [DecidableEq F] [Repr F]

theorem Vector.eq_iff (a1 a2 : Vector α n) : a1 = a2 ↔ toList a1 = toList a2 := by
  constructor
  intro h; rw [h]
  intro h; exact Vector.eq _ _ h

def Vector.Mem (a : α) : Vector α n → Prop := fun v => v.toList.Mem a

instance : Membership α (Vector α n) where
  mem := Vector.Mem

theorem Vector.mem_def (v : Vector α n) : a ∈ v ↔ a ∈ v.toList := Iff.rfl

theorem Vector.mem_cons {a b : α} {l : Vector α n} : a ∈ (Vector.cons b l) ↔ a = b ∨ a ∈ l := by
  constructor
  intro h
  simp [Vector.mem_def] at h
  rcases h with h|h; left; assumption; right; simp [Vector.mem_def,h]
  intro h; rcases h with h|h ; simp [Vector.mem_def,h]; rw [Vector.mem_def] at h ⊢; simp [h]

instance [DecidableEq α] (a : α) (v : Vector α n) : Decidable (a ∈ v) :=
  inferInstanceAs <| Decidable (a ∈ v.toList)

abbrev Vector.allZero (v : Vector F n) : Prop := v.toList.all (.=0)

theorem Vector.allZero_def (v : Vector F n) : v.allZero = v.toList.all (.=0) := rfl

lemma Vector.replicate_zero (a : α) : Vector.replicate 0 a = Vector.nil := rfl

theorem Vector.mem_replicate {a b : α} : ∀ {n}, b ∈ Vector.replicate n a ↔ n ≠ 0 ∧ b = a
  | 0 => by simp [Vector.replicate_zero,Vector.mem_def]
  | n+1 => by simp [Vector.mem_cons,Vector.mem_replicate]

lemma Vector.mem_replicate' : ∀ x ∈ (Vector.replicate n c).toList, x = c := by
  intro x hx
  rw [← Vector.mem_def,Vector.mem_replicate] at hx
  exact hx.2

lemma Vector.replicate_toList : (Vector.replicate n c).toList = List.replicate n c := by rfl

theorem Vector.allZero_eq_replicate0 (v : Vector F n) : v.allZero ↔ v = Vector.replicate n 0 := by
  constructor
  · intro hv
    rw [allZero] at hv
    simp at hv
    rw [Vector.eq_iff,replicate_toList]
    refine List.eq_replicate.mpr ⟨v.toList_length,hv⟩
  · intro hv
    rw [hv,allZero]
    simp
    exact mem_replicate'

theorem Vector.cons_eq_cons {a b : α} {v v' : Vector α n} : v.cons a = v'.cons b ↔ a = b ∧ v = v' := by
  obtain ⟨l,_⟩ := v
  obtain ⟨l',_⟩ := v'
  simp [Vector.cons,Vector.eq_iff]

instance (v : Vector F n)  : Decidable (v.allZero) := inferInstance

structure ReducedRow0 (n : Nat)

structure ReducedRowN0 (n : Nat) where
  z : Fin n
  k : Nat
  tail : Vector F k
  h : n = p + k + 1

def ReducedRow (n : Nat) := Sum (ReducedRow0 n) (ReducedRowN0 F n)

def zeroVec (k: Nat) : Vector F k := Vector.replicate k 0

def ReducedRow0.toVector {F : Type} [Field F] (_ : ReducedRow0 n): Vector F n := zeroVec F n

def ReducedRowN0.toVector {F : Type} [Field F] (row : ReducedRowN0 F n): Vector F n := row.h ▸ (zeroVec F n).append (Vector.cons 1 row.tail)

def ReducedRow.toVector (row : ReducedRow F n): Vector F n :=
  match row with
  | .inl row0 => row0.toVector
  | .inr rowN0 => rowN0.toVector

def Vector.isReducedRow (v : Vector F n) : Prop := ∃ r : ReducedRow F n, v = r.toVector

/--
Gives the index of the first nonzero element in a vector, along with a proof
of that element being nonzero
-/
def Vector.indNonzElt {F : Type} [Field F] [DecidableEq F] (v : Vector F k) : Option {idx : Fin k // v.get idx ≠ 0} :=
  v.inductionOn none
  fun _ {x} _ a => if h : x ≠ 0 then some ⟨0, h⟩ else a.map fun idx => ⟨idx.1.succ, idx.2⟩

--separate zero row and nz row

-- def List.indNonzElt {F : Type} [Field F] [DecidableEq F] (l : List F) (hl : l.length = k) : Option {idx : Fin k // l.get (idx.cast (Eq.symm hl)) ≠ 0} :=
--   l.rec none
--   fun {x} _ a => if h : x ≠ 0 then some ⟨⟨0,_⟩, h⟩ else a.map fun idx => ⟨idx.1.succ, idx.2⟩

#check Vector.toList_cons

-- theorem Vector.toList_get (i : Fin n) (v : Vector α n) : v.get i = v.toList.get (i.cast (Eq.symm v.toList_length)) := rfl

-- theorem Vector.indNonzElt_toList {F : Type} [Field F] [DecidableEq F] (v : Vector F k) : v.indNonzElt = v.toList.indNonzElt :=

theorem Vector.indNonzElt_nil : Vector.nil.indNonzElt (F:=F) = none := rfl

theorem Vector.indNonzElt_cons_0_none {F : Type} [Field F] [DecidableEq F] (v : Vector F k) (hv : v.indNonzElt = none) :
  (Vector.cons 0 v).indNonzElt = none := by
  induction' v using Vector.inductionOn
  · simp [Vector.indNonzElt]
  · rw [Vector.indNonzElt,Vector.inductionOn_cons,← Vector.indNonzElt]
    simp [hv]

theorem Vector.indNonzElt_cons_non0 (v : Vector F k) (x : F) (hx : x≠0) :
  (Vector.cons x v).indNonzElt = some ⟨0,by simp [hx]⟩ := by
  rw [Vector.indNonzElt,Vector.inductionOn_cons,← Vector.indNonzElt]
  simp [hx]

theorem Vector.indNonzElt_cons_0_some (v : Vector F k) (idx : Fin k) (hidx : v.get idx ≠ 0) (hv : v.indNonzElt = some ⟨idx,hidx⟩) :
  (Vector.cons 0 v).indNonzElt = some ⟨idx.succ,by simp [hidx]⟩ := by
  rw [Vector.indNonzElt,Vector.inductionOn_cons,← Vector.indNonzElt]
  simp [hv]

lemma Vector.indNonzElt_some_consSome {F : Type} [Field F] [DecidableEq F] {v : Vector F k} {x : F} (h : (v.indNonzElt).isSome = true) :
((Vector.cons x v).indNonzElt).isSome = true := by
  induction' v using Vector.inductionOn
  · rw [indNonzElt_nil] at h; simp at h
  · rw [indNonzElt,Vector.inductionOn_cons,← indNonzElt]
    simp
    by_cases hx:x=0
    · simp [hx,h]
    · simp [hx]

lemma Vector.indNonzElt_some_ex (v : Vector F k) (h : ∃ x ∈ v.toList, x≠0) : (v.indNonzElt).isSome = true := by
  induction' v using Vector.inductionOn with k' x w hi
  · simp at h
  · simp at h
    rcases h with h|h
    · rw [indNonzElt,Vector.inductionOn_cons,← indNonzElt]
      simp [h]
    · exact indNonzElt_some_consSome (hi h)

lemma Vector.indNonzElt_allZero (v : Vector F k) (h : v.allZero) : v.indNonzElt = none := by
  rw [Vector.allZero_eq_replicate0] at h
  induction' v using Vector.inductionOn with p a w ih
  · rfl
  · simp [Vector.cons_eq_cons] at h
    rw [h.1]
    rw [indNonzElt_cons_0_none]
    exact ih h.2

lemma Vector.indNonzElt_zeroVec : indNonzElt (zeroVec F n) = none := by
  set v := zeroVec F n with hv
  dsimp [zeroVec] at hv
  rw [← allZero_eq_replicate0] at hv
  exact indNonzElt_allZero F v hv

def Vector.concat (a : α) : Vector α n → Vector α (n+1) := fun v => Vector.append v ⟨[a],rfl⟩

#check Vector.toList_cons

lemma List.replicate_concat_get {p : Nat} {a b : α} : (List.replicate p a ++ [b]).get ⟨p,by simp⟩ = b := by
  have h1 := List.get_append_right (i:=p) (as:=List.replicate p a) (bs:=[b]) (by rw [List.length_replicate]; exact Nat.lt_irrefl p) (h':=by rw [List.length_append,List.length_replicate]; exact lt_add_one p) (h'':=by rw [List.length_replicate];simp)
  simp [h1]

  -- lemma Vector.indNonzElt_append (v w : Vector F n) (hv : V.indNonzElt = none) : (v.append w).indNonzElt =

lemma Vector.cons_eq_listCons (a : α) (l : List α) : (⟨a::l,by simp⟩ : Vector α l.length.succ) = Vector.cons a ⟨l,rfl⟩ := rfl

lemma Vector.indNonzElt_zeroVecAppend {p : Nat} {w : Vector F n} (hw : w.indNonzElt = none) :
  ((zeroVec F p).append w).indNonzElt = none := by
  obtain ⟨l,hl⟩ := w
  induction p with
  | zero => simp [zeroVec,replicate,append]; convert hw <;> exact Nat.zero_add n
  | succ q ih =>
    simp [zeroVec,replicate,append]
    -- have : (0 ::ᵥ (⟨List.replicate q 0 ++ l,rfl⟩ : Vector F (q+n))).length = q+1+n := by simp [hl]; ring
    have : (⟨0 :: (List.replicate q 0 ++ l), by simp [hl]; ring⟩ : Vector F (q+1+n)) = (0 ::ᵥ ⟨List.replicate q 0 ++ l, rfl⟩).congr (by simp [hl]; ring) := rfl
    rw [this]
    sorry


#check Nat.odd_iff
#check List.splitAt

def Vector.splitAt (i : Fin n) (v : Vector α n) : Vector α i × Vector α (n-i) :=
  ⟨⟨(v.toList.splitAt i).1,by simp⟩,⟨(v.toList.splitAt i).2,by simp⟩⟩

-- fn that returns splitting of vector into 0s, nonz elt and tail
--update to 4.9.0

theorem Vector.isreducedRow_iff (v : Vector F n) :
  v.isReducedRow ↔ match v.indNonzElt with | none => true | some idx => (v.get idx = 1) ∧ (v.splitAt idx).1.allZero := by
  constructor
  · intro h
    dsimp [isReducedRow] at h
    rcases h with ⟨r,hr⟩
    rw [hr]
    simp [ReducedRow.toVector]
    match hr1:r with
    | .inl row0 =>
      simp [hr1,ReducedRow0.toVector,Vector.indNonzElt_zeroVec]
    | .inr rown0 =>
      simp [ReducedRowN0.toVector,zeroVec,Vector.replicate,Vector.append,Vector.cons]
      set tv := rown0.tail with htv
      rcases ht:tv with ⟨tl,htl⟩
      simp
      sorry
  · sorry


-- section
-- variable (l : List Nat) (x : Nat)
-- #synth Decidable (∃ y : Nat, y=x)
-- end

def ReducedRowN0.zerosSelf (row : ReducedRowN0 F n) (R : Vector (ReducedRowN0 F n) m) : Prop :=
  ∀ r ∈ R, row.toVector.get r.z = 0

def ReducedRowN0.zerosAbove (row : ReducedRowN0 F n) (R : Vector (ReducedRowN0 F n) m) : Prop :=
  (R.map fun r => r.toVector.get row.z).allZero

def ReducedRowN0.leadingZerosLT (row : ReducedRowN0 F n) (R : Vector (ReducedRowN0 F n) m) :=
  match R.toList.head? with | none => true | some r => row.z < r.z

section
variable (row : ReducedRowN0 F n) (R : Vector (ReducedRowN0 F n) m)

instance : Decidable (row.zerosSelf F R) :=
  inferInstanceAs <| Decidable ((∀ r ∈ R.toList, row.toVector.get r.z = 0))

instance : Decidable (row.zerosAbove F R) :=
  inferInstanceAs <| Decidable ((R.map fun r => r.toVector.get row.z).toList.all (.=0) = true)

#synth Decidable ((row.zerosSelf F R) ∧ (row.zerosAbove F R))

end

inductive RowReducedEchelonFormN0 : (R : Vector (ReducedRowN0 F n) m) → Prop where
| nil : RowReducedEchelonFormN0 Vector.nil
| cons : (row : ReducedRowN0 F n) → RowReducedEchelonFormN0 R →
          row.zerosSelf F R →
          row.zerosAbove F R →
          row.leadingZerosLT F R →
          RowReducedEchelonFormN0 (R.cons row)

inductive RowReducedEchelonForm0 (z : Nat)

structure RowReducedEchelonForm (R : Vector (ReducedRowN0 F n) m) (z : Nat) where
nonZeroRows : RowReducedEchelonFormN0 F R
zeroRows : RowReducedEchelonForm0 z

def isRowReducedEchelonForm (R : Vector (ReducedRow F n) m) := ∃ z : Fin m, ((R.splitAt z).1.toList.all (fun r => r.isLeft)) ∧ ((R.splitAt z).2.toList.all (fun r => r.isRight))

def RowReducedEchelonForm.toMatrix (R : Vector (ReducedRowN0 F n) m) (z : Nat) : Matrix (Fin (m+z)) (Fin n) F :=
  (((R.map fun r => r.toVector).append (Vector.replicate z (zeroVec F n))).map (fun v => v.get)).get

lemma myLemma1 (l : Vector (ReducedRowN0 F n) m) (l' : Vector (ReducedRowN0 F n) (m+1)) (hl' : l' = l.cons row) (h : RowReducedEchelonFormN0 F l') :
  (RowReducedEchelonFormN0 F l) ∧ (row.zerosSelf F l) ∧ (row.zerosAbove F l) ∧ (row.leadingZerosLT F l) := by
  match h with
  | .cons row H0 H1 H2 H3 => have ⟨h1,h2⟩ := Vector.cons_eq_cons.mp hl'; subst h1 h2; exact ⟨H0,H1,H2,H3⟩

lemma myLemma2 {l : Vector (ReducedRowN0 F n) m} (hl : RowReducedEchelonFormN0 F (l.cons row)) :
  (RowReducedEchelonFormN0 F l) ∧ (row.zerosSelf F l) ∧ (row.zerosAbove F l) ∧ (row.leadingZerosLT F l) :=
  myLemma1 F l (l.cons row) rfl hl

instance : Decidable (RowReducedEchelonFormN0 F R) :=
  R.inductionOn
  (.isTrue (RowReducedEchelonFormN0.nil))
  (fun _ {row} {l} ih => match ih with
    | isTrue hl =>
      if hr : (row.zerosSelf F l) ∧ (row.zerosAbove F l) ∧ (row.leadingZerosLT F l)
      then .isTrue (RowReducedEchelonFormN0.cons row hl hr.1 hr.2.1 hr.2.2)
      else .isFalse (by
        intro h
        rw [Decidable.not_and_iff_or_not_not,Decidable.not_and_iff_or_not_not] at hr
        have h0 := myLemma2 F h
        rcases hr with h1|h2|h3
        · exact absurd h0.2.1 h1
        · exact absurd h0.2.2.1 h2
        · exact absurd h0.2.2.2 h3)
    | isFalse hl => .isFalse (by intro h; exact absurd (myLemma2 F h).1 hl))
