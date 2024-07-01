import Mathlib.Data.Matrix.Notation
import Mathlib.Data.List.Indexes

variable (F : Type) [Field F] [DecidableEq F] [Repr F]

abbrev colVecofMat (M : Matrix (Fin m) (Fin n) F) := (Vector.ofFn M.transpose).map Vector.ofFn

abbrev Vector.allZero (v : Vector F n) : Prop := v.toList.all (.=0)

instance (v : Vector F n)  : Decidable (v.allZero) := inferInstance

/--
The type of Vectors that would be rows in a row-reduced matrix with `n` columns.
It is either filled with `0`s or of the form `[0,0,...,0,1,(arbitrary entries)]`

If `row : ReducedRow n`:
* `row.z` gives the leading zeros, or `none` if the row is all zeros
* `row.k` gives the length of the arbitrary part
* `row.tail` gives the arbitrary part
* `row.h` is a proof that if the row isn't all zeros, then
  `row.z` + `row.k` + 1 = n
-/
structure ReducedRow (n : Nat) where
  z : Option (Fin n)
  k : Nat
  tail : Vector F k
  h : (hz : z = some p) → n = p + k + 1

def zeroVec (k: Nat) : Vector F k := Vector.replicate k 0

/--
Form a Vector from the data stored in the `ReducedRow` type
-/
def ReducedRow.toVector (row : ReducedRow F n): Vector F n :=
  match hz:row.z with
  | none => zeroVec F n
  | some p => row.h hz ▸ (zeroVec F p).append (Vector.cons 1 row.tail)

#eval ReducedRow.toVector Rat (n:=5) ⟨some 2,2,⟨[3,4],rfl⟩,by simp⟩
#eval ReducedRow.toVector Rat (n:=4) ⟨none,_,⟨[],rfl⟩,by simp⟩

#check Membership

#synth Membership Nat (List Nat)

-- define 2 kinds of reducedrows - allzero and nonzero
-- define nonzero row rechelon llist as inductive type
-- stack nonzero list on sero rows (denoted by number : Nat) as a structure

#check Vector.append
#check List.not_mem_nil
#check List.mem_append
#check List.Mem
#synth Decidable (1 ∈ [1,2])

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
  -- ⟨fun h => by cases h <;> simp [Membership.mem, *],
  --  fun | Or.inl rfl => by constructor | Or.inr h => by constructor; assumption⟩

instance [DecidableEq α] (a : α) (v : Vector α n) : Decidable (a ∈ v) :=
  inferInstanceAs <| Decidable (a ∈ v.toList)

#synth Membership F (Vector F 1)

-- #check (⟨[1,2],rfl⟩ : Vector Nat 2)
-- #eval 1 ∈ (⟨[1,2],rfl⟩ : Vector Nat 2)
-- def v : Vector Nat 2 := (⟨[1,2],rfl⟩)
-- #eval 1 ∈ v

theorem Vector.not_mem_nil (a : α) : ¬ a ∈ Vector.nil := nofun

theorem Vector.eq_of_mem_singleton {a b : F} : (let v : Vector F 1 := ⟨[b],rfl⟩; a ∈ v) → a = b := by
  rw [Vector.mem_def]; simp [Vector.head]

def Vector.concat (a : α) : Vector α n → Vector α (n+1) := fun v => Vector.append v ⟨[a],rfl⟩

theorem Vector.concat_cons (a b : α) (v : Vector α n) : (Vector.cons a v).concat b = Vector.cons a (v.concat b) := by
  obtain ⟨l,hl⟩ := v
  simp [Vector.concat,Vector.append,Vector.cons]

#check List.concat_cons

theorem Vector.concat_eq_list_concat (v : Vector α n) (a : α) : v.concat a = ⟨v.toList.concat a,by simp⟩ := by
  induction' v with _ x v hi
  · simp [Vector.concat,Vector.append]
  · simp [Vector.concat_cons,hi]
    rfl

-- inductive RowEchelonForm : (R : Vector (ReducedRow F n) m) → Type where
-- | nil : RowEchelonForm Vector.nil
-- | cons : (row : ReducedRow F n) → RowEchelonForm R →
--          (∀ r ∈ R, (hz : r.z.isSome) → (row.toVector F).get (r.z.get hz) = 0) →
--          (match R.toList.getLast? with | none => true | some r => ¬(r.toVector = zeroVec F n) ∨ row.toVector = zeroVec F n) →
--          RowEchelonForm (R.concat row)

inductive RowEchelonForm : (R : Vector (ReducedRow F n) m) → Type where
| nil : RowEchelonForm Vector.nil
| cons : (row : ReducedRow F n) → RowEchelonForm R →
         (∀ r ∈ R, (hz : r.z.isSome) → (row.toVector F).get (r.z.get hz) = 0) →
         (match R.toList.head? with | none => true | some r => ¬(row.toVector = zeroVec F n) ∨ r.toVector = zeroVec F n) →
         RowEchelonForm (R.cons row)

-- keep relevat data from R as argument instead of using getLast?

--(match R with | [] => true | r::_ => ¬(r.toVector = zeroVec n) ∨ row.toVector = zeroVec n)

/-
A term of this type maps to an m×n matrix that satisies the following conditions:
1. Every row must be row-reduced
2. The leading one of every nonzero reduced row must have only zeros below it
-/
-- def RowEchelonForm (m n : Nat) (R : List (ReducedRow n)) :=
--   { l : RowEchelonList R // R.length = m}

/--
Function to evaluate a term of type `RowEchelonForm m n R`
as an m×n matrix that resembles R
-/
-- def RowEchelonForm.toMatrix (Q : RowEchelonList F R) : Matrix (Fin m) (Fin n) Rat :=
--   List.length_map R _ ▸ (R.map fun r => (r.toVector F).get).get

def RowEchelonForm.toMatrix {R : Vector (ReducedRow F n) m} (Q : RowEchelonForm F R) : Matrix (Fin m) (Fin n) F :=
  (R.map fun r => (r.toVector F).get).get

def r1 : ReducedRow Rat 2 := ⟨some 0,_,⟨[2],rfl⟩,by simp⟩
def r2 : ReducedRow Rat 2 := ⟨some 1,_,⟨[],rfl⟩,by simp⟩

def test1 : RowEchelonForm Rat ⟨[r2],rfl⟩ :=
  RowEchelonForm.cons r2 (RowEchelonForm.nil) (by intro r hr1 hr2; simp [Vector.mem_def] at hr1) (rfl)

def test2 : RowEchelonForm Rat ⟨[r1,r2],rfl⟩ :=
  RowEchelonForm.cons r1 test1 (by intro r hr; unfold r1 ReducedRow.toVector zeroVec; simp [r2,Vector.mem_def,Vector.head] at hr; simp [hr,Vector.replicate,Vector.append]) (by simp [r1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector])

#eval test2.toMatrix

#check List.last'

/--
A term of this type maps to a m×n matrix that satisfies the following conditions:
1. Every row must be row-reduced
2. The leading one of every nonzero reduced row must have only zeros above and below it
-/
-- inductive RowReducedEchelonForm : (R : Vector (ReducedRow F n) m) → Prop where
-- | nil : RowReducedEchelonForm Vector.nil
-- | cons : (row : ReducedRow F n) → RowReducedEchelonForm R →
--          ((row.toVector F).allZero) → RowReducedEchelonForm (R.concat row)
        --  (∀ r ∈ R, (hz : r.z.isSome) → row.toVector.get (r.z.get hz) = 0) →
        --  ((hz : row.z.isSome) → (R.map fun r => r.toVector.get (row.z.get hz)).all (fun x => x=0)) →
        --  (match R.getLast? with | none => true | some r => ¬(r.toVector = zeroVec n) ∨ row.toVector = zeroVec n) →
        --  RowReducedEchelonForm (R.concat row)

inductive RowReducedEchelonForm : (R : Vector (ReducedRow F n) m) → Prop where
| nil : RowReducedEchelonForm Vector.nil
| cons : (row : ReducedRow F n) → RowReducedEchelonForm R →
         (∀ r ∈ R, (hz : r.z.isSome) → (row.toVector F).get (r.z.get hz) = 0) →
         ((hz : row.z.isSome) → (R.map fun r => (r.toVector F).get (row.z.get hz)).allZero) →
         (match R.toList.head? with | none => true | some r => (((r.toVector F).allZero) ∨ ¬(row.toVector F).allZero)) →
        --  (match R.toList.head? with | none => true | some r => match r.z with | none => true | some rz => row.z < rz) →
         RowReducedEchelonForm (R.cons row)

-- try building matrix from below

#check List.reverseRecOn
#check List.reverseRecOn_concat
#check List.of_concat_eq_concat
#check List.concat
#check Vector.eq

theorem Vector.eq_iff (a1 a2 : Vector α n) : a1 = a2 ↔ toList a1 = toList a2 := by
  constructor
  intro h; rw [h]
  intro h; exact Vector.eq _ _ h

theorem Vector.of_concat_eq_concat {as bs : Vector α n} {a b : α} (h : as.concat a = bs.concat b) : as = bs ∧ a = b := by
  obtain ⟨l1,h1⟩ := as
  obtain ⟨l2,h2⟩ := bs
  simp [Vector.concat_eq_list_concat,Vector.eq_iff] at h
  rw [← List.concat_eq_append,← List.concat_eq_append] at h
  simp [Vector.eq_iff]
  exact List.of_concat_eq_concat h

-- lemma myLemma1 (l : Vector (ReducedRow F n) m) (l' : Vector (ReducedRow F n) (m+1)) (hl' : l' = l.concat r) (h : RowReducedEchelonForm F l') : (r.toVector F).allZero := by
--   match h with
--   | .cons row _ _ => have ⟨_,h2⟩ := Vector.of_concat_eq_concat hl'; subst h2; assumption

#check List.cons_eq_cons

theorem Vector.cons_eq_cons {a b : α} {v v' : Vector α n} : v.cons a = v'.cons b ↔ a = b ∧ v = v' := by
  obtain ⟨l,_⟩ := v
  obtain ⟨l',_⟩ := v'
  simp [Vector.cons,Vector.eq_iff]

lemma myLemma1 (l : Vector (ReducedRow F n) m) (l' : Vector (ReducedRow F n) (m+1)) (hl' : l' = l.cons row) (h : RowReducedEchelonForm F l') :
  (RowReducedEchelonForm F l) ∧ (∀ r ∈ l, (hz : r.z.isSome) → (row.toVector F).get (r.z.get hz) = 0)
  ∧ ((hz : row.z.isSome) → (l.map fun r => (r.toVector F).get (row.z.get hz)).allZero)
  ∧ (match l.toList.head? with | none => true | some r => (((r.toVector F).allZero) ∨ ¬(row.toVector F).allZero)) := by
  -- ∧ (match l.toList.head? with | none => true | some r => match r.z with | none => true | some rz => row.z < rz) := by
  match h with
  | .cons row H0 H1 H2 H3 => have ⟨h1,h2⟩ := Vector.cons_eq_cons.mp hl'; subst h1 h2; exact ⟨H0,H1,H2,H3⟩

lemma myLemma2 {l : Vector (ReducedRow F n) m} (hl : RowReducedEchelonForm F (l.cons row)) :
  (RowReducedEchelonForm F l) ∧ (∀ r ∈ l, (hz : r.z.isSome) → (row.toVector F).get (r.z.get hz) = 0)
  ∧ ((hz : row.z.isSome) → (l.map fun r => (r.toVector F).get (row.z.get hz)).allZero)
  ∧ (match l.toList.head? with | none => true | some r => (((r.toVector F).allZero) ∨ ¬(row.toVector F).allZero)) :=
  -- ∧ (match l.toList.head? with | none => true | some r => match r.z with | none => true | some rz => row.z < rz) :=
  myLemma1 F l (l.cons row) rfl hl

-- lemma myLemma3 (l : Vector (ReducedRow F n) m) (l' : Vector (ReducedRow F n) (m+1)) (hl' : l' = l.cons r) (h : RowReducedEchelonForm F l') : RowReducedEchelonForm F l := by
--   match h with
--   | .cons r' hl _ => have ⟨_,h2⟩ := Vector.cons_eq_cons.mp hl'; symm at h2; subst h2; assumption

-- lemma myLemma4 {l : Vector (ReducedRow F n) m} (hl : RowReducedEchelonForm F (l.cons r)) :
--   RowReducedEchelonForm F l := myLemma3 F l (l.cons r) rfl hl

instance (l : Vector (ReducedRow F n) m) (row : ReducedRow F n) : Decidable ((∀ r ∈ l, (hz : r.z.isSome) → (row.toVector F).get (r.z.get hz) = 0)) :=
  inferInstanceAs <| Decidable (∀ r ∈ l.toList, (hz : r.z.isSome) → (row.toVector F).get (r.z.get hz) = 0)

instance : Decidable (RowReducedEchelonForm F R) :=
  -- induction' R using Vector.inductionOn with _ row l ih
  -- · exact .isTrue (RowReducedEchelonForm.nil)
  -- · match ih with
  --   | isTrue hl =>
  --     if hr:(∀ r ∈ l, (hz : r.z.isSome) → (row.toVector F).get (r.z.get hz) = 0)
  --     ∧ ((hz : row.z.isSome) → (l.map fun r => (r.toVector F).get (row.z.get hz)).allZero)
  --     ∧ (match R.toList.head? with | none => true | some r => (((r.toVector F).allZero) ∨ ¬(row.toVector F).allZero)
          -- ∧ match r.z with | none => true | some rz => row.z < rz))
  --     then exact .isTrue (RowReducedEchelonForm.cons row hl hr.1 hr.2.1 hr.2.2)
  --       else exact .isFalse (by intro h; have := (myLemma2 _ h).2; contradiction)
  --   | isFalse hl => exact .isFalse (by intro h; have hr := (myLemma2 _ h).1; contradiction)

  R.inductionOn
  (.isTrue (RowReducedEchelonForm.nil))
  (fun _ {row} {l} ih => match ih with
    | isTrue hl =>
      if hr1:(∀ r ∈ l, (hz : r.z.isSome) → (row.toVector F).get (r.z.get hz) = 0) then
      if hr2: ((hz : row.z.isSome) → (l.map fun r => (r.toVector F).get (row.z.get hz)).allZero) then
      if hr3: (match l.toList.head? with | none => true | some r => ((r.toVector F).allZero) ∨ ¬(row.toVector F).allZero) then
      -- if hr4: ((hz : row.z.isSome) → match l.toList.head? with | none => true | some r => match r.z with | none => true | some rz => (row.z.get hz) < rz) then
      .isTrue (RowReducedEchelonForm.cons row hl hr1 hr2 (by match hs:l.toList.head? with | .none => simp | some s => simp [hs] at hr3 ⊢; exact hr3))
      -- else .isFalse (by intro h; have := (myLemma2 _ h).2.2.2.2; sorry)
      else .isFalse (by intro h; have := (myLemma2 _ h).2.2.2; match hs:l.toList.head? with | .none => simp [hs] at hr3 | some s => simp_rw [hs] at hr3 this; rw [decide_eq_true_eq] at hr3; contradiction)
      else .isFalse (by intro h; have := (myLemma2 _ h).2.2.1; contradiction)
      else .isFalse (by intro h; have := (myLemma2 _ h).2.1; contradiction)
    | isFalse hl => .isFalse (by intro h; have hr := (myLemma2 _ h).1; contradiction))

  -- | nil => exact .isTrue (RowReducedEchelonForm.nil)
  -- | cons x v ih =>
  -- | nil => exact .isTrue RowReducedEchelonList.nil
  -- | append_singleton l r ih =>
  --     rw [← List.concat_eq_append]
  --     match ih with
  --     | isTrue hl =>
  --       if hr:r.toVector.allZero then exact .isTrue (RowReducedEchelonList.cons r hl hr)
  --       else exact .isFalse (by intro h; have := myLemma2 h; contradiction)
  --     | isFalse h => exact .isFalse (by intro h; have := myLemma4 h; contradiction)
  -- R.toList.reverseRecOn
  -- (.isTrue .nil)
  -- (fun l r ih => by
  --     rw [← List.concat_eq_append]
  --     match ih with
  --     | isTrue hl =>
  --       if hr:r.toVector.allZero then exact .isTrue (RowReducedEchelonList.cons r hl hr)
  --       else exact .isFalse (by intro h; have := myLemma2 h; contradiction)
  --     | isFalse h => exact .isFalse (by intro h; have := myLemma4 h; contradiction))

def z1 : ReducedRow Rat 2 := ⟨none,_,⟨[],rfl⟩,by simp⟩

def m0 : RowReducedEchelonForm Rat ⟨[z1,z1],rfl⟩ := by decide

--define function to check all-zero vector

-- def RowReducedEchelonForm (m n : Nat) (R : List (ReducedRow n)) :=
--   { l : RowReducedEchelonList R // R.length = m}

def RowReducedEchelonForm.toMatrix {R : Vector (ReducedRow F n) m} (Q : RowReducedEchelonForm F R) : Matrix (Fin m) (Fin n) F :=
  (R.map fun r => (r.toVector F).get).get

#eval m0.toMatrix

def v0 : ReducedRow Rat 2 := ⟨none,_,⟨[],rfl⟩,by simp⟩
def v1 : ReducedRow Rat 2 := ⟨some 0,_,⟨[0],rfl⟩,by simp⟩
def v2 : ReducedRow Rat 2 := ⟨some 1,_,⟨[],rfl⟩,by simp⟩

def testm1 : RowReducedEchelonForm Rat ⟨[v1],rfl⟩ := by decide
  -- ⟨RowReducedEchelonList.cons v1 RowReducedEchelonList.nil (by intro r hr; simp at hr) (by simp) rfl,rfl⟩

def testm2 : RowReducedEchelonForm Rat ⟨[v1,v2],rfl⟩ := by decide
--  ⟨RowReducedEchelonList.cons v2 testm1.1 (by unfold v1 v2; intro r hr; simp at hr; simp [hr,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head]) (by unfold v1 v2 ReducedRow.toVector zeroVec; simp [Vector.replicate,Vector.append,Vector.get]) (by simp [v1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector]),rfl⟩

#eval testm2.toMatrix

def a1 : ReducedRow Rat 4 := ⟨some 0,_,⟨[0,4,0],rfl⟩,by simp⟩
def a2 : ReducedRow Rat 4 := ⟨some 1,_,⟨[3,0],rfl⟩,by simp⟩
def a3 : ReducedRow Rat 4 := ⟨some 3,_,⟨[],rfl⟩,by simp; rfl⟩
def a4 : ReducedRow Rat 4 := ⟨none,_,⟨[],rfl⟩,by simp⟩

def m1 : RowReducedEchelonForm Rat ⟨[a1,a4],rfl⟩ := by decide
  -- ⟨RowReducedEchelonList.cons a4 (RowReducedEchelonList.cons a3 (RowReducedEchelonList.cons a2 (RowReducedEchelonList.cons a1 RowReducedEchelonList.nil (by intro r hr1 hr2; simp at hr1) (by intro hz; simp) rfl) (by intro r hr1 hr2; simp at hr1; simp [hr1,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head]) (by intro hz; simp [a1,a2,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.get]) (by simp [a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector])) (by intro r hr1 hr2; simp at hr1; rcases hr1 with hr1|hr1 <;> simp [hr1,a3,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head,Vector.get]) (by intro hz; simp [a1,a2,a3,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.get,List.get]) (by simp [a2,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector])) (by intro r hr1 hr2; simp at hr1; rcases hr1 with hr1|hr1|hr1 <;> simp [hr1,a4,a3,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head,Vector.get,List.get]) (by intro hz; simp [a4] at hz) (by simp [a3,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector]),rfl⟩

#eval m1.toMatrix

-- def m2 : RowReducedEchelonForm 4 4 [a1,a2,a4,a3] :=
--   ⟨RowReducedEchelonList.cons a3 (RowReducedEchelonList.cons a4 (RowReducedEchelonList.cons a2 (RowReducedEchelonList.cons a1 RowReducedEchelonList.nil (by intro r hr1 hr2; simp at hr1) (by intro hz; simp) rfl) (by intro r hr1 hr2; simp at hr1; simp [hr1,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head]) (by intro hz; simp [a1,a2,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.get]) (by simp [a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector])) (by intro r hr1 hr2; simp at hr1; rcases hr1 with hr1|hr1 <;> simp [hr1,a4,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head,Vector.get]) (by intro hz; simp [a4] at hz) (by simp [a2,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector])) (by intro r hr1 hr2; simp at hr1; rcases hr1 with hr1|hr1|hr1; simp [hr1,a4,a3,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head,Vector.get,List.get]; simp [hr1,a4,a3,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head,Vector.get,List.get]; simp [hr1,a4] at hr2) (by intro hz; simp [a1,a2,a4,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.get,List.get]) (by simp [a4,a3,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector]),rfl⟩
-- --as expected
-- #eval m2.toMatrix
