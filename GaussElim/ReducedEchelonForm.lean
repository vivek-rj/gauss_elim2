import Mathlib.Data.Matrix.Notation

abbrev colVecofMat (M : Matrix (Fin m) (Fin n) Rat) := (Vector.ofFn M.transpose).map Vector.ofFn

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
  tail : Vector Rat k
  h : (hz : z = some p) → n = p + k + 1

def zeroVec (k: Nat) : Vector Rat k := Vector.replicate k 0

/--
Form a Vector from the data stored in the `ReducedRow` type
-/
def ReducedRow.toVector (row : ReducedRow n): Vector Rat (n) :=
  match hz:row.z with
  | none => zeroVec n
  | some p => row.h hz ▸ (zeroVec p).append (Vector.cons 1 row.tail)

#eval ReducedRow.toVector (n:=5) ⟨some 2,2,⟨[3,4],rfl⟩,by simp⟩
#eval ReducedRow.toVector (n:=4) ⟨none,_,⟨[],rfl⟩,by simp⟩

inductive RowEchelonList : (R : List (ReducedRow n)) → Type where
| nil : RowEchelonList []
| cons : (row : ReducedRow n) → RowEchelonList R → (∀ r ∈ R, (hz : r.z.isSome) → row.toVector.get (r.z.get hz) = 0) → (match R.getLast? with | none => true | some r => ¬(r.toVector = zeroVec n) ∨ row.toVector = zeroVec n) → RowEchelonList (R.concat row)

--(match R with | [] => true | r::_ => ¬(r.toVector = zeroVec n) ∨ row.toVector = zeroVec n)

/--
A term of this type maps to an m×n matrix that satisies the following conditions:
1. Every row must be row-reduced
2. The leading one of every nonzero reduced row must have only zeros below it
-/
def RowEchelonForm (m n : Nat) (R : List (ReducedRow n)) :=
  { l : RowEchelonList R // R.length = m}

/--
Function to evaluate a term of type `RowEchelonForm m n R`
as an m×n matrix that resembles R
-/
def RowEchelonForm.toMatrix (Q : RowEchelonForm m n R) : Matrix (Fin m) (Fin n) Rat :=
  Q.2 ▸ List.length_map R _ ▸ (R.map fun r => r.toVector.get).get

def r1 : ReducedRow 2 := ⟨some 0,_,⟨[2],rfl⟩,by simp⟩
def r2 : ReducedRow 2 := ⟨some 1,_,⟨[],rfl⟩,by simp⟩

def test1 : RowEchelonForm 1 2 [r1] :=
  ⟨RowEchelonList.cons r1 (RowEchelonList.nil) (by intro r hr1 hr2; simp at hr1) (rfl),rfl⟩

def test2 : RowEchelonForm 2 2 [r1,r2] :=
  ⟨RowEchelonList.cons r2 test1.1 (by intro r hr; unfold r2 ReducedRow.toVector zeroVec; unfold r1 at hr; simp at hr; simp [hr,Vector.replicate,Vector.append,Vector.head]) (by simp [r1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector]),rfl⟩

#eval test2.toMatrix

#check List.last'

/--
A term of this type maps to a m×n matrix that satisfies the following conditions:
1. Every row must be row-reduced
2. The leading one of every nonzero reduced row must have only zeros above and below it
-/
inductive RowReducedEchelonList : (R : List (ReducedRow n)) → Type where
| nil : RowReducedEchelonList []
| cons : (row : ReducedRow n) → RowReducedEchelonList R → (∀ r ∈ R, (hz : r.z.isSome) → row.toVector.get (r.z.get hz) = 0) → ((hz : row.z.isSome) → (R.map fun r => r.toVector.get (row.z.get hz)).all (fun x => x=0)) → (match R.getLast? with | none => true | some r => ¬(r.toVector = zeroVec n) ∨ row.toVector = zeroVec n) → RowReducedEchelonList (R.concat row)

def RowReducedEchelonForm (m n : Nat) (R : List (ReducedRow n)) :=
  { l : RowReducedEchelonList R // R.length = m}

def RowReducedEchelonForm.toMatrix (Q : RowReducedEchelonForm m n R) : Matrix (Fin m) (Fin n) Rat :=
  Q.2 ▸ List.length_map R _ ▸ (R.map fun r => r.toVector.get).get

def v1 : ReducedRow 2 := ⟨some 0,_,⟨[0],rfl⟩,by simp⟩
def v2 : ReducedRow 2 := ⟨some 1,_,⟨[],rfl⟩,by simp⟩

def testm1 : RowReducedEchelonForm 1 2 [v1] :=
  ⟨RowReducedEchelonList.cons v1 RowReducedEchelonList.nil (by intro r hr; simp at hr) (by simp) rfl,rfl⟩

def testm2 : RowReducedEchelonForm 2 2 [v1,v2] :=
 ⟨RowReducedEchelonList.cons v2 testm1.1 (by unfold v1 v2; intro r hr; simp at hr; simp [hr,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head]) (by unfold v1 v2 ReducedRow.toVector zeroVec; simp [Vector.replicate,Vector.append,Vector.get]) (by simp [v1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector]),rfl⟩

#eval testm2.toMatrix

def a1 : ReducedRow 4 := ⟨some 0,_,⟨[0,4,0],rfl⟩,by simp⟩
def a2 : ReducedRow 4 := ⟨some 1,_,⟨[3,0],rfl⟩,by simp⟩
def a3 : ReducedRow 4 := ⟨some 3,_,⟨[],rfl⟩,by simp; rfl⟩
def a4 : ReducedRow 4 := ⟨none,_,⟨[],rfl⟩,by simp⟩

def m1 : RowReducedEchelonForm 4 4 [a1,a2,a3,a4] :=
  ⟨RowReducedEchelonList.cons a4 (RowReducedEchelonList.cons a3 (RowReducedEchelonList.cons a2 (RowReducedEchelonList.cons a1 RowReducedEchelonList.nil (by intro r hr1 hr2; simp at hr1) (by intro hz; simp) rfl) (by intro r hr1 hr2; simp at hr1; simp [hr1,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head]) (by intro hz; simp [a1,a2,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.get]) (by simp [a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector])) (by intro r hr1 hr2; simp at hr1; rcases hr1 with hr1|hr1 <;> simp [hr1,a3,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head,Vector.get]) (by intro hz; simp [a1,a2,a3,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.get,List.get]) (by simp [a2,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector])) (by intro r hr1 hr2; simp at hr1; rcases hr1 with hr1|hr1|hr1 <;> simp [hr1,a4,a3,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head,Vector.get,List.get]) (by intro hz; simp [a4] at hz) (by simp [a3,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector]),rfl⟩

#eval m1.toMatrix

-- def m2 : RowReducedEchelonForm 4 4 [a1,a2,a4,a3] :=
--   ⟨RowReducedEchelonList.cons a3 (RowReducedEchelonList.cons a4 (RowReducedEchelonList.cons a2 (RowReducedEchelonList.cons a1 RowReducedEchelonList.nil (by intro r hr1 hr2; simp at hr1) (by intro hz; simp) rfl) (by intro r hr1 hr2; simp at hr1; simp [hr1,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head]) (by intro hz; simp [a1,a2,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.get]) (by simp [a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector])) (by intro r hr1 hr2; simp at hr1; rcases hr1 with hr1|hr1 <;> simp [hr1,a4,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head,Vector.get]) (by intro hz; simp [a4] at hz) (by simp [a2,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector])) (by intro r hr1 hr2; simp at hr1; rcases hr1 with hr1|hr1|hr1; simp [hr1,a4,a3,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head,Vector.get,List.get]; simp [hr1,a4,a3,a2,a1,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head,Vector.get,List.get]; simp [hr1,a4] at hr2) (by intro hz; simp [a1,a2,a4,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.get,List.get]) (by simp [a4,a3,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector]),rfl⟩
-- --as expected
-- #eval m2.toMatrix
