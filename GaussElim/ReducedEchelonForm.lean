import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.Linarith

variable (F : Type) [Field F] [DecidableEq F] [Repr F] (M : Matrix (Fin m) (Fin n) Rat)

/--
Vector containing rows of the matrix as vectors
-/
abbrev rowVecofMat := (Vector.ofFn M).map Vector.ofFn

/--
Vector containing columns of the matrix as vectors
-/
abbrev colVecofMat := (Vector.ofFn M.transpose).map Vector.ofFn

/-Row-reduced form
1. The first nonzero entry of every row must be 1
2. Each column containing the first nonzero entry of a row must have all its other
   entries as 0
-/

def vector_isPrefixOf : Vector F k → Vector F k → Bool :=
  fun v => fun w => List.isPrefixOf v.toList w.toList

abbrev vec_allZero (v : Vector Rat k) : Bool := v.toList.all (fun x => (x==0))

structure ReducedRow (n : Nat) where
  z : Option (Fin n)
  k : Nat
  tail : Vector Rat k
  h : (hz : z = some p) → n = p + k + 1

def zeroVec (k: Nat) : Vector Rat k := Vector.replicate k 0

def ReducedRow.toVector (row : ReducedRow n): Vector Rat (n) :=
  match hz:row.z with
  | none => zeroVec n
  | some p => row.h hz ▸ (zeroVec p).append (Vector.cons 1 row.tail)

#eval ReducedRow.toVector (n:=5) ⟨some 2,2,⟨[3,4],rfl⟩,by simp⟩
#eval ReducedRow.toVector (n:=4) ⟨none,_,⟨[],rfl⟩,by simp⟩

--padding : size of [0,0,...,0,1] pattern in a ReducedRow

-- inductive RowEchelonList : (padding : Nat) → (R : List (ReducedRow n)) → Type where
-- | nil : RowEchelonList 0 []
-- | cons : (row : ReducedRow n) → RowEchelonList padding R → row.z+1 > padding → RowEchelonList row.z (R.concat row)

-- def RowEchelonForm (m n : Nat) {padding : Nat} (R : List (ReducedRow n)) :=
--   { l : RowEchelonList padding R // R.length = m}

-- def RowEchelonForm.toMatrix {padding : Nat} (Q : RowEchelonForm m n R (padding:=padding)) : Matrix (Fin m) (Fin n) Rat :=
--   Q.2 ▸ List.length_map R _ ▸ (R.map fun r => r.toVector.get).get

-- def testl : List (ReducedRow 2) := [⟨0,_,⟨[2],rfl⟩,rfl⟩,⟨1,_,⟨[],rfl⟩,rfl⟩]

-- def r1 : ReducedRow 2 := ⟨0,_,⟨[2],rfl⟩,rfl⟩
-- def r2 : ReducedRow 2 := ⟨1,_,⟨[],rfl⟩,rfl⟩

-- def test1 : RowEchelonForm 1 2 [r1] (padding:=0) :=
--   ⟨RowEchelonList.cons r1 RowEchelonList.nil (Nat.zero_lt_succ _),rfl⟩

-- def testm : RowEchelonForm 2 2 testl (padding:=1) :=
--   ⟨RowEchelonList.cons r2 (RowEchelonList.cons r1 RowEchelonList.nil (Nat.zero_lt_succ _)) (by unfold r2 r1; simp),rfl⟩

-- #eval testm.toMatrix

inductive RowEchelonList : (R : List (ReducedRow n)) → Type where
| nil : RowEchelonList []
| cons : (row : ReducedRow n) → RowEchelonList R → (∀ r ∈ R, (hz : r.z.isSome) → row.toVector.get (r.z.get hz) = 0) → RowEchelonList (R.concat row)

def RowEchelonForm (m n : Nat) (R : List (ReducedRow n)) :=
  { l : RowEchelonList R // R.length = m}

def RowEchelonForm.toMatrix (Q : RowEchelonForm m n R) : Matrix (Fin m) (Fin n) Rat :=
  Q.2 ▸ List.length_map R _ ▸ (R.map fun r => r.toVector.get).get

def r1 : ReducedRow 2 := ⟨some 0,_,⟨[2],rfl⟩,by simp⟩
def r2 : ReducedRow 2 := ⟨some 1,_,⟨[],rfl⟩,by simp⟩

def test1 : RowEchelonForm 1 2 [r1] :=
  ⟨RowEchelonList.cons r1 (RowEchelonList.nil) (by intro r hr1 hr2; simp at hr1),rfl⟩

def test2 : RowEchelonForm 2 2 [r1,r2] :=
  ⟨RowEchelonList.cons r2 test1.1 (by intro r hr; unfold r2 ReducedRow.toVector zeroVec; unfold r1 at hr; simp at hr; simp [hr,Vector.replicate,Vector.append,Vector.head]),rfl⟩

#eval test2.toMatrix

/-
Row-reduced echelon form
1. The matrix must be row-reduced
2. All rows that have only 0s must occur before those that have a nonzero entry
3. If rows 1,...,r are the nonzero rows and the first nonzero entry for each of
these rows occurs in columns k₁,k₂,...,k_r, then  k₁< k₂<...< k_r
-/

inductive RowReducedEchelonList : (R : List (ReducedRow n)) → Type where
| nil : RowReducedEchelonList []
| cons : (row : ReducedRow n) → RowReducedEchelonList R → (∀ r ∈ R, (hz : r.z.isSome) → row.toVector.get (r.z.get hz) = 0) → ((R.map (fun r => r.z.map (fun p => r.toVector.get p))).all (fun x => x=some 0)) → RowReducedEchelonList (R.concat row)

--((R.map (fun r => r.z.map (fun p => r.toVector.get p))).all (fun x => x=some 0)) ???

def RowReducedEchelonForm (m n : Nat) (R : List (ReducedRow n)) :=
  { l : RowReducedEchelonList R // R.length = m}

def RowReducedEchelonForm.toMatrix (Q : RowReducedEchelonForm m n R) : Matrix (Fin m) (Fin n) Rat :=
  Q.2 ▸ List.length_map R _ ▸ (R.map fun r => r.toVector.get).get

def v1 : ReducedRow 2 := ⟨some 0,_,⟨[0],rfl⟩,by simp⟩
def v2 : ReducedRow 2 := ⟨some 1,_,⟨[],rfl⟩,by simp⟩

def testm1 : RowReducedEchelonForm 1 2 [v1] :=
  ⟨RowReducedEchelonList.cons v1 RowReducedEchelonList.nil (by intro r hr; simp at hr) (by simp),rfl⟩

def testm2 : RowReducedEchelonForm 2 2 [v1,v2] :=
 ⟨RowReducedEchelonList.cons v2 testm1.1 (by unfold v1 v2; intro r hr; simp at hr; simp [hr,ReducedRow.toVector,zeroVec,Vector.replicate,Vector.append,Vector.head]) (by unfold v1 v2 ReducedRow.toVector zeroVec; simp [Vector.replicate,Vector.append,Vector.get]),rfl⟩

#eval testm2.toMatrix

def a1 : ReducedRow 4 := ⟨some 0,_,⟨[0,4,0],rfl⟩,by simp⟩
def a2 : ReducedRow 4 := ⟨some 1,_,⟨[1,3],rfl⟩,by simp⟩
def a3 : ReducedRow 4 := ⟨some 3,_,⟨[],rfl⟩,by simp; rfl⟩
def a4 : ReducedRow 4 := ⟨none,_,⟨[],rfl⟩,by simp⟩

def m1 : RowReducedEchelonForm 4 4 [a1,a2,a3,a4] :=
  ⟨RowReducedEchelonList.cons a4 (RowReducedEchelonList.cons a3 (RowReducedEchelonList.cons a2 (RowReducedEchelonList.cons a1 RowReducedEchelonList.nil))),rfl⟩
