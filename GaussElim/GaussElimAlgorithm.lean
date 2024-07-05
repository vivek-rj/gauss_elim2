import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basis
import GaussElim.ReducedEchelonForm2

variable {F : Type} [Field F] [DecidableEq F]

inductive ElemOp (F : Type) [Field F] [DecidableEq F] (m : ℕ) : Type where
| scalarMul (c : F) (hc : c≠0) (i : Fin m)
| rowSwap (i : Fin m) (j : Fin m)
| rowMulAdd (c : F) (i : Fin m) (j : Fin m) (hij : i≠j)
deriving Repr,BEq

def ElemOp.onMatrix (E : ElemOp F m) (A : Matrix (Fin m) (Fin k) F) : Matrix (Fin m) (Fin k) F :=
match E with
| scalarMul c _ i => A.updateRow i (c • (A i))
| rowSwap i j => let newr := (A i)
    Matrix.updateRow (Matrix.updateRow A i (A j)) j newr
| rowMulAdd c i j _ => A.updateRow i (A i + (c • (A j)))

def ElemOp.listOnMatrix (l : List (ElemOp F m)) (A : Matrix (Fin m) (Fin n) F) : Matrix (Fin m) (Fin n) F :=
  match l with
  | [] => A
  | E::as => ElemOp.onMatrix E (ElemOp.listOnMatrix as A)

def ElemOp.elemMat (E : ElemOp F m) := ElemOp.onMatrix E (1:Matrix (Fin m) (Fin m) F)

variable (M : Matrix (Fin m) (Fin n) F)

def botRight (i : Fin m) (j : Fin n) : Matrix (Fin (m-i)) (Fin (n-j)) F :=
  M.submatrix (fun k => ⟨k+i,Nat.add_lt_of_lt_sub k.2⟩) (fun l => ⟨l+j,Nat.add_lt_of_lt_sub l.2⟩)

abbrev Matrix.colList := (List.ofFn M.transpose).map Vector.ofFn

abbrev Vector.allZero (v : Vector F n) := v.toList.all (.=0)

lemma Vector.allZero_not_anyN0 (v : Vector F n) : ¬ v.allZero ↔ v.any (.≠0) := by
  constructor <;> (intro hv;simp at hv ⊢; exact hv)

def findPivotAuxN0 (l : List (Vector F m)) (hl : l.any (fun c => ¬c.allZero)) (j : Nat) : {c : F // c≠0}×(Fin m)×(Nat) :=
    match l with
    | [] => by simp at hl
    | col::as =>
      if hc : ¬ (col.allZero) then
        let ⟨piv,rowInd,_⟩ := (col.firstNonzElt (col.allZero_not_anyN0.mp (by simp at hc ⊢; exact hc)))
        (piv,rowInd,0)
      else
        by
        have as_nontriv: as.any (fun c => ¬c.allZero) := by
          simp at hc
          simp [List.any_cons, hc] at hl
          rcases hl with hl|hl
          · rcases hl with ⟨x,xc,hx⟩; have := hc x xc; contradiction
          · simp [hl]
        let (piv,rowInd,colInd) := findPivotAuxN0 as as_nontriv j
        exact (piv,rowInd,colInd+1)

-- How to track column index of pivot and show that matrix has nonzer entry at those coordinates

def mat : List (Vector Rat 3) := [⟨[0,0,0],rfl⟩,⟨[0,0,0],rfl⟩,⟨[4,0,0],rfl⟩]
#eval findPivotAuxN0 mat (by decide) 0

lemma Matrix.zero_eq_colListZero (hM : M = 0) : M.colList.all (fun c => c.allZero) := by
  simp [colList,hM]

def findPivotN0 (hM : M ≠ 0) : {c : F // c≠0}×(Fin m)×(Fin n) :=
  have hl : M.colList.any (fun c => ¬c.allZero) := by
    contrapose hM
    push_neg at *
    simp at hM
    apply Matrix.ext
    simp
    intro i j
    exact hM j i
  let (piv,rowInd,colInd) := findPivotAuxN0 M.colList hl 0
  have hr : (Vector.ofFn (M rowInd)).any (.≠0) := by
    simp
    use piv
    constructor
    · sorry
    · exact piv.2
  (piv,rowInd,((Vector.ofFn (M rowInd)).firstNonzElt hr).2.1)

def findPivot_toElemOp (pivData : {c : F // c≠0}×(Fin m)) : List (ElemOp F m) :=
  let (⟨c,hc⟩,i) := pivData
  [ElemOp.scalarMul c hc i,ElemOp.rowSwap i ⟨0,Fin.pos i⟩]

-- def elimColBelowPiv (pivData : {c : F // c≠0}×(Fin m)) (hrow : Vector.ofFn (M 0))
--   let colInd :=
