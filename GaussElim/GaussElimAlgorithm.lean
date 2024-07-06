import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basis
import GaussElim.ReducedEchelonForm2

variable {F : Type} [Field F] [DecidableEq F]

/--
`ElemOp F m` is the type of elementary row operations that can be performed on
a matrix with m rows in the field F
-/
inductive ElemOp (F : Type) [Field F] [DecidableEq F] (m : ℕ) : Type where
| scalarMul (c : F) (hc : c≠0) (i : Fin m)
| rowSwap (i : Fin m) (j : Fin m)
| rowMulAdd (c : F) (i : Fin m) (j : Fin m) (hij : i≠j)
deriving Repr,BEq

/--
Operates an `E : ElemOp F m` on the m×n matrix `A`
-/
def ElemOp.onMatrix (E : ElemOp F m) (A : Matrix (Fin m) (Fin n) F) : Matrix (Fin m) (Fin n) F :=
match E with
| scalarMul c _ i => A.updateRow i (c • (A i))
| rowSwap i j => let newr := (A i)
    Matrix.updateRow (Matrix.updateRow A i (A j)) j newr
| rowMulAdd c i j _ => A.updateRow i (A i + (c • (A j)))

/--
Operates a list of `ElemOp`s on the matrix `A`
-/
def ElemOp.listOnMatrix (l : List (ElemOp F m)) (A : Matrix (Fin m) (Fin n) F) : Matrix (Fin m) (Fin n) F :=
  match l with
  | [] => A
  | E::as => ElemOp.onMatrix E (ElemOp.listOnMatrix as A)

/--
The elementary matrix corresponding to an elementary operation, obtained by
operating it on the identity matrix
-/
def ElemOp.elemMat (E : ElemOp F m) := ElemOp.onMatrix E (1:Matrix (Fin m) (Fin m) F)

variable (M : Matrix (Fin m) (Fin n) F)


abbrev Matrix.colList := (List.ofFn M.transpose).map Vector.ofFn

abbrev Vector.allZero (v : Vector F n) := v.toList.all (.=0)

lemma Vector.allZero_not_anyN0 (v : Vector F n) : ¬ v.allZero ↔ v.any (.≠0) := by
  constructor <;> (intro hv;simp at hv ⊢; exact hv)

lemma Matrix.colList_get (i : Fin m) (j : Fin n) : (M.colList.get (j.cast (by simp))).get i = M i j := by simp

def findPivotAuxN0 (l : List (Vector F m)) (hl : l.any (fun c => ¬c.allZero)) : {c : F // c≠0}×(i : Fin m)×{j : Fin l.length // (l.get j).get i = c}:=
    match l with
    | [] => by simp at hl
    | col::as =>
      if hc : ¬ (col.allZero) then
        let ⟨piv,rowInd,_⟩ := (col.firstNonzElt (col.allZero_not_anyN0.mp (by simp at hc ⊢; exact hc)))
        (piv,⟨rowInd,⟨⟨0,_⟩,_⟩⟩)
      else
        have as_nontriv: as.any (fun c => ¬c.allZero) := by
          simp at hc
          simp [List.any_cons, hc] at hl
          rcases hl with hl|hl
          · rcases hl with ⟨x,xc,hx⟩; have := hc x xc; contradiction
          · simp [hl]
        have ha : as.length ≠ 0 := by contrapose as_nontriv; simp at as_nontriv ⊢; simp [as_nontriv]
        let (piv,⟨rowInd,⟨colInd,hpiv⟩⟩) := findPivotAuxN0 as as_nontriv
        (piv,rowInd,⟨n-as.length,by refine Nat.div_rec_lemma ⟨Nat.zero_lt_of_ne_zero ha,Nat.le_of_succ_le hn⟩⟩)

lemma findPivotAuxN0_colIndLT (l : List (Vector F m)) (hl : l.any (fun c => ¬c.allZero)) (j : Nat) : (findPivotAuxN0 l hl j).2.2 < l.length := by
  induction l with
  | nil => simp [List.any] at hl
  | cons h tl tl_ih =>
    dsimp [findPivotAuxN0]
    split <;> simp
    apply tl_ih

-- How to track column index of pivot and show that matrix has nonzer entry at those coordinates

def mat : List (Vector Rat 3) := [⟨[0,0,0],rfl⟩,⟨[0,0,0],rfl⟩,⟨[4,0,0],rfl⟩]
#eval findPivotAuxN0 mat (by decide) 0

lemma Matrix.zero_eq_colListZero (hM : M = 0) : M.colList.all (fun c => c.allZero) := by
  simp [colList,hM]

#check List.rec

def findPivotN0 (hM : M ≠ 0) : {c : F // c≠0}×(Fin m)×(Fin n) :=
  have hl : M.colList.any (fun c => ¬c.allZero) := by
    contrapose hM
    push_neg at *
    simp at hM
    apply Matrix.ext
    simp
    intro i j
    exact hM j i
  let (piv,rowInd,_) := findPivotAuxN0 M.colList hl 0
  have hM : M (findPivotAuxN0 M.colList hl 0).2.1 ⟨(findPivotAuxN0 M.colList hl 0).2.2,by convert findPivotAuxN0_colIndLT M.colList hl 0; simp⟩ = (findPivotAuxN0 M.colList hl 0).1 := by
    generalize M.colList = l at *
    induction M.colList using List.rec with
    | nil => sorry
    | cons head tail ih => sorry

  (piv,rowInd,⟨(findPivotAuxN0 M.colList hl 0).2.2,(by convert findPivotAuxN0_colIndLT M.colList hl 0; simp)⟩)

def findPivot_toElemOp (pivData : {c : F // c≠0}×(Fin m)) : List (ElemOp F m) :=
  let (⟨c,hc⟩,i) := pivData
  [ElemOp.scalarMul c hc i,ElemOp.rowSwap i ⟨0,Fin.pos i⟩]

-- def elimColBelowPiv (pivData : {c : F // c≠0}×(Fin m)) (hrow : Vector.ofFn (M 0))
--   let colInd :=
