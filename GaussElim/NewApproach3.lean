import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fin.Tuple.Reflection

variable (F : Type) [Field F] [DecidableEq F]

inductive RowEchelonForm : (m n : Nat) → Type where
| nil : RowEchelonForm m 0
| pad : RowEchelonForm m n → RowEchelonForm m n.succ
| extend : RowEchelonForm m n → Vector F n → RowEchelonForm m n.succ

def mat := !![1,2,3;4,5,6;7,8,9]
def v1 := ![1,2,3]
#eval FinVec.map (fun r => (Fin.cons 0 r : Fin _ → ℕ)) mat

def RowEchelonForm.toMatrix (R : RowEchelonForm F m n) : Matrix (Fin m) (Fin n) F :=
  match R with
  | nil => fun x => ![]
  | pad R0 => fun R => FinVec.map (fun r => (Fin.cons 0 r : Fin _ → F)) R
  | extend R0 v => sorry
