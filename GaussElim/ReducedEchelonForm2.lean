import Mathlib.Data.Matrix.Notation

variable {F : Type} [Field F] [DecidableEq F]

structure ReducedRow0 (n : Nat)

structure ReducedRowN0 (F : Type) [Field F] [DecidableEq F] (n : Nat) where
  z : Fin n
  k : Nat
  tail : Vector F k
  h : n = z + k + 1

def ReducedRow (F : Type) [Field F] [DecidableEq F] (n : Nat) := Sum (ReducedRow0 n) (ReducedRowN0 F n)

def zeroVec (k: Nat) : Vector F k := Vector.replicate k 0

def ReducedRow0.toVector (_ : ReducedRow0 n): Vector F n := zeroVec n

def ReducedRowN0.toVector (row : ReducedRowN0 F n): Vector F n := row.h ▸ (zeroVec row.z).append (Vector.cons 1 row.tail)

def ReducedRow.toVector (row : ReducedRow F n): Vector F n :=
  match row with
  | .inl row0 => row0.toVector
  | .inr rowN0 => rowN0.toVector

def Vector.isReducedRowN0 (v : Vector F n) : Prop := ∃ r : ReducedRowN0 F n, v = r.toVector

def Vector.any (v : Vector F n) (p : F → Bool) := v.toList.any p

@[simp] theorem Vector.any_def (v : Vector F n) (p : F → Bool) : v.any p = v.toList.any p := rfl

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

theorem Vector.firstNonzElt_cons_non0 {v : Vector F n} (h: v.any (· ≠ 0)) {x : F} (hx : x ≠0) :
  (Vector.cons x v).firstNonzElt (by simp [hx]) = (⟨x,hx⟩,⟨⟨0,by simp⟩,v⟩) := by
  induction' v using Vector.inductionOn with _ x w hw
  · simp at h
  · sorry

def v : Vector Rat 5 := ⟨[0,0,4,2,3],rfl⟩
#eval v.firstNonzElt (by decide)

lemma Vector.eq_firstNonzEltAppend (v : Vector F n) (h: v.any (· ≠ 0)) :
  let (⟨x,hx⟩,⟨i,t⟩) := v.firstNonzElt h; v = (((Vector.replicate i 0).append (t.cons x)).congr (by simp; apply Nat.add_sub_of_le (Nat.succ_le_of_lt i.2)) := by
    induction' v using Vector.inductionOn with _ x w hw
    · simp at h
    · sorry
      rw [firstNonzElt]
      -- split_ifs
      -- · sorry
      -- · sorry



theorem Vector.isreducedRowN0_conds (v : Vector F n) (h: v.any (· ≠ 0)) :
  (v.firstNonzElt h).1 = ⟨1,by norm_num⟩ → v.isReducedRowN0 := by
  intro hv
  let (⟨x,hx⟩,⟨i,t⟩) := v.firstNonzElt h
  let r : ReducedRowN0 F n := ⟨i,(n-i-1),t,sorry⟩
  use r
  dsimp [ReducedRowN0.toVector,zeroVec]
  rw [eq_firstNonzEltAppend v h]
