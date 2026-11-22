module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaN

@[expose] public section

noncomputable section

open Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

def LowUni {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Bl.FirstLemmaN.goal1 L

def UpTri {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j, j < i → U i j = 0

def blk {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => Fin.lastCases (Fin.lastCases e row j) (fun i' => Fin.lastCases (col i') (fun j' => P i' j') j) i

@[simp] theorem blk_cc {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk P col row e i.castSucc j.castSucc = P i j := by simp [blk]

@[simp] theorem blk_cl {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk P col row e i.castSucc (Fin.last n) = col i := by simp [blk]

@[simp] theorem blk_lc {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk P col row e (Fin.last n) j.castSucc = row j := by simp [blk]

@[simp] theorem blk_ll {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) :
    blk P col row e (Fin.last n) (Fin.last n) = e := by simp [blk]

theorem det_lowUni {n : ℕ} {L : Matrix (Fin n) (Fin n) ℂ} (h : LowUni L) : L.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular L (fun i j hij => h.1 i j hij)]
  simp [h.2]

end PI.UnitaryGroupMassFormula.HwConjInf
