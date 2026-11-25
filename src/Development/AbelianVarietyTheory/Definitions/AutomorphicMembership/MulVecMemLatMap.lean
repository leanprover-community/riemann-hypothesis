module

public import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FractionFieldToGenericStalkAlgebraMapEq
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

section Tri

variable {m : ℕ} {u v : Matrix (Fin m) (Fin m) E}

def simpleSum {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E := ∑ a : Fin r, A a.castSucc a.succ

end Tri

section Frames

variable {σ : E →+* E} {n r : ℕ} {J s : Matrix (Fin n) (Fin n) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

end Frames

section Lattices

variable [NumberField E] {σ : E →+* E} {n r : ℕ} {J s : Matrix (Fin n) (Fin n) E}
  {P P' : Matrix (Fin n) (Fin (r + 1)) E} {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Λ M : Submodule (𝓞 E) (Fin n → E)}





end Lattices

end GlobalTheory.IntTerm
