module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetFromBlocksSingle
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

namespace GlobalTheory

open Matrix

theorem det_gram_two_frames {K : Type} [CommRing K] (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (T T' : K) :
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -T else 0) Z W
      (Matrix.diagonal fun i => if i = Fin.last r then -T' else 0)).det
      = (-1) ^ (r + 1) * (Z.det * W.det - T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det
          * (W.submatrix Fin.castSucc Fin.castSucc).det)) := by
  apply GlobalTheory.SA.TransvG.det_fromBlocks_last

end GlobalTheory
