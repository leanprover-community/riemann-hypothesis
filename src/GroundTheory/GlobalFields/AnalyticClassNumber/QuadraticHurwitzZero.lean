import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

open Complex HurwitzZeta Filter Topology Set

namespace GroundTheory.Global.Quadratic




def hurwitzCombTerm (x : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (((n : ℝ) + x : ℝ) : ℂ) ^ (-s) + ((1 - 2 * x : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) +
    ((2 * x - 2 : ℝ) : ℂ) * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s)

def hurwitzComb (x : ℝ) (s : ℂ) : ℂ :=
  hurwitzZeta x s + ((1 - 2 * x : ℝ) : ℂ) * hurwitzZeta (1 : ℝ) s +
    ((2 * x - 2 : ℝ) : ℂ) * hurwitzZeta (1 / 2 : ℝ) s












end Quadratic

end GroundTheory.Global
