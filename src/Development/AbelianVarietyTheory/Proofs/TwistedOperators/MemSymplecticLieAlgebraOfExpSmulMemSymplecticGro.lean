module

import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieF
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

open scoped Matrix

namespace GlobalTheory.RealWeil

theorem mem_sp_of_exp_mem_symplecticGroup (l : Type) [Fintype l] [DecidableEq l]
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) :
    X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  apply PositivityTheory.RL.Up.mem_lie_of <;> assumption

end GlobalTheory.RealWeil
