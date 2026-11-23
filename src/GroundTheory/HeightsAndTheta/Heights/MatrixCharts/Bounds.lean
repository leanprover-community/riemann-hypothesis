module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCBounds

open Matrix
open scoped ComplexOrder

noncomputable section

variable (D : PeriodChartData)

theorem log_inv_sq_nonneg {w : ℂ} (hw : ‖w‖ < 1) : 0 ≤ Real.log (‖w‖ ^ 2)⁻¹ := by
  rw [Real.log_inv]
  exact neg_nonneg.mpr (Real.log_nonpos (by positivity) (pow_le_one₀ (norm_nonneg w) hw.le))

theorem injective_of_rank {g rk : ℕ} (F : Matrix (Fin g) (Fin rk) ℂ) (h : F.rank = rk) :
    Function.Injective F.mulVec := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin F)
  rw [Module.finrank_fin_fun] at h1
  have h2 : Module.finrank ℂ (LinearMap.ker F.mulVecLin) = 0 := by
    rw [← Matrix.finrank_range_mulVecLin] at h; omega
  have h3 : LinearMap.ker F.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h2
  exact LinearMap.ker_eq_bot.mp h3

theorem gram_posDef {g rk : ℕ} (F : Matrix (Fin g) (Fin rk) ℂ) (h : F.rank = rk) :
    (Fᴴ * F).PosDef :=
  PosDef.conjTranspose_mul_self F (injective_of_rank F h)

end

end GroundTheory.Heights₂.Heights.MCBounds
