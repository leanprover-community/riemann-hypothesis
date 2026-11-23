module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

theorem br_sum_log_norm_sq (M : IntermediateField ℚ ℂ) [NumberField M] (s : M) (hs : s ≠ 0) :
    ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (‖ρ s‖ ^ 2) = 2 * Real.log |((Algebra.norm ℚ s : ℚ) : ℝ)| := by
  have hρ : ∀ ρ : M →ₐ[ℚ] ℂ, ρ s ≠ 0 := fun ρ => (map_ne_zero ρ).2 hs
  rw [← Real.log_prod (fun ρ _ => by have := hρ ρ; positivity)]
  have hN := Algebra.norm_eq_prod_embeddings ℚ ℂ s
  have h1 : ∏ ρ : M →ₐ[ℚ] ℂ, ‖ρ s‖ ^ 2 = |((Algebra.norm ℚ s : ℚ) : ℝ)| ^ 2 := by
    rw [Finset.prod_pow, ← norm_prod]
    convert congrArg (fun z : ℂ => ‖z‖ ^ 2) hN.symm using 2
    simp
  rw [h1, Real.log_pow]
  push_cast; ring

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
