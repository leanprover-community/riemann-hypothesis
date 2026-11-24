module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentComplexOfRealHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.linearIndependent_complex_of_real_hermitian : ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℝ u → (∀ i j, (u i ⬝ᵥ Hm *ᵥ star (u j)).im = 0) → LinearIndependent ℂ u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RealFormIndep.linearIndependent_complex_of_real_form | exact GlobalTheory.CompanionTheory.Ar.RealFormIndep.linearIndependent_complex_of_real_form | (intros; apply GlobalTheory.CompanionTheory.Ar.RealFormIndep.linearIndependent_complex_of_real_form <;> assumption)
