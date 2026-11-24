module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformSymplecticImaginary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem _root_.GlobalTheory.T.siegel_transform_symplectic_imaginary : ∀ {I : Type} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ), Zᵀ = Z → (1 - Zᴴ * Z).PosDef → ∀ z w : I → ℂ, (tz Z z ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z w)).im = (z ⬝ᵥ star w).im := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' <;> assumption)
