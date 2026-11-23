module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ

@[expose] public section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve (scheme toSpec chartZ)
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjHol

theorem valuationRing_stalk {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp K)
    [hf : SmoothOfRelativeDimension 1 f] (x : X) : ValuationRing (X.presheaf.stalk x) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : GlobalTheory.IsNormalScheme X := GlobalTheory.isNormalScheme_of_smooth f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have h : Order.coheight x ≤ 1 := by simpa using GlobalTheory.AffineCover.coheight_le_of_smooth f hf x
  rcases h.eq_or_lt with h | h
  · have := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk h
    infer_instance
  · have h0 : Order.coheight x = 0 := by simpa using h
    have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le h0.le
    letI := (Ring.KrullDimLE.isField_of_isDomain (R := X.presheaf.stalk x)).toField
    exact ValuationRing.of_field _

end GlobalTheory.ProjHol
