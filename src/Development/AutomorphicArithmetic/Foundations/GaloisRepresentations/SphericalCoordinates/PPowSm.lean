module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBundleQuotientEquivalence
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothOfRelativeDimensionFibrePower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.powSm_of :
    UpperTheory.Gal.W2.PowSm := by
  intro X s d g hs hqc hsep A _ _ hA hg k
  have hP : IsProper (KS.pow A k).hom := KS.Leray.isProper_pow_hom A hA.proper k
  have hsm := FibPow.smoothOfRelativeDimension_fibrePower ℂ X s d g hs A hA hg k
  refine ⟨hsm, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · haveI : Smooth ((KS.pow A k).hom ≫ s) := hsm.smooth
    infer_instance
