module

public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AutomorphicArithmetic.CMTraceForms.CmDatumDiscriminantDepthBounds
public import Development.AutomorphicArithmetic.CMTraceForms.SplitPlacesDiscriminantDepthOfSplitAt
public import Formalism.LocalRingCardinality.HostCls
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.CharDepth

theorem twoPlaces_host : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E), H.d = D.host.d → ∀ (p : ℕ) [Fact p.Prime], p ∈ D.host.small → UpperTheory.Depth.SplitAt H.d p ∧ UpperTheory.Depth.SplitPlaces p H D.R.f (D.host.vdH p) ∧ 0 ≤ D.host.vdH p ∧ D.host.vdH p ≤ vd2 D := by
  intro D H hd p _ hp
  have hpp : p.Prime := Fact.out
  have hs : UpperTheory.Depth.SplitAt H.d p := by
    by_cases h2 : p = 2
    · exact Or.inl h2
    · exact Or.inr (by rw [hd]; exact D.host.QS_split p hpp h2 (D.host.mem_small_iff.1 hp).2)
  obtain ⟨h1, -, -, -, h5⟩ := UpperTheory.cmDatum_discriminantDepth_bounds D.host.toHostAx
  refine ⟨hs, ?_, D.host.vdH_nonneg p, (h1 p hp).1.trans (h1 p hp).2⟩
  rw [h5 p]
  exact UpperTheory.splitPlaces_discriminantDepth_of_splitAt p D.host.E H hs D.R.f D.host.finrank_E'

end GlobalTheory.CharDepth
