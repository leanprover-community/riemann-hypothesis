module

public import GroundTheory.FunctionField.PlaceDefs
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PlenPlaces
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.CompanionTheory.Relay.length_formula_sum_valuations : ∀ (k K A : Type) [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K] [CommRing A] [IsDomain A] [Algebra k A] [Algebra A K] [IsScalarTower k A K] [IsLocalRing A] [IsNoetherianRing A] [IsFractionRing A K] [Algebra.EssFiniteType k A], ¬ IsField A → ∀ f : A, f ≠ 0 → (((Module.length A (A ⧸ Ideal.span {f})).toNat * Module.finrank k (IsLocalRing.ResidueField A) : ℕ) : ℤ) = ∑ᶠ v ∈ {v : GroundTheory.FunctionField.Place k K | (∀ a : A, v.valuation (algebraMap A K a) ≤ 1) ∧ ∀ a ∈ IsLocalRing.maximalIdeal A, v.valuation (algebraMap A K a) < 1}, (v.deg : ℤ) * v.ord (algebraMap A K f) := by
  first | exact @PositivityTheory.HtPt.Plen.len_places | exact PositivityTheory.HtPt.Plen.len_places
