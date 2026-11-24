module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionGenericFiberPullbackLocalIso
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ), (∀ x, IsIso (j.stalkMap x)) → ∀ (M : MLine p (τ.comp (algebraMap k K))) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), j (genericPoint G) = genericPoint X → ∃ (s' : (M.bc hp.w τ).B.Sec) (hs' : genericPoint G ∈ nonzeroLocus s'), nonzeroLocus s' = j ⁻¹ᵁ nonzeroLocus s ∧ (∀ x, (divOfSec (M.bc hp.w τ).φ.isLB s' hs').mult x = (divOfSec M.φ.isLB s hs).mult (j x)) ∧ ∀ y, (M.bc hp.w τ).logSec s' y = M.logSec s (bcPt hp.w τ y) := by
  first | exact @GlobalTheory.Mix.exists_sec_bc | exact GlobalTheory.Mix.exists_sec_bc | (intros; apply GlobalTheory.Mix.exists_sec_bc <;> assumption)
