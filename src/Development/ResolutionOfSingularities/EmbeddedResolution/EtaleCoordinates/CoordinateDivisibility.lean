module

public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinatePolynomialRing
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.RegularLocalRing
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorRadical
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

@[expose] public section

universe u

namespace FunctorialResolution.EmbeddedResolution

theorem isPrime_span_singleton_algebraMap_etaleChartCoord (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (j : Fin m)
    (hj : etaleChartCoord k m S j ∈ q) :
    (Ideal.span ({algebraMap S A (etaleChartCoord k m S j)} : Set A)).IsPrime := by
  have : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hJ : ∀ i ∈ ({j} : Finset (Fin m)), etaleChartCoord k m S i ∈ q := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact hj
  have hJA : ∀ i ∈ ({j} : Finset (Fin m)),
      algebraMap S A (etaleChartCoord k m S i) ∈ IsLocalRing.maximalIdeal A := by
    intro i hi
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q _).mpr (hJ i hi)
  have hli := linearIndependent_toCotangent_etaleChartCoord k m S q A {j} hJ hJA
  exact IsRegularLocalRing.isPrime_span_singleton
    (fun i : { x : Fin m // x ∈ ({j} : Finset (Fin m)) } =>
      algebraMap S A (etaleChartCoord k m S (i : Fin m)))
    (fun i => hJA (i : Fin m) i.2) hli ⟨j, Finset.mem_singleton_self j⟩

end FunctorialResolution.EmbeddedResolution
