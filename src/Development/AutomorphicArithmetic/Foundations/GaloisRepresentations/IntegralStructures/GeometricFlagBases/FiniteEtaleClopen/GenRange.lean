module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

theorem UpperTheory.Gal.Int.Geo.Cut.genRange :
    UpperTheory.Gal.Int.Geo.Cut.GenRange := by
  intro O k _ _ _ _ _ Y p
  haveI : IsPreimmersion (gen O k) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have hker : RingHom.ker (algebraMap O k) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O k)
  refine ⟨?_, (pullback.fst p (gen O k)).isEmbedding⟩
  rw [Scheme.Pullback.range_fst]
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz⟩
    rw [← hz]
    change Ideal.comap (algebraMap O k) (z : PrimeSpectrum k).asIdeal = ⊥
    haveI : (z : PrimeSpectrum k).asIdeal.IsPrime := (z : PrimeSpectrum k).isPrime
    rw [Ideal.eq_bot_of_prime (z : PrimeSpectrum k).asIdeal, ← RingHom.ker_eq_comap_bot, hker]
  · intro h
    refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap O k) ⊥ = (p y).asIdeal
    rw [h, ← RingHom.ker_eq_comap_bot, hker]
