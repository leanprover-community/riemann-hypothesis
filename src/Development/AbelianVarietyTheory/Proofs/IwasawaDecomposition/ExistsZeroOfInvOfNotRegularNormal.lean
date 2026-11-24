module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.NormalPole

theorem exists_height_one {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (f : K) (Q : Ideal R)
    (hQ : ∀ s c : R, algebraMap R K s * f = algebraMap R K c → s ∈ Q) [Q.IsPrime] :
    ∃ p : Ideal R, p.IsPrime ∧ p ≤ Q ∧ p.height = 1 ∧
      ∀ s c : R, algebraMap R K s * f = algebraMap R K c → s ∈ p := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : algebraMap R K c ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hc0
  let d : Ideal R := (Ideal.span {c}).colon {b}
  have hd : ∀ s, s ∈ d ↔ c ∣ s * b := fun s => by
    simp only [d, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton]
  have reg : ∀ s, (∃ e : R, algebraMap R K s * (algebraMap R K b / algebraMap R K c) =
      algebraMap R K e) ↔ s ∈ d := fun s => by
    rw [hd]
    refine exists_congr fun e => ?_
    rw [← mul_div_assoc, div_eq_iff hcK, ← map_mul, ← map_mul, (IsFractionRing.injective R _).eq_iff,
      mul_comm e]
  have hdQ : d ≤ Q := fun s hs => by
    obtain ⟨e, he⟩ := (reg s).2 hs
    exact hQ s e he
  obtain ⟨p, hp, hpQ⟩ := Ideal.exists_minimalPrimes_le hdQ
  have hpa : p ∈ associatedPrimes R (R ⧸ d) := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    rw [Ideal.annihilator_quotient]
    exact hp
  obtain ⟨hpp, x, hx⟩ := isAssociatedPrime_iff.mp hpa
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : p.height = 1 := height_eq_one_of_forall_mem_iff_dvd (b := x * b) hc0 fun r => by
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hd, _root_.mul_assoc]
  exact ⟨p, hpp, hpQ, h1, fun s e he => hp.1.2 ((reg s).1 ⟨e, he⟩)⟩

theorem mem_range_iff {R B K : Type} [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra R K]
    [Algebra B K] [IsScalarTower R B K] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime B p] (f : K) :
    (∃ a : B, algebraMap B K a = f) ↔
      ∃ s c : R, algebraMap R K s * f = algebraMap R K c ∧ s ∉ p := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj p.primeCompl a
    refine ⟨s, c, ?_, s.2⟩
    rw [IsScalarTower.algebraMap_apply R B K, IsScalarTower.algebraMap_apply R B K c, ← map_mul,
      mul_comm, e]
  · rintro ⟨s, c, e, hs⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units B (⟨s, hs⟩ : p.primeCompl)
    refine ⟨↑u⁻¹ * algebraMap R B c, ?_⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← e, IsScalarTower.algebraMap_apply R B K s]
    have hu' : algebraMap R B s = u := hu.symm
    rw [hu', ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]

end GlobalTheory.NormalPole
