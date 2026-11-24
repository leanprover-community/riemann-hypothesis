module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
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
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

theorem exists_finset_isIntB_one_tmul (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type)
    (b : Module.Basis κ ℚ M) (x : M) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] x) := by
  have hfin : (⋃ i ∈ ((b.repr x).support : Set κ), HeightOneSpectrum.Support ℤ (b.repr x i)).Finite :=
    (b.repr x).support.finite_toSet.biUnion fun i _ => HeightOneSpectrum.Support.finite ℤ (b.repr x i)
  refine ⟨hfin.toFinset, fun v hv i => ?_⟩
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  by_cases hi : b.repr x i = 0
  · rw [hi, map_zero]; exact zero_mem _
  · have h1 : v ∉ HeightOneSpectrum.Support ℤ (b.repr x i) := fun h =>
      hv (hfin.mem_toFinset.2 (Set.mem_biUnion (Finsupp.mem_support_iff.2 hi) h))
    have h2 : v.valuation ℚ (b.repr x i) ≤ 1 := not_lt.1 h1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h3 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (b.repr x i)
    rw [← h3] at h2
    convert h2 using 2
    rfl

end GlobalTheory.AdicSpan
