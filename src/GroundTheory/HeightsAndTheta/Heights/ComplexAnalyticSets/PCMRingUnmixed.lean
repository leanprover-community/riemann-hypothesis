module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMRingUnmixed
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CMDepthAssoc
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.HeightCoheightQuotient
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence

theorem CMRingUnmixed.proof : CMRingUnmixed.Statement := by
  intro A _ _ p hp
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := A)
  obtain ⟨hprime, y, hy⟩ := isAssociatedPrime_iff.mp hp
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs y hy0 hm hreg
  rw [← hy, ← hdim] at hD
  have heq : ringKrullDim (A ⧸ p) = ringKrullDim A :=
    le_antisymm (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective) hD
  refine ⟨⟨⟨hprime, bot_le⟩, fun q hq hqp => ?_⟩, heq⟩
  by_contra hpq
  have hlt : q < p := lt_of_le_of_ne hqp fun h => hpq (h ▸ le_rfl)
  have hq' : q.IsPrime := hq.1
  have h1 := Order.coheight_add_one_le (α := PrimeSpectrum A) (a := ⟨p, hprime⟩) (b := ⟨q, hq'⟩) hlt
  have h2 : ringKrullDim (A ⧸ q) ≤ ringKrullDim A :=
    ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  rw [ringKrullDim_quotient_eq_coheight, hdim] at h2
  rw [ringKrullDim_quotient_eq_coheight, hdim] at heq
  have e1 : Order.coheight (⟨p, hprime⟩ : PrimeSpectrum A) = (rs.length : ℕ∞) := by exact_mod_cast heq
  have e2 : Order.coheight (⟨q, hq'⟩ : PrimeSpectrum A) ≤ (rs.length : ℕ∞) := by exact_mod_cast h2
  rw [e1] at h1
  have h3 : ((rs.length + 1 : ℕ) : ℕ∞) ≤ (rs.length : ℕ) := by exact_mod_cast h1.trans e2
  have h4 : rs.length + 1 ≤ rs.length := by exact_mod_cast h3
  omega

end GroundTheory.Heights₂.Heights
