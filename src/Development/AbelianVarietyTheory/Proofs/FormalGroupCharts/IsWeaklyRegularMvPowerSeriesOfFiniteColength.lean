module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Field
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isWeaklyRegular_mvPowerSeries_of_pow_le :
    ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ)
      (f : σ → MvPowerSeries σ k), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) →
      (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤
        Ideal.span (Set.range f)) →
      RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries σ k) (List.ofFn fun i => f (e i)) := by
  rintro k _ σ _ n e f h0 ⟨M, hM⟩
  have := FormalIsogeny.isRegularLocalRing_mvPowerSeries k σ
  refine (isRegular_of_radical_eq_maximalIdeal ?_ ?_).1
  · have h1 : Ideal.ofList (List.ofFn fun i => f (e i)) = Ideal.span (Set.range f) := by
      rw [ofList_ofFn_eq_span_range]
      exact congrArg Ideal.span (e.surjective.range_comp f)
    rw [h1]
    refine le_antisymm ((maximalIdeal.isMaximal _).isPrime.radical_le_iff.2 ?_) fun g hg => ?_
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp [h0])
    · have h2 : MvPowerSeries.constantCoeff g = 0 := by
        simpa [maximalIdeal_eq_bot] using FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
      have h3 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) := by
        rw [← germIdeal_eq_span]
        exact h2
      exact ⟨M, hM (Ideal.pow_mem_pow h3 M)⟩
  · rw [FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_field, zero_add,
      List.length_ofFn, ← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

end GlobalTheory
