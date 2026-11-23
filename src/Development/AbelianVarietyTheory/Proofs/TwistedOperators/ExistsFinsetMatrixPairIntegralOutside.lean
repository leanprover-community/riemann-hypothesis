module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory

theorem matrixPair_integral_cofinite (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (M N : Matrix κ κ (Af F)) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ∀ i j,
      evalV F v (M i j) ∈ v.adicCompletionIntegers F ∧
      evalV F v (N i j) ∈ v.adicCompletionIntegers F := by
  have hM : ∀ᶠ v in Filter.cofinite, ∀ p : κ × κ,
      (M p.1 p.2).1 v ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun p => (M p.1 p.2).2
  have hN : ∀ᶠ v in Filter.cofinite, ∀ p : κ × κ,
      (N p.1 p.2).1 v ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun p => (N p.1 p.2).2
  have h := hM.and hN
  rw [Filter.eventually_cofinite] at h
  refine ⟨h.toFinset, fun v hv i j => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
  exact ⟨hv.1 (i, j), hv.2 (i, j)⟩

end GlobalTheory
