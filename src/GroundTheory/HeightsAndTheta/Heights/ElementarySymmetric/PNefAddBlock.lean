module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
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

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

namespace NefAddBlock

section Reduction

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (p : ℕ) [Fact p.Prime]


theorem map_red {W : Ideal (Geo.MRing ι)} (hW : Geo.IsMultiProjPrime W)
    (hpW : (C (p : ℤ) : Geo.MRing ι) ∈ W) (n : ℕ)
    (hdim : ringKrullDim (Geo.MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    NumbersDVR.IsMultiProjPrime (W.map (Bridge.GeoNum.red p)) ∧
      FieldNumbers.relDim (W.map (Bridge.GeoNum.red p)) = ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have hker : RingHom.ker (Bridge.GeoNum.red (ι := ι) p) ≤ W := by
    rw [Bridge.GeoNum.ker_red, Ideal.span_le, Set.singleton_subset_iff]
    exact hpW
  have hcm : (W.map (Bridge.GeoNum.red p)).comap (Bridge.GeoNum.red p) = W :=
    Bridge.GeoNum.comap_map_eq p hker
  have : W.IsPrime := hW.1
  refine ⟨⟨Ideal.map_isPrime_of_surjective (Bridge.GeoNum.red_surjective p) hker, ?_, ?_⟩, ?_⟩
  · rw [Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, hWS⟩ := hW.2.1
    refine ⟨Bridge.GeoNum.red p '' S, ?_, by rw [hWS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨b, hb⟩ := hS f hf
    exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [← Bridge.GeoNum.isRelevant_comap_iff p, hcm]
    exact hW.2.2
  · rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, ← hdim]
    have := ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p (W.map (Bridge.GeoNum.red p)))
    rw [hcm] at this
    exact this.symm

end Reduction

end NefAddBlock

end GroundTheory.Heights₂.Heights
