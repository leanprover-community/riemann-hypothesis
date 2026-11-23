module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtension
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUnique
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

namespace GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
  (mseg joinCoord IsPull SameGeneric)

theorem main :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
      [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (z : (Σ k, ι' k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
      (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' →
      ∃ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V,
        IsPull O x z E EB ∧ IsPull O x z E' E'B ∧ SameGeneric O (joinCoord x z) EB E'B := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z N V _ _ E E' hE
  obtain ⟨EB, hEB⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V E).1 K' ι' z
  obtain ⟨E'B, hE'B⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V E').1 K' ι' z
  exact ⟨EB, E'B, hEB, hE'B,
    (GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve O Ω K ι x N V E E' K' ι' z EB E'B hEB hE'B).2.1 hE⟩

end GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt
