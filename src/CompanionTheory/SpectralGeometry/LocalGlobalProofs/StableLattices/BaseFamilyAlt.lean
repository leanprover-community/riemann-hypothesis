module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentLeftRuleStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentRightRuleStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.CompanionTheory.BaseFamily

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J ReciprocityTheory.ChartRestriction.DS

theorem baseFam : CompanionTheory.RgExh.Dec.J.BaseFam := by
  intro n ε H _ _ _ σ D E hK hσ
  refine ⟨fun ξ u Y hY g hg => ?_, fun ξ => ?_⟩
  · have h := GlobalTheory.T.NilpotentRightRule n ε H σ D E hK 0 [] hσ ((ξ, []) : D × List (Fin n)) u Y hY g hg
    have e : actM E Y u = ∑ a, ∑ b, Y a b • E a b u := by
      simp [actM, LinearMap.sum_apply]
    show HasDerivAt _ (baseCoef σ D (ξ : H) (actM E Y u) g) 0
    rw [e]
    exact h
  · obtain ⟨l, hl⟩ := GlobalTheory.T.NilpotentLeftRule n ε H σ D E hK 0 [] hσ ((ξ, []) : D × List (Fin n))
    refine ⟨fun c d => (l c d).mapDomain Prod.fst, fun a b u g hg => ?_⟩
    have h := hl a b u g hg
    refine h.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_)
    congr 1
    rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
    rfl

end GlobalTheory.CompanionTheory.BaseFamily
