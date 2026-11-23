module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceUnmixedGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMHeightOneGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimDomain
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLocalDimGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCMUnmixed
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem SliceUnmixedGeneral.proof (hA : CMHeightOneGeneral.Statement) (hC : LocalDimDomain.Statement)
    (hB : SliceLocalDimGeneral.Statement) (hD : SliceCMUnmixed.Statement) :
    SliceUnmixedGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  obtain ⟨f, hfW, hf⟩ := hA n J W (linForm u) hJ hu hW
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  have hqJ : q ∈ zeroSet J := fun g hg => hq g (hW.1.2 (Ideal.mem_sup_left hg))
  obtain ⟨O, hOo, hOd, hO⟩ := hB n d J q hJ hdim hqJ
  exact ⟨O, hOo, hOd, fun L hL =>
    hD n d J L q (hf q hq hfq) (hC n (d + 1) J hJ hdim q hqJ) (hO L hL)⟩

end GroundTheory.Heights₂.Heights
