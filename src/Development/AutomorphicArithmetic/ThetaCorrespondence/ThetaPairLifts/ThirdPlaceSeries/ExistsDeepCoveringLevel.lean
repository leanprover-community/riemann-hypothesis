module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCoverOverSizedFieldStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff

@[expose] public section



section
section

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.DeepExist
theorem exists_deep_covering_level_alt (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : _root_.GlobalTheory.CovTop.DeepExistence := by
  refine Closed.imp (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0) fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, h⟩ := h
  refine ⟨C, hC, x0, fun x hx hle ι p hp i hi => ?_⟩
  have hN := h x hx hle ι p hp i
  obtain ⟨Y, hY⟩ := GlobalTheory.T.exists_good_cover_over_sized_field hP.p8 (Fm.D x ι) p.T.toCore p.fw.laws.pins ((i : ℕ) + 1) ⟨by omega, i.isLt⟩ hN.split
    hN.cop (expL (Fm.L x ι).sc.L)
  refine ⟨Y, (goodCov_iff p i Y).2 (hY.mono (size_le hN ?_))⟩
  exact RecTied.core_size_le p hp.2 (by linarith [hN.big.2.1])
end GlobalTheory.CovTop.DeepExist
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.covering_deepEx_of_prints : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepExistence := by
  exact @_root_.GlobalTheory.CovTop.DeepExist.exists_deep_covering_level_alt
end
end
