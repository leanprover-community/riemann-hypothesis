module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricToFS
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFSExtension
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDefectMetricChange
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem MetricToFS.proof (hE : PullFSExtension.Statement) (hC : DefectMetricChange.Statement) :
    MetricToFS.Statement := by
  intro D Ω _ _ κ _ I d e hI hF
  obtain ⟨m₀, hs, hc, hp, hpull⟩ := hE D Ω κ d.x e hF
  exact ⟨d.withMetric m₀ ⊥ hs hc bot_le hp, rfl, hpull,
    hC D Ω κ I d m₀ ⊥ hs hc bot_le hp e hI hF⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
