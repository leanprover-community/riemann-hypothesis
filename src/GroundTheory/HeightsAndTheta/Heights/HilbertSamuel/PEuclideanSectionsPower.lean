module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSectionsPower
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsBisAlt
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

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

theorem EuclideanSectionsPower.proof (hL : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement) :
    EuclideanSectionsPower.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD hII har hb hA hc
  obtain ⟨μ, m, hμ, hcon, hZ, hm, hdeg⟩ := hP K ι Ω y D A P0 II hD hII har hb hA hc
  obtain ⟨r, φ, hinj, hdisc, hlat, hsup, hmul, hrank, hnorm⟩ :=
    hL K ι Ω y D A har hb hA.semipos.1.continuousOn μ hμ hcon hZ
  refine ⟨r, φ, hinj, hdisc, hlat, hsup, hmul, hrank, m, hm, fun ε hε => ?_⟩
  filter_upwards [hdeg ε hε] with q hq
  intro _ _
  exact hq (r (m * q)) (φ (m * q)) (hinj _) (hnorm _)

end GroundTheory.Heights₂.Heights.HilbertSamuel
