module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.BeConjOfNorm
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BeConjNorm
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LevelRestrictionOfGroupLawHolds
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.MainNotions.Ext.CutA

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

theorem l0 {p : ℕ} [Fact p.Prime] (g : G1 p) : PowerSeries.constantCoeff g.l = 0 := by
  first
    | (unfold Formalism.MainNotions.GL3Theta.G1.l flog; simp)
    | (simp [Formalism.MainNotions.GL3Theta.G1.l, flog, PowerSeries.coeff_mk])
    | (show PowerSeries.coeff 0 (flog _ _) = 0; simp [flog])

theorem beConjOfNorm_holds : BeConjOfNorm := by
  intro p _ g S hOk hsw hadd hint hF hN hdec hph hbi
  exact conjugate_norm_bound p g.l g.ex g.ph (l0 g) hOk.2.2.1 hOk.2.2.2 (ph0 g) S hsw hadd hint hF hN hdec hph hbi

end Formalism.MainNotions.Ext.CutA
