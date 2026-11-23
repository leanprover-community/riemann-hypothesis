module

public import Formalism.LatticeTheta.LatticeSummableDecay
public import Mathlib.Algebra.Module.ZLattice.Summable
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Filter Asymptotics Topology

noncomputable section

namespace Formalism.H

theorem lattice_summable_decay (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : LatticeSummableDecay V := by
  intro L _ _ g b hb hg
  obtain ⟨C, hC⟩ := hg.bound
  have hrank : Module.finrank ℤ L = Module.finrank ℝ V := ZLattice.rank ℝ L
  have hsum : Summable fun z : L => ‖z‖ ^ (-b) :=
    ZLattice.summable_norm_rpow L (-b) (by rw [hrank]; linarith)
  have ht : Tendsto (Subtype.val : L → V) cofinite (cocompact V) :=
    L.toAddSubgroup.tendsto_coe_cofinite_of_isDiscrete
      (isDiscrete_iff_discreteTopology.mpr inferInstance)
  refine Summable.of_norm_bounded_eventually (hsum.mul_left C) ?_
  filter_upwards [ht.eventually hC] with z hz
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at hz
  exact hz

end Formalism.H
