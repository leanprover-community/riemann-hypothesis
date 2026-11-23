module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NotMidCases
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory

namespace WlocSk

open HM

theorem uw_finite {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) : IsFiniteMeasure (hmeas (Formalism.QuantumDeterminants.UWset k r z) (uw_clsub z)) := by
  have : CompactSpace (Grp (Formalism.QuantumDeterminants.UWset k r z : Set (Mx k r)) (uw_clsub z)) :=
    isCompact_iff_compactSpace.mp (compactW z hz hT)
  refine ⟨?_⟩
  unfold hmeas
  rw [Measure.map_apply (val_cemb _ _).continuous.measurable MeasurableSet.univ, Set.preimage_univ]
  exact isCompact_univ.measure_lt_top

theorem haar_measure_unipotent_nilradical : HaarWN := by
  intro k r z hz hT
  exact ⟨hmeas (Formalism.QuantumDeterminants.UWset k r z) (uw_clsub z), haarNm k r, hmeas_haar _ _, haarNm_haar,
    uw_finite z hz hT, haarNm_compact⟩

end WlocSk
