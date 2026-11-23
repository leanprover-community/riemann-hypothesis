module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition

@[expose] public section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

theorem maMeasure_thm : MaMeasureStatement := by
  intro e X _ _ _ _ _ A Φ hΦ hPsh
  have hne : Nonempty (ChartPartition A) := existsPartition A
  refine ⟨?_, fun g hg => ⟨⟨fun hgi => (maMeasure_forward A Φ hΦ hPsh hg hgi).1,
    fun hgi => maMeasure_converse A Φ hΦ hPsh hg hgi⟩,
    fun hgi => (maMeasure_forward A Φ hΦ hPsh hg hgi).2⟩⟩

  rw [maMeasure_eq_sum A Φ hne]
  haveI : ∀ j, IsFiniteMeasure (chartMeasure A hne.some Φ j) := fun j =>
    chartMeasure_finite A hne.some Φ hΦ hPsh j
  infer_instance
theorem maMeasureMono : MaMeasureMonoStatement := by
  intro e X _ _ _ A Φ Θ hΦ hΦp hΘ hΘp
  exact maMeasure_mono_of_psh A Φ Θ hΦ hΦp hΘ hΘp

end

end ReciprocityTheory.AnForm.M
