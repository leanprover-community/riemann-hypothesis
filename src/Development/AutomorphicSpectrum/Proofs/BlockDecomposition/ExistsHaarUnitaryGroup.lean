module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.ModelS

theorem exists_rightInvariant_measure_unitaryGroup
    (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] :
    ∃ κ : Measure (Matrix.unitaryGroup (Fin n) ℂ),
      IsFiniteMeasure κ ∧ κ.IsMulRightInvariant ∧ κ.IsOpenPosMeasure := by
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
    GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  let μ : Measure (Matrix.unitaryGroup (Fin n) ℂ) := Measure.haarMeasure ⊤
  refine ⟨μ.inv, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.CompanionTheory.ModelS
