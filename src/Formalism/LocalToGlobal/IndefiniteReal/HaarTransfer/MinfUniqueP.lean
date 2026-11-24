module

public import Formalism.LocalRingCardinality.DataCD
public import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.IndefR.Leaf.Proofs
open Formalism.IndefR.Leaf MeasureTheory Formalism.BasicNotions

theorem exists_haar_measure_with_density (p q : ℕ) (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    ∃ m : Measure (UpqT p q), m.IsHaarMeasure ∧ OmegaDensity m c := by
  obtain ⟨c', hc'0, hc't, hd⟩ :=
    Formalism.BasicNotions.Examples₂.CD.omegaDensity_haar p q (MeasureTheory.Measure.haar : Measure (UpqT p q))
  refine ⟨(c / c') • MeasureTheory.Measure.haar, ?_, ?_⟩
  · exact MeasureTheory.Measure.IsHaarMeasure.smul _ (ENNReal.div_pos_iff.mpr ⟨hc0, hc't⟩).ne'
      (ENNReal.div_lt_top hct hc'0).ne
  · have h := Formalism.BasicNotions.Examples₂.CD.omegaDensity_smul p q hd (c / c') (ENNReal.div_lt_top hct hc'0).ne
    rwa [ENNReal.div_mul_cancel hc'0 hc't] at h

end Formalism.IndefR.Leaf.Proofs
