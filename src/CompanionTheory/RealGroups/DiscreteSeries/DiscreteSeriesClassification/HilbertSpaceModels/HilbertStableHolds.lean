module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.StepFormulaF
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight

@[expose] public section

noncomputable section

namespace CompanionTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

theorem hilbert_stable_holds : StepStable := by
  intro n ε lam T Ψ hP
  have hv₀ : T.w ≠ 0 := HW.KType.w_ne_zero T
  have hσ := rreg_isURepOn ε
  have hV := datumV_isKIrrHW hP hv₀
  exact closure_genSub_stable hσ (isDerivedOn_smE hσ) hV.1 hV.2.1 (datumV_casimir hP T.w)

theorem hilbert_datum_holds : StepDatum := by
  intro n ε lam T Ψ hP
  have hv₀ : T.w ≠ 0 := HW.KType.w_ne_zero T
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV := datumV_isKIrrHW hP hv₀
  exact isKTypeOf_of_isKIrrHW hσ hD hV (datumV_kStable hP T.w) (fun μ x hx hx0 hμ =>
    weights_le_of_irr_hw hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hx hx0 hμ)

end CompanionTheory.RgDs.Hilb
