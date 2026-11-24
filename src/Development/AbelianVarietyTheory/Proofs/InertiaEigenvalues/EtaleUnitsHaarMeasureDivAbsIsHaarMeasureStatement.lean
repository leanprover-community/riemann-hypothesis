module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleUnitsHaarMeasureDivAbsIsHaarMeasure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.etaleUnitsHaarMeasureDivAbs_isHaarMeasure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → BorelSpace A.Kˣ ∧ (LinDesc.unitsMeas A μK).IsHaarMeasure ∧ ∀ h : A.K → ℂ, ∫ s, h (s : A.K) ∂(LinDesc.unitsMeas A μK) = ∫ t in {t : A.K | IsUnit t}, h t * ((A.absK t : ℂ))⁻¹ ∂μK := by
  first | exact @GlobalTheory.JR.LinDesc.unitsMeas_isHaar | exact GlobalTheory.JR.LinDesc.unitsMeas_isHaar | (intros; apply GlobalTheory.JR.LinDesc.unitsMeas_isHaar <;> assumption)
