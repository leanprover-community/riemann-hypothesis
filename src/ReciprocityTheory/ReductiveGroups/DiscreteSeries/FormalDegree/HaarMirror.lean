module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarHaar

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem cPQ_pos (ε : Fin n → Bool) : 0 < cPQ ε := by
  unfold cPQ
  positivity

theorem real_UJ_eq_UJ (ε : Fin n → Bool) : Formalism.REAL.UJ ε = UJ ε := by
  rfl

theorem comap_muPolarMat_isHaar (ε : Fin n → Bool) :
    ∀ (H : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ), H = UJ ε → ∀ (m : MeasurableSpace H), @BorelSpace H _ m →
      (Measure.comap (β := Fin n → Fin n → ℂ)
        (fun g : H => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
        (muPolarMat ε)).IsHaarMeasure := by
  rintro H rfl
  have h0 : (inferInstance : MeasurableSpace (UJ ε)) = borel (UJ ε) := BorelSpace.measurable_eq
  rintro m hm
  have e : m = _ := hm.measurable_eq.trans h0.symm
  subst e
  exact muPolar_isHaar ε

theorem muCD_isHaar (ε : Fin n → Bool) : (muCD ε).IsHaarMeasure := by
  haveI hH := comap_muPolarMat_isHaar ε (Formalism.REAL.UJ ε) (real_UJ_eq_UJ ε) inferInstance inferInstance
  unfold muCD
  exact MeasureTheory.Measure.IsHaarMeasure.smul _
    (ENNReal.ofReal_pos.mpr (cPQ_pos ε)).ne' ENNReal.ofReal_ne_top

end ReciprocityTheory.ChartRestriction.DS
