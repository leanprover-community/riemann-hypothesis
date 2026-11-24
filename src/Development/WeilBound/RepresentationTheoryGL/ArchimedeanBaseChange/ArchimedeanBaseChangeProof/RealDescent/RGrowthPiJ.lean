module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotIntegralZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.CutTrDZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F
open scoped Classical

namespace PositivityTheory.Rg.BcB.Desc

attribute [local instance] borelH

def GrowthPiJ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (n : ℕ), 1 ≤ n →
  ∀ [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] [MeasurableSpace (GA E 0)] [BorelSpace (GA E 0)]
  (μ₁ : Measure (GA E n)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E 0)) [μ₂.IsHaarMeasure],
  ∃ D : Dom E n 0, (∀ F : H E n 0 → ℂ, Continuous F → HasCompactSupport F → ∫ x, F x ∂D.μ = ∫ x₁, ∫ x₂, F (x₁, x₂) ∂μ₂ ∂μ₁) ∧
    ∀ π : CuspSub E n, ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E n 0 → ℂ))
    (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (r₀ r₁ ε : ℝ), IsTestM Φ₁ → IsTestM Φ₂ →
    (∀ i j, FinOn D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ → 0 ≤ r₀ → 0 ≤ r₁ → 0 < ε → ∃ (C : ℝ) (N : ℕ), ∀ (k : ℕ)
      (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E n 0 → ℂ)) (t : ℂ), IsTestM Φ → IsROp D Φ (T₁ * U * T₂) →
      (∀ f ∈ piSp D π ι, U f ∈ piSp D π ι) → (∀ f ∈ (piSp D π ι)ᗮ, U f ∈ (piSp D π ι)ᗮ) →
      D4.IsTest2J (trM Φ M) (r₀ + k * r₁) → IsTwTr D.μ π (trM Φ M) t →
      ‖ellSum2 μ₁ μ₂ (trM Φ M) - t / 2‖ ≤ C * (1 + k) ^ N * ‖U ∘L (piSp D π ι)ᗮ.subtypeL‖ + C * ‖U‖ * ε ^ k

def RGrowthPiJ : Prop := D4.EllFormula2J → PositivityTheory.Rg.BcB.E1.SFun → PiVecEx → PiInv → GrowthPiJ

end PositivityTheory.Rg.BcB.Desc

end
