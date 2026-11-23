module

public import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianFormPeriodMatrixNormalForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl


theorem _root_.GlobalTheory.T.hermitian_form_period_matrix_normal_form : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (v : Fin g ⊕ Fin g → Fin g → ℂ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ α β, (hermForm Hm (v α) (v β)).im = Matrix.J (Fin g) ℝ α β) →
    ∃ (h : Matrix (Fin g) (Fin g) ℂ) (X Y : Matrix (Fin g) (Fin g) ℝ),
      IsUnit h.det ∧ X.IsSymm ∧ Y.PosDef ∧
      (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) ∧
      (∀ i, h.mulVec (v (Sum.inl i)) = Pi.single i 1) ∧
      (∀ i, h.mulVec (v (Sum.inr i)) = (periodMatrix X Y).mulVec (Pi.single i 1)) ∧
      (Matrix.of fun α β => (hermForm Hm (v α) (v β)).re) = siegelGram X Y := by
  first | exact @GlobalTheory.CompanionTheory.NForm.normal_form_gram | exact GlobalTheory.CompanionTheory.NForm.normal_form_gram | (intros; apply GlobalTheory.CompanionTheory.NForm.normal_form_gram <;> assumption)
