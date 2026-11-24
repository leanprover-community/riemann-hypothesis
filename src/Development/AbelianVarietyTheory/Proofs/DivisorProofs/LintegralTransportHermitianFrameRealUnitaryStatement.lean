module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralTransportHermitianFrameRealUnitary
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_transportHermitianFrame_realUnitary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ), X.p0 = X'.p0 → ∀ (φ : Frame X'.Ψ r → ℝ≥0∞), Measurable φ → ∫⁻ g, φ (trF X X' e (frameOf X g)) ∂haarR X = ∫⁻ g, φ (frameOf X' g) ∂haarR X' := by
  first | exact @GlobalTheory.FlagQuotHaar.lintegral_trF_frameOf | exact GlobalTheory.FlagQuotHaar.lintegral_trF_frameOf | (intros; apply GlobalTheory.FlagQuotHaar.lintegral_trF_frameOf <;> assumption)
