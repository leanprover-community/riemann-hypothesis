module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FubiniRightConvolutionBoundedContinuous
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.integral_fundamentalDomain_convolution_comm_of_bounded : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (μ : Measure G) (𝓕 : Set G), μ 𝓕 < ⊤ → ∀ (m : Measure H) [SFinite m] (α : H → ℂ), Integrable α m → ∀ (ψ φ : G → ℂ), Continuous ψ → Continuous φ → ∀ (A B : ℝ), (∀ g, ‖ψ g‖ ≤ A) → (∀ g, ‖φ g‖ ≤ B) → IntegrableOn (fun x => ψ x * ∫ h, α h * φ (x * (h : G)) ∂m) 𝓕 μ ∧ Integrable (fun h : H => α h * ∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) m ∧ ∫ x in 𝓕, ψ x * (∫ h, α h * φ (x * (h : G)) ∂m) ∂μ = ∫ h, α h * (∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) ∂m := by
  first | exact @GlobalTheory.fubini_right_convolution_bounded_continuous | exact GlobalTheory.fubini_right_convolution_bounded_continuous | (intros; apply GlobalTheory.fubini_right_convolution_bounded_continuous <;> assumption)
