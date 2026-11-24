module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedWhittakerIntegralEqVolumeMulIntegralPer
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

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.truncatedWhittakerIntegral_eq_volume_mul_integral_perp : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ (a : A.K) (c : F), c ≠ 0 → ∫ z in {z : A.K | c • z ∈ A.OK}, (∫ t, (∫ b, φ' (b, t) * A.psiK ψ (t * z * b) ∂μK) * A.etaK t ∂μK) * A.psiK ψ (-(a * z)) ∂μK = (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * ∫ t, (∫ b, φ' (b, t) * Set.indicator {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK := by
  first | exact @GlobalTheory.WhitCollapse.collapse | exact GlobalTheory.WhitCollapse.collapse | (intros; apply GlobalTheory.WhitCollapse.collapse <;> assumption)
