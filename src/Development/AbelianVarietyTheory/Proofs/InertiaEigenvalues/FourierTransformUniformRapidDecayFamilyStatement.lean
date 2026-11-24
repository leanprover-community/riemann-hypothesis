module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformUniformRapidDecayFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

theorem _root_.GlobalTheory.T.fourierTransform_uniformRapidDecay_family : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (ι : Type) (w : ι → ℝ) (𝒞 : Set (ι → (Fin n → Cinf E) → ℂ)), (∀ f ∈ 𝒞, (∀ i, ContDiff ℝ ∞ (f i) ∧ HasCompactSupport (f i)) ∧ ∃ C : ℝ, ∀ i, ∫ y, ‖f i y‖ ∂(infMeasure E n) ≤ C * w i) → (∀ f ∈ 𝒞, ∀ v : Fin n → Cinf E, (fun i y => fderiv ℝ (f i) y v) ∈ 𝒞) → ∀ M : ℕ, ∀ f ∈ 𝒞, ∃ C : ℝ, ∀ i u, ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M ≤ C * w i := by
  first | exact @GlobalTheory.fourier_decay_family | exact GlobalTheory.fourier_decay_family | (intros; apply GlobalTheory.fourier_decay_family <;> assumption)
