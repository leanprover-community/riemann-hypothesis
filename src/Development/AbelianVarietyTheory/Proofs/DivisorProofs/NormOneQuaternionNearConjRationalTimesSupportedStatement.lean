module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneQuaternionNearConjRationalTimesSupported
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.normOneQuaternion_near_conj_rational_times_supported : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → ε • (g - 1) = 0 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ w ∈ W, ∃ y : DA F a b, IsUnit (nrm y) ∧ ∃ γ : ℍ[F, a, b], nrm γ = 1 ∧ ∃ h : DA F a b, nrm h = 1 ∧ ε • (h - 1) = h - 1 ∧ y * w = rat γ * y * h := by
  first | exact @GlobalTheory.QSAStep.key_step | exact GlobalTheory.QSAStep.key_step | (intros; apply GlobalTheory.QSAStep.key_step <;> assumption)
