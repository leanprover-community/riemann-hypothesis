module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import GroundTheory.AutomorphicForms.ReductionMeasure
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

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

noncomputable section
namespace GlobalTheory.RSPole

def schurDir (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑' l : {l : Fin n → ℕ // Antitone l},
    ENNReal.ofReal (‖GlobalTheory.JSW.schurAt l.1 α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x)))

def eulD {I : Type} (q : I → ℕ) {n : ℕ} (α : I → Fin n → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∏' w, schurDir (q w) (α w) x

def thetaZ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (μ : Measure (GA E a)) (𝓕 : Set (GA E a))
    (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (x : ℝ) : ℂ :=
  ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ φ' Φ J η g
      ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
    ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ

end GlobalTheory.RSPole
