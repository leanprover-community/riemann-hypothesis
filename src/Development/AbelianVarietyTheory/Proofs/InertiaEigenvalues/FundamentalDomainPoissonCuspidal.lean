module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntersectionFamilyMultilinear
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

theorem _root_.GlobalTheory.T.fundamental_domain_poisson_cuspidal : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    ∀ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ γ : {ξ : Fin (m + 1) → E // ξ ≠ 0} → GL (Fin (m + 1)) E,
    (∀ ξ, Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) (γ ξ).val = ξ.1) → ∀ h : GA E (m + 1),
    HasSum (fun ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0} =>
        GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (Matrix.vecMul (algebraMap E (Ad E) ∘ ξ.1) h.val) *
          partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) (ratGL E (m + 1) (γ ξ) * h)))
      (partialCoeff (GlobalTheory.RSnm.colSmooth (m + 1) F φ) (m + 1 + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) := by
  first | (exact @GlobalTheory.ColFourier.hasSum_colSmooth) | (exact GlobalTheory.ColFourier.hasSum_colSmooth) | (intros; apply GlobalTheory.ColFourier.hasSum_colSmooth  <;> assumption)
