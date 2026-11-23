module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogLogCut
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def deepMap {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (I : Fin d → Fin n) (y : Fin (d + 1) → ℂ) : Fin (d + 1) → ℂ :=
  vecCons (eval y P) fun i => s y (I i)

def deepJacDet {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (I : Fin d → Fin n) (y : Fin (d + 1) → ℂ) : ℂ :=
  LinearMap.det ((fderiv ℂ (deepMap P s I) y : (Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) :
    (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ))

def TubeDeepRankOne.Statement : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin (d + 1)) (Fin n) ℂ) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (U : Set (Fin (d + 1) → ℂ)) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ),
    IsOpen U → y ∈ U → DifferentiableOn ℂ s U → (∀ y' ∈ U, A *ᵥ s y' = y') → eval y P ≠ 0 →
      ReciprocityTheory.AnForm.maDens
          (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y =
        (2 / Real.pi) ^ (d + 1) * ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 / ‖eval y P‖ ^ 2

end

end GroundTheory.Heights₂.Heights
