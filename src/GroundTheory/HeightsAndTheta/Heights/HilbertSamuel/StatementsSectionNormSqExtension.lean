module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
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

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionNormSqExtension.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (m N : ℕ) (v : Fin N → Ω),
    IsSmoothHerm A → IsConjInvariantH A →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    ∃ S : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S {x | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} ∧
      (∀ x : (Σ k, ι k) → ℂ, (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → 0 < S x) ∧
      (∀ (c : K → ℂ) (x : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → S (fun p => c p.1 * x p) = S x) ∧
      (∀ x : (Σ k, ι k) → ℂ, S (fun p => (starRingEnd ℂ) (x p)) = S x) ∧
      (∀ x ∈ mcPts (mCoordIdeal y), S x = ∑ j, secNormAt y A m (v j) x ^ 2) ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ w : (Σ k, addIdx ι N k) → ℂ,
        IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z w →
        leviForm (fun z' : (Σ k, addIdx ι N k) → ℂ =>
            Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) / 2 - Real.log (S (basePart₂ z')) / 2) z w =
          (m : ℝ) * leviForm (fun x => Real.log (A.h x)) (basePart₂ z) (basePart₂ w)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
