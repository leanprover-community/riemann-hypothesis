module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import Mathlib.Algebra.Module.ZLattice.Covolume
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def imageLattice {E V : Type*} [AddCommGroup E] [AddCommGroup V] (φ : E →+ V) : Submodule ℤ V :=
  AddSubgroup.toIntSubmodule φ.range

def EuclideanSections.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (r : ℕ → ℕ) (φ : ∀ n : ℕ, chartLat y A.a n →+ EuclideanSpace ℝ (Fin (r n))),
      (∀ n, Function.Injective (φ n)) ∧
      (∀ n, DiscreteTopology (imageLattice (φ n))) ∧
      (∀ n [DiscreteTopology (imageLattice (φ n))], IsZLattice ℝ (imageLattice (φ n))) ∧
      (∀ (n : ℕ) (c : ℝ) (s : chartLat y A.a n), 0 ≤ c →
        IsBoundedH (mCoordIdeal y) y A n c (s : Ω) → ‖φ n s‖ ≤ c) ∧
      (∃ C : ℝ, ∀ n : ℕ, (r n : ℝ) ≤ C * ((n : ℝ) + 1) ^ D) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ∀ [DiscreteTopology (imageLattice (φ n))] [IsZLattice ℝ (imageLattice (φ n))],
          -Real.log (ZLattice.covolume (imageLattice (φ n))) ≤
            (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
              ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
