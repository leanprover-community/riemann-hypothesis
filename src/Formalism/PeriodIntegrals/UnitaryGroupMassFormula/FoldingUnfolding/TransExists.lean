module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.FoldDCUnfold.W

universe u

def TransExists : Prop :=
  ∀ (G : Type u) [Group G] (K H : Subgroup G), H ≤ K → ∃ E : Set G, IsRightTransversal K H E

def TransIndep : Prop :=
  ∀ (G : Type u) [Group G] (Γ H : Subgroup G) (T T' : Set G),
    IsRightTransversal Γ H T → IsRightTransversal Γ H T' →
    ∀ c ∈ Γ, ∀ f : G → ℝ≥0∞, (∀ s ∈ H, ∀ y : G, f (s * y) = f y) →
      ∑' η : T, f ((η : G) * c) = ∑' η : T', f (η : G)

def TransProd : Prop :=
  ∀ (G : Type u) [Group G] (Γ S H : Subgroup G) (E D : Set G), H ≤ S → S ≤ Γ →
    IsRightTransversal S H E → IsRightTransversal Γ S D →
    Function.Injective (fun p : E × D => (p.1 : G) * (p.2 : G)) ∧
      IsRightTransversal Γ H (Set.range (fun p : E × D => (p.1 : G) * (p.2 : G)))

def DCTrans : Prop :=
  ∀ (G : Type u) [Group G] (Γ S S' : Subgroup G), S ≤ Γ → S' ≤ Γ →
    ∀ (R : Set G), IsDoubleTransversal Γ S S' R →
    ∀ (E : G → Set G), (∀ r ∈ R, IsRightTransversal S (stab S S' r) (E r)) →
      Function.Injective (fun p : (Σ r : R, E (r : G)) => (p.1 : G)⁻¹ * (p.2 : G)) ∧
        IsRightTransversal Γ S'
          (Set.range (fun p : (Σ r : R, E (r : G)) => (p.1 : G)⁻¹ * (p.2 : G)))

end PI.FoldDCUnfold.W
