module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

def FamUnif : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra ℂ B] [Algebra.FiniteType ℂ B] (𝒜 : Over (Sp B)) [GrpObj 𝒜] (g : ℕ),
    IsAbelianScheme 𝒜 → SmoothOfRelativeDimension g 𝒜.hom →
    ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (y : (I → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen U → 0 ∈ U →
      (∀ b, DifferentiableOn ℂ (fun z ↦ y z b) U) →
    ∀ (A : (I → ℂ) → Over (Sp ℂ)) [∀ z, GrpObj (A z)] (φ : ∀ z, (A z).left ⟶ 𝒜.left),
      (∀ z, IsGrpPullback (A z) 𝒜 (spMap (y z : B →+* ℂ)) (φ z)) →
    ∀ (L : ∀ z, LB (A z).left), (∀ z, (L z).IsLB) →
    ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (φ₀ : A₀.left ⟶ 𝒜.left), IsGrpPullback A₀ 𝒜 (spMap (y 0 : B →+* ℂ)) φ₀ →
    ∀ (L₀ : LB A₀.left) (u₀ : HolUnif A₀ L₀ g),
    ∃ (r : ℝ) (u : ∀ z, HolUnif (A z) (L z) g) (τ : ∀ z, u₀.Λ ≃+ (u z).Λ), 0 < r ∧ Metric.ball 0 r ⊆ U ∧
      IsHolTo (Metric.ball (0 : I → ℂ) r ×ˢ (Set.univ : Set (Fin g → ℂ)))
        (fun q ↦ (show Sp ℂ ⟶ (A q.1).left from ((u q.1).ex q.2).left) ≫ φ q.1) ∧
      (∃ W : 𝒜.left.Opens, IsAffineOpen W ∧ ∀ z ∈ Metric.ball (0 : I → ℂ) r,
        ⊤ ≤ ((show Sp ℂ ⟶ (A z).left from ((u z).ex 0).left) ≫ φ z) ⁻¹ᵁ W) ∧
      (∀ w, ((u 0).ex w).left ≫ φ 0 = (u₀.ex w).left ≫ φ₀) ∧ (∀ x, (τ 0 x : Fin g → ℂ) = x) ∧
      (∀ x, DifferentiableOn ℂ (fun z ↦ (τ z x : Fin g → ℂ)) (Metric.ball 0 r)) ∧
      ∀ (α : 𝒜 ⟶ 𝒜) [IsMonHom α] (M₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
        (∀ w, (u₀.ex (M₀ w)).left ≫ φ₀ = (u₀.ex w).left ≫ φ₀ ≫ α.left) →
        ∀ z ∈ Metric.ball (0 : I → ℂ) r, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
          (∀ w, ((u z).ex (M w)).left ≫ φ z = ((u z).ex w).left ≫ φ z ≫ α.left) ∧
          ∀ x x' : u₀.Λ, (x' : Fin g → ℂ) = M₀ x → (τ z x' : Fin g → ℂ) = M (τ z x)

end GlobalTheory.PeriodFamily
