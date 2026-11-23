module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.HermitianNormSquare

theorem core_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V) {n : ℕ}
    (e : Fin n → V) (w : Fin n → ℂ) :
    c.inner (∑ a, w a • e a) (∑ a, w a • e a)
      = star w ⬝ᵥ ((Matrix.of fun a b => c.inner (e a) (e b)) *ᵥ w) := by
  letI : PreInnerProductSpace.Core ℂ V := c.toCore
  have hl : ∀ (s : Finset (Fin n)) (f : Fin n → V) (y : V),
      c.inner (∑ a ∈ s, f a) y = ∑ a ∈ s, c.inner (f a) y := by
    intro s f y
    induction s using Finset.induction_on with
    | empty => simpa using InnerProductSpace.Core.inner_zero_left (𝕜 := ℂ) y
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      exact InnerProductSpace.Core.inner_add_left (𝕜 := ℂ) _ _ _
  have hr : ∀ (s : Finset (Fin n)) (f : Fin n → V) (x : V),
      c.inner x (∑ a ∈ s, f a) = ∑ a ∈ s, c.inner x (f a) := by
    intro s f x
    induction s using Finset.induction_on with
    | empty => simpa using InnerProductSpace.Core.inner_zero_right (𝕜 := ℂ) x
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      exact InnerProductSpace.Core.inner_add_right (𝕜 := ℂ) _ _ _
  rw [hl]
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ), hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ)]
  simp only [RCLike.star_def, Complex.star_def]
  ring

end PositivityTheory.Xgn.HermitianNormSquare

theorem PositivityTheory.Xgn.hermitian_norm_square_formula : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (ε : Fin n → B.carrier) (Γ : Matrix (Fin n) (Fin n) ℂ),
    (∀ a b, Γ a b = (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b)) → ∀ w : Fin n → ℂ,
    sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) = (star w ⬝ᵥ (Γ *ᵥ w)).re := by
  intro L _ _ B σ n ε Γ hΓ w
  have hx : (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a :
      GroundTheory.Heights₂.Heights.Fibre σ B.carrier)
      = ∑ a, w a • ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul']
    congr 1
    change w a = w a * 1
    rw [_root_.mul_one]
  have hM : Γ = Matrix.of fun a b => (B.metric.form σ).inner
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b) := by
    ext a b
    exact hΓ a b
  unfold sqAt
  rw [hx, hM, ← PositivityTheory.Xgn.HermitianNormSquare.core_sum]
