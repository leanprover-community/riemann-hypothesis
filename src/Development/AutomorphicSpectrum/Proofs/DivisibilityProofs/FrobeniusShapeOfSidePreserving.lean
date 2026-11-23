module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem isLeft_pow_congr {Ψ : Type} (f : Equiv.Perm (Ψ ⊕ Ψ))
    (hf : (∀ σ, (f σ).isLeft = σ.isLeft) ∨ ∀ σ, (f σ).isLeft = σ.isRight) (k : ℕ) :
    ∀ σ σ' : Ψ ⊕ Ψ, σ.isLeft = σ'.isLeft → ((f ^ k) σ).isLeft = ((f ^ k) σ').isLeft := by
  induction k with
  | zero =>
    intro σ σ' h
    simpa using h
  | succ k ih =>
    intro σ σ' h
    have h' := ih σ σ' h
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rcases hf with hf | hf
    · rw [hf, hf]
      exact h'
    · rw [hf, hf]
      cases h1 : (f ^ k) σ <;> cases h2 : (f ^ k) σ' <;> simp_all

theorem frobShape_of_side : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)), (∀ p, (∀ σ, (φ p σ).isLeft = σ.isLeft) ∨ ∀ σ, (φ p σ).isLeft = σ.isRight) → FrobShape fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ : Ψ ⊕ Ψ) := by
  intro Ψ _ _ φ h
  unfold FrobShape
  intro p n τ τ'
  exact isLeft_pow_congr (φ p) (h p) (n + 1) _ _ rfl

end GlobalTheory.CompanionTheory.Ar.Num
