module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import GroundTheory.HeightsAndTheta.Heights.HermitianLattice
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelLocalizationAtPrime
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.lie_model_localization_at_prime : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L]
    (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra (𝓞 L) A]
    [IsLocalization.AtPrime A 𝔭] [Algebra A L] [IsScalarTower (𝓞 L) A L] (z : Sp (𝓞 L) ⟶ X)
    (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier) (f : Module.Dual Ω Li)
    (h : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) A) ≫ z)), IsCptGen ξ →
    (∀ e ∈ M.lat ⟨_, h⟩, f e ∈ regAt ξ ⟨_, h⟩) →
    (∀ h' : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z), ∀ e ∈ M.lat ⟨_, h'⟩, f e ∈ regAt ξ ⟨_, h'⟩) →
    ∃ g : B.carrier →ₗ[𝓞 L] A,
      (∀ (x : B.carrier) (e : Li) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G) (u : L),
        M.ValAt _ e v → (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left) →
        ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (f e) u → algebraMap A L (g x) = u) ∧
      ∀ (e : Li) (u : A), e ∈ M.lat ⟨_, h⟩ → ValAt ξ (spMap (algebraMap (𝓞 L) A) ≫ z) (f e) u →
        ∃ (d : 𝓞 L) (n : ℕ) (x x' : B.carrier) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
          d ∉ 𝔭 ∧ n ≠ 0 ∧ g x = algebraMap (𝓞 L) A d * u ∧ M.ValAt _ ((n : Ω) • e) v ∧
          (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x').left) ∧ (n : 𝓞 L) • x = d • x' := by
  exact @GlobalTheory.CompanionTheory.Ar.RootHt.FinLie.exists_integral_form
