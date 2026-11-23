module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingsEqualImagesEqual
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.regular_rings_equal_images_equal : ∀ (P X₁ X₂ : Scheme.{0}) (Ω : Type) [Field Ω] (ξ₀ : Sp Ω ⟶ P) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (f₁ : X₁ ⟶ P) (f₂ : X₂ ⟶ P) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → IsCptGen ξ₁ → IsCptGen ξ₂ → ξ₁ ≫ f₁ = ξ₀ → ξ₂ ≫ f₂ = ξ₀ → ∀ (p₁ : Cpt ξ₁) (p₂ : Cpt ξ₂), regAt ξ₁ p₁ = regAt ξ₂ p₂ → f₁ p₁.1 = f₂ p₂.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.image_eq_of_regAt_eq | exact GlobalTheory.CompanionTheory.Ar.SncBase.image_eq_of_regAt_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.image_eq_of_regAt_eq <;> assumption)
