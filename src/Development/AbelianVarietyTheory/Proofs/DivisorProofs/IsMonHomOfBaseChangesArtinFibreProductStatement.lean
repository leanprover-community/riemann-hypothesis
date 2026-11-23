module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfBaseChangesArtinFibreProduct
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.isGrpPullback_id_of_baseChanges_artinFibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A' A : Over (Spec P)) [GrpObj A'] [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (A₀ : Over (Spec R₀)) [GrpObj A₁] [GrpObj A₂] [GrpObj A₀] (j₁ : A₁.left ⟶ A'.left) (j₂ : A₂.left ⟶ A'.left) (k₁ : A₁.left ⟶ A.left) (k₂ : A₂.left ⟶ A.left) (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left) (φ : A'.left ⟶ A.left), Flat A'.hom → IsGrpPullback A₁ A' (Spec.map f₁) j₁ → IsGrpPullback A₂ A' (Spec.map f₂) j₂ → IsGrpPullback A₁ A (Spec.map f₁) k₁ → IsGrpPullback A₂ A (Spec.map f₂) k₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) i₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) i₂ → i₁ ≫ j₁ = i₂ ≫ j₂ → IsPullback φ A'.hom A.hom (𝟙 _) → j₁ ≫ φ = k₁ → j₂ ≫ φ = k₂ → IsGrpPullback A' A (𝟙 _) φ := by
  first | exact @GlobalTheory.PinchHom.main | exact GlobalTheory.PinchHom.main | (intros; apply GlobalTheory.PinchHom.main <;> assumption)
