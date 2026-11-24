module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureEndomorphismHomLiftSquareZero
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.pure_endomorphism_hom_lift_square_zero : GlobalTheory.Published.GrothendieckMessing → ∀ p : ℕ, p.Prime → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), IsNilpotent (p : R) → Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (g g' : ℕ) (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom → IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → ∀ (U : A ⟶ A) (V : B ⟶ B) (U₀ : A₀ ⟶ A₀) (V₀ : B₀ ⟶ B₀) [IsMonHom U] [IsMonHom V] [IsMonHom U₀] [IsMonHom V₀], i ≫ U.left = U₀.left ≫ i → j ≫ V.left = V₀.left ≫ j → ∀ r s r' s' : R, IsPure A U r s → IsPure B V r' s' → IsUnit (r - s') → ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], U₀ ≫ f₀ = f₀ ≫ V₀ → ∃ f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j ∧ U ≫ f = f ≫ V ∧ ∀ f' : A ⟶ B, IsMonHom f' → i ≫ f'.left = f₀.left ≫ j → f' = f := by
  first | exact @GlobalTheory.pureLift_step | exact GlobalTheory.pureLift_step | (intros; apply GlobalTheory.pureLift_step <;> assumption)
