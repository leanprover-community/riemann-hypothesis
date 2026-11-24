module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationLiftsSquareZeroSmoothLift
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

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.multiplication_lifts_square_zero_smooth_lift : FormSt → AxesVanishingExtendedDegOne → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) → Smooth X.hom → ∀ (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left), l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i → ∃ m : X ⊗ X ⟶ X, l ≫ m.left = (μ[A₀]).left ≫ i := by
  first | exact @GlobalTheory.Obs.mul_lifts | exact GlobalTheory.Obs.mul_lifts | (intros; apply GlobalTheory.Obs.mul_lifts <;> assumption)
