module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntermediateGrpPullbackAbelianScheme
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.RingTheory.DividedPowers.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme : ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (ρ : R →+* R₁) (π₁ : R₁ →+* R₀) (g : ℕ)
    (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (spMap (π₁.comp ρ)) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left),
      IsGrpPullback A₀ A₁ (spMap π₁) i₁ ∧ IsGrpPullback A₁ A (spMap ρ) i₂ ∧ i₁ ≫ i₂ = i ∧ IsAbelianScheme A₁ ∧
      SmoothOfRelativeDimension g A₁.hom := by
  first | exact @GlobalTheory.SqLift.exists_intermediate_grpPullback | exact GlobalTheory.SqLift.exists_intermediate_grpPullback | (intros; apply GlobalTheory.SqLift.exists_intermediate_grpPullback <;> assumption)
