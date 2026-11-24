module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLineBundleSectionOfClosedImmersionAffineOpen
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lift_lineBundle_section_of_closedImmersion_affineOpen : ∀ (X' Z' : Scheme.{0}) (i' : Z' ⟶ X') [IsClosedImmersion i'] (L' : LB X'), L'.IsLB →
    ∀ (Y' : X'.Opens), IsAffineOpen Y' → ∀ (τ : ∀ k, Γ(Z', i' ⁻¹ᵁ (L'.U k ⊓ Y'))),
    (∀ (k l : L'.ι) (z : Z') (hk : z ∈ i' ⁻¹ᵁ (L'.U k ⊓ Y')) (hl : z ∈ i' ⁻¹ᵁ (L'.U l ⊓ Y')),
      Z'.presheaf.germ _ z hk (τ k) =
        Z'.presheaf.germ (i' ⁻¹ᵁ (L'.U k ⊓ L'.U l)) z ⟨hk.1, hl.1⟩ ((i'.app _).hom (L'.g k l).val) *
          Z'.presheaf.germ _ z hl (τ l)) →
    ∃ θ : ∀ k, Γ(X', L'.U k ⊓ Y'),
      (∀ (k l : L'.ι) (x : X') (hk : x ∈ L'.U k ⊓ Y') (hl : x ∈ L'.U l ⊓ Y'),
        X'.presheaf.germ _ x hk (θ k) =
          X'.presheaf.germ (L'.U k ⊓ L'.U l) x ⟨hk.1, hl.1⟩ (L'.g k l).val * X'.presheaf.germ _ x hl (θ l)) ∧
      ∀ k, (i'.app (L'.U k ⊓ Y')).hom (θ k) = τ k := by
  first | exact @GlobalTheory.PinchLift.lift_section_of_closedImm | exact GlobalTheory.PinchLift.lift_section_of_closedImm | (intros; apply GlobalTheory.PinchLift.lift_section_of_closedImm <;> assumption)
