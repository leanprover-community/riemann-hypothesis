module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPoint
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MoverFibre

theorem isIrreducible_fibre_fst : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, IsIrreducible ((fst G G).left ⁻¹' {x}) := by
  intro R _ G _ hG x
  let j := G.left.fromSpecResidueField x
  let p₁ : pullback G.hom G.hom ⟶ G.left := pullback.fst G.hom G.hom
  have hp : (fst G G).left = p₁ := rfl
  have hirr0 := GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ G hG _ (j ≫ G.hom)
  haveI hirr : IrreducibleSpace (pullback G.hom (j ≫ G.hom) : Scheme.{0}) := hirr0
  let e : pullback G.hom (j ≫ G.hom) ≅ p₁.fiber x :=
    pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso G.hom G.hom j).symm ≪≫ pullbackSymmetry _ _
  have hr := (IrreducibleSpace.isIrreducible_univ (pullback G.hom (j ≫ G.hom) : Scheme.{0})).image _
      ((e.hom ≫ Scheme.Hom.fiberι p₁ x).continuous.continuousOn)
  rw [Set.image_univ] at hr
  have hrange : Set.range (e.hom ≫ Scheme.Hom.fiberι p₁ x) = Set.range (Scheme.Hom.fiberι p₁ x) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨e.hom z, by rw [Scheme.Hom.comp_apply]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨e.inv z, by rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e.inv e.hom, e.inv_hom_id]; rfl⟩
  show IsIrreducible (p₁ ⁻¹' {x})
  rw [← Scheme.Hom.range_fiberι p₁ x, ← hrange]
  exact hr

end GlobalTheory.MoverFibre
