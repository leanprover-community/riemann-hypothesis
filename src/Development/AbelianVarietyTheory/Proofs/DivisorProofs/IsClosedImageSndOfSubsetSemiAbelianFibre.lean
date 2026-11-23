module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFromSpecResidueFieldCompOfIsClosedOfClosStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
      ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) →
      ∀ N : Set (G ⊗ G).left, IsClosed N → N ⊆ (fst G G).left ⁻¹' {x} →
      IsClosed ((snd G G).left '' N) := by
  intro R _ _ G _ hG x hx hxc N hN hNZ
  have hlft : LocallyOfFiniteType G.hom := by
    haveI := hG.smooth; infer_instance
  have hfin : IsFinite (G.left.fromSpecResidueField x ≫ G.hom) :=
    GlobalTheory.T.isFinite_fromSpecResidueField_comp_of_closed R G hlft x hx hxc
  set k := G.left.fromSpecResidueField x
  set f := G.hom
  let i := pullback.snd k (pullback.fst f f)
  have hrange : Set.range i = (pullback.fst f f) ⁻¹' {x} := by
    simp only [i, Scheme.Pullback.range_snd, k, Scheme.range_fromSpecResidueField]
  have hcomp : i ≫ pullback.snd f f =
      (pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f :=
    (pullbackRightPullbackFstIso_hom_snd f f k).symm
  have hcl : IsClosedMap (i ≫ pullback.snd f f) := by
    rw [hcomp]
    haveI := hfin
    haveI : IsFinite (pullback.snd (k ≫ f) f) := inferInstance
    exact ((pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f).isClosedMap
  have hNi : (snd G G).left '' N = (i ≫ pullback.snd f f) '' (i ⁻¹' N) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Set.image_preimage_eq_of_subset]
    · rfl
    · rw [hrange]; exact hNZ
  rw [hNi]
  exact hcl _ (hN.preimage i.continuous)
