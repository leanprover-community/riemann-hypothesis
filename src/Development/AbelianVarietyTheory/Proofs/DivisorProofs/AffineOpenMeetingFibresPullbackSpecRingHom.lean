module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem affine_preimage_pullback_meets_fibres {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R')
    (A : Over (Sp R)) (W : A.left.Opens) : IsAffineOpen W →
    (∀ t ∈ Set.range (spMap a), ∃ x ∈ W, A.hom x = t) →
    ∃ V : ((Over.pullback (spMap a)).obj A).left.Opens, IsAffineOpen V ∧
      ∀ s : Sp R', ∃ x ∈ V, ((Over.pullback (spMap a)).obj A).hom x = s := by
  intro hW hfib
  haveI : IsAffineHom (pullback.fst A.hom (spMap a)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  refine ⟨(pullback.fst A.hom (spMap a)) ⁻¹ᵁ W, hW.preimage _, ?_⟩
  intro s
  obtain ⟨x, hxW, hx⟩ := hfib (spMap a s) ⟨s, rfl⟩
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := A.hom) (g := spMap a) x s hx
  exact ⟨z, by show (pullback.fst A.hom (spMap a)) z ∈ W; rw [hz1]; exact hxW, hz2⟩

end GlobalTheory
