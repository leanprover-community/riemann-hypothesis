module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

theorem exists_germ_frac {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) {y : X}
    (hs : ξ (IsLocalRing.closedPoint Ω) ⤳ y) (a : Ω) :
    ∃ f g : X.presheaf.stalk y,
      (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom g ≠ 0 ∧
      a * (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom g =
        (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom f := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y) (U := ⊤) trivial
  have hzU : ξ (IsLocalRing.closedPoint Ω) ∈ U := hs.mem_open U.isOpen hyU
  let z : U := ⟨_, hzU⟩
  letI := X.presheaf.algebra_section_stalk z
  have hl := hU.isLocalization_stalk z
  obtain ⟨s, rfl⟩ := hb.2 a
  obtain ⟨⟨f, g⟩, e⟩ := IsLocalization.surj (S := X.presheaf.stalk z.1)
    (hU.primeIdealOf z).asIdeal.primeCompl s
  have hgerm : ∀ r : Γ(X, U), (X.presheaf.stalkSpecializes hs).hom (X.presheaf.germ U y hyU r) =
      X.presheaf.germ U _ hzU r := fun r =>
    ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hyU hs) r
  refine ⟨X.presheaf.germ U y hyU f, X.presheaf.germ U y hyU g.1, ?_, ?_⟩
  · have hu : IsUnit (X.presheaf.germ U _ hzU g.1) :=
      IsLocalization.map_units (X.presheaf.stalk z.1) g
    have := hu.map (Scheme.stalkClosedPointTo ξ).hom
    simpa [hgerm] using this.ne_zero
  · have e' : s * X.presheaf.germ U _ hzU g.1 = X.presheaf.germ U _ hzU f := e
    have := congrArg (Scheme.stalkClosedPointTo ξ).hom e'
    simpa [hgerm] using this

theorem isFractionRing_regAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ →
    ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω := by
  intro X Ω _ ξ h p
  refine IsFractionRing.of_field (regAt ξ p) Ω fun a => ?_
  obtain ⟨f, g, hg, e⟩ := exists_germ_frac ξ h.bij (y := p.1) p.2 a
  refine ⟨⟨genMap ξ p f, f, rfl⟩, ⟨genMap ξ p g, g, rfl⟩, ?_⟩
  exact eq_div_of_mul_eq hg e

end GlobalTheory.CompanionTheory.Ar.LieStalk
