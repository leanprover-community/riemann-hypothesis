module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordsDown

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

theorem isUnit_natCast_of_local {A : Type*} [CommRing A] (φ : A →+* ℂ) [IsLocalHom φ] (r : ℕ) (hr : r.Prime) :
    IsUnit (r : A) := by
  apply isUnit_of_map_unit φ
  rw [map_natCast]
  exact isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hr.ne_zero)

theorem unitAt_centre {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (z : Spec (CommRingCat.of ℂ) ⟶ X')
    (h : genPt ξ' ⤳ centre z) (r : ℕ) (hr : r.Prime) : unitAt ξ' ⟨centre z, h⟩ (r : Ω) := by
  have hz : IsLocalHom (Scheme.stalkClosedPointTo z).hom := inferInstance
  have hu : IsUnit ((r : X'.presheaf.stalk (centre z))) := isUnit_natCast_of_local (Scheme.stalkClosedPointTo z).hom r hr
  have hu' : IsUnit ((r : Ω)) := by
    have := hu.map (genMap ξ' ⟨centre z, h⟩)
    rwa [map_natCast] at this
  obtain ⟨u, hu1⟩ := hu.exists_right_inv
  refine ⟨hu'.ne_zero, ⟨(r : X'.presheaf.stalk (centre z)), map_natCast _ _⟩, ⟨u, ?_⟩⟩
  have e := congrArg (genMap ξ' ⟨centre z, h⟩) hu1
  rw [map_mul, map_natCast, map_one] at e
  exact eq_inv_of_mul_eq_one_right e

theorem genMap_stalkMap (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ g) ⤳ g q.1) (s : X.presheaf.stalk (g q.1)) :
    genMap ξ' q ((g.stalkMap q.1).hom s) = genMap (ξ' ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ' g
  have e4 := congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

theorem valAt_down {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (g : X' ⟶ X) (hinj : IsCptGen ξ')
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (h' : genPt ξ' ⤳ centre z)
    (h : genPt (ξ' ≫ g) ⤳ g (centre z))
    (hreg : regAt ξ' ⟨centre z, h'⟩ = regAt (ξ' ≫ g) ⟨g (centre z), h⟩)
    {a : Ω} {r : ℂ} (hv : ValAt ξ' z a r) : ValAt (ξ' ≫ g) (z ≫ g) a r := by
  obtain ⟨h1, s, hs, rfl⟩ := hv
  have ha : a ∈ regAt (ξ' ≫ g) ⟨g (centre z), h⟩ := by
    rw [← hreg]
    exact ⟨s, hs⟩
  obtain ⟨s₀, hs₀⟩ := ha
  have e : (g.stalkMap (centre z)).hom s₀ = s := by
    apply hinj.inj ⟨centre z, h'⟩
    rw [genMap_stalkMap ξ' g ⟨centre z, h'⟩ h s₀]
    exact hs₀.trans hs.symm
  subst e
  refine ⟨h, s₀, hs₀, ?_⟩
  exact congrArg (fun t => t.hom s₀) (Scheme.stalkClosedPointTo_comp z g)

theorem coordsAt_down : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (K' : Type) (J' : K' → Type) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, J' k) → ℂ), (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → IsCptGen ξ' → ξ' ≫ g = ξ → (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) → (∀ q' : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt ξ' q' = regAt ξ ⟨g q'.1, h⟩) → CoordsAt ξ' y' z w → CoordsAt ξ y (z ≫ g) (fun p : (Σ k, J k) => w ⟨bk p.1, bx p.1 p.2⟩) := by
  intro X X' Ω _ ξ ξ' g K J y K' J' y' bk bx z w hall hall' hgen hcomp hy hreg hw
  subst hcomp
  refine ⟨fun k => ?_, fun k c hc => ?_⟩
  · obtain ⟨c, hc⟩ := hw.1 (bk k)
    exact ⟨(bx k).symm c, by simpa using hc⟩
  · obtain ⟨hne, hv⟩ := hw.2 (bk k) (bx k c) hc
    refine ⟨by rwa [hy] at hne, fun i => ?_⟩
    obtain ⟨r, hr, e⟩ := hv (bx k i)
    rw [hy, hy] at hr
    have h' := hall' (centre z)
    have h := hall (g (centre z))
    refine ⟨r, valAt_down g hgen z h' h (hreg ⟨centre z, h'⟩ (fun p hp hf => hf (unitAt_centre z h' p hp)) h) hr, e⟩

end GlobalTheory.CompanionTheory.Ar.CoordsDown
