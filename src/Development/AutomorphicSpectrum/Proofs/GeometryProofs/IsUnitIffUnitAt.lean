module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
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

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ValHom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

def stalkEquiv {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
  RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun a b hab => hξ.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩

theorem stalkEquiv_coe {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (s : X.presheaf.stalk p.1) :
    ((stalkEquiv ξ hξ p s : regAt ξ p) : Ω) = genMap ξ p s := rfl

theorem isUnit_iff_unitAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (s : X.presheaf.stalk p.1) :
    IsUnit s ↔ unitAt ξ p (genMap ξ p s) := by
  constructor
  · intro hs
    obtain ⟨u, rfl⟩ := hs
    refine ⟨((u.isUnit).map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : _ˣ) : X.presheaf.stalk p.1), ?_⟩⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, Units.inv_mul, map_one]
  · rintro ⟨h0, -, ⟨t, ht⟩⟩
    refine IsUnit.of_mul_eq_one t (hξ.inj p ?_)
    rw [map_mul, map_one, ht, mul_inv_cancel₀ h0]

theorem exists_valAt_hom (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X)
    (h : genPt ξ ⤳ centre z) (hξ : IsCptGen ξ) :
    ∃ φ : regAt ξ ⟨centre z, h⟩ →+* R,
      (∀ (a : Ω) (r : R), ValAt ξ z a r ↔ ∃ ha : a ∈ regAt ξ ⟨centre z, h⟩, φ ⟨a, ha⟩ = r) ∧
      ∀ a : regAt ξ ⟨centre z, h⟩, IsUnit (φ a) ↔ unitAt ξ ⟨centre z, h⟩ (a : Ω) := by
  let p : Cpt ξ := ⟨centre z, h⟩
  let e := stalkEquiv ξ hξ p
  let v : X.presheaf.stalk (centre z) →+* R := (Scheme.stalkClosedPointTo z).hom
  have hv : IsLocalHom v := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  have key : ∀ s, e.symm (e s) = s := e.symm_apply_apply
  refine ⟨v.comp (e.symm : regAt ξ p →+* X.presheaf.stalk p.1), ?_, ?_⟩
  · intro a r
    constructor
    · rintro ⟨h', s, hs, hr⟩
      have hs' : genMap ξ p s = a := hs
      refine ⟨⟨s, hs'⟩, ?_⟩
      have : (⟨a, ⟨s, hs'⟩⟩ : regAt ξ p) = e s := Subtype.ext hs'.symm
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [this, key]
      exact hr
    · rintro ⟨ha, hr⟩
      refine ⟨h, e.symm ⟨a, ha⟩, ?_, hr⟩
      have := stalkEquiv_coe ξ hξ p (e.symm ⟨a, ha⟩)
      rw [RingEquiv.apply_symm_apply] at this
      exact this.symm
  · intro a
    obtain ⟨s, rfl⟩ := e.surjective a
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [key]
    have : IsUnit (v s) ↔ IsUnit s := isUnit_map_iff v s
    exact this.trans (isUnit_iff_unitAt ξ hξ p s)

end GlobalTheory.CompanionTheory.Ar.ValHom
