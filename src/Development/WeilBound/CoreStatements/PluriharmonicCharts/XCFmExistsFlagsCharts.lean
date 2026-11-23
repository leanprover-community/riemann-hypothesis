module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

private theorem stalkClosedPointTo_specMap_comp_eq {X : Scheme.{0}} {Ω G : Type} [Field Ω] [Field G]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* G) :
    ∃ e : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint G) = ξ (IsLocalRing.closedPoint Ω),
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i) ≫ ξ) =
        (X.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
  have hξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hi : IsLocalHom i := ⟨fun a ha => isUnit_iff_ne_zero.mpr (fun h0 => by simp [h0] at ha)⟩
  have hloc : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom := by
    rw [CommRingCat.hom_comp]
    infer_instance
  have key := (SpecToEquivOfLocalRing X (CommRingCat.of G)).right_inv
    ⟨_, Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i, hloc⟩
  rw [SpecToEquivOfLocalRing_eq_iff] at key
  obtain ⟨h1, h2⟩ := key
  change (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω))) (IsLocalRing.closedPoint G) = ξ (IsLocalRing.closedPoint Ω) at h1
  change Scheme.stalkClosedPointTo (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω))) = (X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom ≫
      Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i at h2
  have hg : Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
      X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
    rw [Spec.map_comp, Category.assoc, hξ]
  revert h1 h2
  generalize Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) = k at hg
  subst hg
  intro h1 h2
  exact ⟨h1, h2⟩

private theorem stalkClosedPointTo_stalkSpecializes_comp {X : Scheme.{0}} {Ω G : Type} [Field Ω] [Field G]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* G) (g : Spec (CommRingCat.of G) ⟶ X)
    (hg : g = Spec.map (CommRingCat.ofHom i) ≫ ξ) (y : X) (hy : g (IsLocalRing.closedPoint G) ⤳ y)
    (h : ξ (IsLocalRing.closedPoint Ω) ⤳ y) (s : X.presheaf.stalk y) :
    (Scheme.stalkClosedPointTo g).hom ((X.presheaf.stalkSpecializes hy).hom s) =
      i ((Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes h).hom s)) := by
  subst hg
  obtain ⟨e, he⟩ := stalkClosedPointTo_specMap_comp_eq ξ i
  rw [he]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.stalkCongr_hom, CommRingCat.hom_ofHom]
  congr 2
  have hh := TopCat.Presheaf.stalkSpecializes_comp X.presheaf (Inseparable.of_eq e.symm).specializes hy
  exact congrArg (fun k => CommRingCat.Hom.hom k s) hh

theorem PositivityTheory.Xgp.inChart_iff_inChart_map_of_dominates : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (i : Ω →+* G) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => i (x k)) c₁ p' := by
  intro X X' Ω G _ _ ξ ξ' f i κ x hT hG' hD p' c₁ h
  set q : Cpt ξ := ⟨f p'.1, h⟩ with hq
  have K : ∀ s : X.presheaf.stalk (f p'.1), genMap ξ' p' ((f.stalkMap p'.1).hom s) = i (genMap ξ q s) := by
    intro s
    have e1 := stalkClosedPointTo_stalkSpecializes_comp ξ i (ξ' ≫ f) hD (f p'.1) (f.base.hom.map_specializes p'.2) h s
    rw [Scheme.stalkClosedPointTo_comp] at e1
    exact (congrArg (Scheme.stalkClosedPointTo ξ').hom
      (Scheme.Hom.stalkSpecializes_stalkMap_apply f _ _ p'.2 s).symm).trans e1
  have F1 : ∀ a, a ∈ regAt ξ q → i a ∈ regAt ξ' p' := by
    intro a ha
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    exact RingHom.mem_range.mpr ⟨_, K s⟩
  have F2 : ∀ a, a ∈ regAt ξ q → (i a)⁻¹ ∈ regAt ξ' p' → a⁻¹ ∈ regAt ξ q := by
    intro a ha hinv
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    obtain ⟨t, ht⟩ := RingHom.mem_range.mp hinv
    by_cases h0 : genMap ξ q s = 0
    · rw [h0, _root_.inv_zero]
      exact zero_mem _
    have hu : IsUnit ((f.stalkMap p'.1).hom s) := by
      have hm : (f.stalkMap p'.1).hom s * t = 1 := by
        apply hG'.inj p'
        rw [map_mul, map_one, K, ht, mul_inv_cancel₀ ((map_ne_zero i).mpr h0)]
      exact isUnit_iff_exists_inv.mpr ⟨t, hm⟩
    obtain ⟨v, hv⟩ := (isUnit_map_iff (f.stalkMap p'.1).hom s).mp hu
    refine RingHom.mem_range.mpr ⟨↑v⁻¹, ?_⟩
    rw [← hv, map_units_inv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(map_ne_zero i).mpr h1, fun c' => ?_⟩
    show i (x c') / i (x c₁) ∈ regAt ξ' p'
    rw [← map_div₀]
    exact F1 _ (h2 c')
  · rintro ⟨h1, h2⟩
    have h1' : x c₁ ≠ 0 := fun h0 => h1 (by simp [h0])
    obtain ⟨c, hc⟩ := hT.cover q
    obtain ⟨hc0, hc⟩ := hc
    refine ⟨h1', fun c' => ?_⟩
    have hinv : (i (x c₁ / x c))⁻¹ ∈ regAt ξ' p' := by
      rw [map_div₀, inv_div]
      exact h2 c
    have hw := F2 _ (hc c₁) hinv
    have e : x c' / x c₁ = (x c' / x c) * (x c₁ / x c)⁻¹ := by
      field_simp
    rw [e]
    exact mul_mem (hc c') hw
