module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GenfibMap
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CentreSetDominatingPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingModelChartCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralClosureChartSpan
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaled
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringIntegralClosureMax
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MaximalIdealMembershipOfLocal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeMemIffNotUnitLocalization
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonempty
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionsTwoComponents
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeExistsUniquePoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLNormExists

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesRegAtLocal, Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisation

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesRegAtLocal =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesRegAtLocal", "h": "module\n\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight\npublic import Development.WeilBound.CoreStatements.HodgeTatePoints.GenfibMap\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem dominates_localRings : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (f : X' ⟶ X), Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, ((∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) :=
  PositivityTheory.HtPt.Mb.dom_local

end GlobalTheory.CompanionTheory.Ar
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesRegAtLocal =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisation =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisation", "h": "module\n\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne\npublic import Mathlib.AlgebraicGeometry.Morphisms.Finite\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CentreSetDominatingPoint\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesRegAtLocal\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingModelChartCompat\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMap\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralClosureChartSpan\npublic import Mathlib.Algebra.Algebra.Subalgebra.Basic\npublic import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaled\npublic import Mathlib.RingTheory.IntegralClosure.Algebra.Basic\npublic import Mathlib.RingTheory.LocalRing.LocalSubring\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringIntegralClosureMax\npublic import Mathlib.RingTheory.LocalRing.Defs\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MaximalIdealMembershipOfLocal\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeMemIffNotUnitLocalization\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonempty\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionsTwoComponents\nimport Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeExistsUniquePoint\nimport Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalization\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PicardGroup\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.WeilBound.CoreStatements.HodgeTatePoints.MbLNormExists\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.NormEx

instance isLocalRing_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) :=
  (LocalSubring.range (genMap ξ p)).isLocalRing

theorem map_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ) (a : Ω)
    (ha : a ∈ chRing o x c) : algebraMap Ω Ω' a ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c := by
  induction ha using Algebra.adjoin_induction with
  | mem a h =>
    obtain ⟨j, rfl⟩ := h
    rw [map_div₀]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ r
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem normal_of_charts {o : Type} [CommRing o] {Ω' : Type} [Field Ω'] [Algebra o Ω'] {κ' : Type} [Finite κ']
    {y : κ' → Ω'} (M' : PModel o y) (S : Set κ') (hS : ∀ p' : Cpt M'.ξ, ∃ c ∈ S, InChart M'.ξ y c p')
    (hI : ∀ c ∈ S, ∀ a : Ω', IsIntegral (chRing o y c) a → a ∈ chRing o y c) : Flat.NormalCpt M'.ξ := by
  intro p' a ha
  obtain ⟨c, hcS, hp⟩ := hS p'
  have h := _root_.GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation o Ω' κ' y M' c p' hp
  refine PositivityTheory.HtPt.Mb.LNormExists.NormEx.mem_of_isIntegral_loc (chRing o y c) (regAt M'.ξ p') (hI c hcS) h.1 (fun a ha => ?_) a ha
  obtain ⟨u, hu, v, hv, hvu, rfl⟩ := (h.2 a).1 ha
  exact ⟨u, hu, v, hv, hvu.1, hvu.2.2, rfl⟩

section Sit

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω']
  {κ' : Type} [Finite κ'] {y : κ' → Ω'} (M' : PModel o y) (f : M'.X ⟶ M.X) (e : κ → κ')


variable {M Ω' M' f} in
theorem dom_of_eq (hD : Dominates M'.ξ M.ξ f (algebraMap Ω Ω')) {p : Cpt M.ξ} {p' : Cpt M'.ξ} (h : f p'.1 = p.1) :
    (∀ a ∈ regAt M.ξ p, algebraMap Ω Ω' a ∈ regAt M'.ξ p') ∧
      ∀ a ∈ regAt M.ξ p, unitAt M'.ξ p' (algebraMap Ω Ω' a) → unitAt M.ξ p a := by
  obtain ⟨h', hl⟩ := _root_.GlobalTheory.CompanionTheory.Ar.dominates_localRings M.X Ω M.ξ M'.X Ω' M'.ξ (algebraMap Ω Ω') f hD p'
  have e : (⟨f p'.1, h'⟩ : Cpt M.ξ) = p := Subtype.ext h
  rwa [e] at hl

theorem fibre_iff (hD : Dominates M'.ξ M.ξ f (algebraMap Ω Ω'))
    (hB : ∀ c, x c ≠ 0 → ∀ a : Ω', IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) a → a ∈ chRing o y (e c))
    (hC : ∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, (∀ j, algebraMap Ω Ω' (x j) / algebraMap Ω Ω' (x c) ∈ regAt M'.ξ p') →
      InChart M'.ξ y (e c) p')
    (c : κ) (p : Cpt M.ξ) (hp : InChart M.ξ x c p) (p' : Cpt M'.ξ) :
    f p'.1 = p.1 ↔ InChart M'.ξ y (e c) p' ∧
      ∀ u ∈ chRing o x c, (unitAt M.ξ p u ↔ unitAt M'.ξ p' (algebraMap Ω Ω' u)) := by
  have hr := _root_.GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation o Ω κ x M c p hp
  constructor
  · intro h
    have hl := dom_of_eq hD h
    refine ⟨hC c hp.1 p' fun j => ?_, fun u hu => ⟨PositivityTheory.HtPt.Mb.LNormExists.NormEx.unitAt_map _ hl.1, hl.2 u (hr.1 u hu)⟩⟩
    rw [← map_div₀]
    exact hl.1 _ (hp.2 j)
  · rintro ⟨hp', hu⟩
    have hr' := _root_.GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation o Ω' κ' y M' (e c) p' hp'
    have hA : ∀ u ∈ chRing o x c, algebraMap Ω Ω' u ∈ regAt M'.ξ p' := fun u hu' =>
      hr'.1 _ (hB c hp.1 _ (isIntegral_algebraMap (x := (⟨_, map_chRing x Ω' c u hu'⟩ :
        chRing o (fun k => algebraMap Ω Ω' (x k)) c))))
    have hl : (∀ a ∈ regAt M.ξ p, algebraMap Ω Ω' a ∈ regAt M'.ξ p') ∧
        ∀ a ∈ regAt M.ξ p, unitAt M'.ξ p' (algebraMap Ω Ω' a) → unitAt M.ξ p a := by
      refine ⟨fun a ha => ?_, fun a ha h => ?_⟩
      · obtain ⟨u, h1, v, h2, hv, rfl⟩ := (hr.2 a).1 ha
        have := ((hu v h2).1 hv).2.2
        rw [map_div₀, div_eq_mul_inv]
        exact mul_mem (hA u h1) this
      · obtain ⟨u, h1, v, h2, hv, rfl⟩ := (hr.2 a).1 ha
        have h3 : unitAt M'.ξ p' (algebraMap Ω Ω' u) := by
          have h4 := Flat.ZUnit.mul h ((hu v h2).1 hv)
          have h5 : algebraMap Ω Ω' (u / v) * algebraMap Ω Ω' v = algebraMap Ω Ω' u := by
            rw [← map_mul, div_mul_cancel₀ _ hv.1]
          rwa [h5] at h4
        have h4 := Flat.ZUnit.mul ((hu u h1).2 h3) (Flat.ZUnit.inv hv)
        rwa [← div_eq_mul_inv] at h4
    obtain ⟨h', hl'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.dominates_localRings M.X Ω M.ξ M'.X Ω' M'.ξ (algebraMap Ω Ω') f hD p'
    exact congrArg Subtype.val (_root_.GlobalTheory.CompanionTheory.Ar.Centre.Sep.eq_of_dominated M M'.ξ (algebraMap Ω Ω') p' ⟨f p'.1, h'⟩ p hl' hl)

theorem chart_over (hD : Dominates M'.ξ M.ξ f (algebraMap Ω Ω'))
    (hB : ∀ c, x c ≠ 0 → ∀ a : Ω', IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) a → a ∈ chRing o y (e c))
    (hC : ∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, (∀ j, algebraMap Ω Ω' (x j) / algebraMap Ω Ω' (x c) ∈ regAt M'.ξ p') →
      InChart M'.ξ y (e c) p')
    (c : κ) (hc : x c ≠ 0) (p' : Cpt M'.ξ) :
    InChart M'.ξ y (e c) p' ↔ ∃ p : Cpt M.ξ, p.1 = f p'.1 ∧ InChart M.ξ x c p := by
  constructor
  · intro hp'
    have hr' := _root_.GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation o Ω' κ' y M' (e c) p' hp'
    have hA : ∀ u ∈ chRing o x c, algebraMap Ω Ω' u ∈ regAt M'.ξ p' := fun u hu' =>
      hr'.1 _ (hB c hc _ (isIntegral_algebraMap (x := (⟨_, map_chRing x Ω' c u hu'⟩ :
        chRing o (fun k => algebraMap Ω Ω' (x k)) c))))
    obtain ⟨p₀, hl, -, hch⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Centre.exists_centre o Ω κ x M M'.X Ω' M'.ξ (algebraMap Ω Ω') p' ⟨c, hc, hA⟩
    obtain ⟨h', hl'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.dominates_localRings M.X Ω M.ξ M'.X Ω' M'.ξ (algebraMap Ω Ω') f hD p'
    exact ⟨p₀, congrArg Subtype.val (_root_.GlobalTheory.CompanionTheory.Ar.Centre.Sep.eq_of_dominated M M'.ξ (algebraMap Ω Ω') p' p₀ ⟨f p'.1, h'⟩ hl hl'),
      hch c hc fun j => hA _ (Algebra.subset_adjoin ⟨j, rfl⟩)⟩
  · rintro ⟨p, hpf, hp⟩
    have hl := dom_of_eq hD hpf.symm
    refine hC c hc p' fun j => ?_
    rw [← map_div₀]
    exact hl.1 _ (hp.2 j)

end Sit

section Sit

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω']
  {κ' : Type} [Finite κ'] {y : κ' → Ω'} (M' : PModel o y) (f : M'.X ⟶ M.X) (e : κ → κ')

end Sit

theorem exists_normalisation : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'], ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω') (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (algebraMap Ω Ω') ∧ Flat.NormalCpt M'.ξ ∧ IsFinite f ∧ ∀ p : Cpt M.ξ, NormAt M'.ξ f (algebraMap Ω Ω') p :=
  PositivityTheory.HtPt.Mb.LNormExists.NormEx.exists_normalisation

end GlobalTheory.CompanionTheory.Ar.NormEx
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisation =====
