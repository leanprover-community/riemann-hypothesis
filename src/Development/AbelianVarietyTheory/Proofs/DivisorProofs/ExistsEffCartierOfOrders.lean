module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CodimOneGenerizationStalk
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Poinc.TraitGlue

theorem dvd_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] {a b : A}
    (ha : a ≠ 0) (h : ∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      algebraMap A (Localization.AtPrime P) a ∣ algebraMap A (Localization.AtPrime P) b) : a ∣ b := by
  have ha' : algebraMap A (FractionRing A) a ≠ 0 := fun e =>
    ha (IsFractionRing.injective A (FractionRing A) (e.trans (map_zero _).symm))
  obtain ⟨c, hc⟩ := KrullAlg.mem_range_of_forall_height_one (A := A)
    (algebraMap A (FractionRing A) b / algebraMap A (FractionRing A) a) (fun P hP h1 => by
      obtain ⟨c, hc⟩ := h P h1
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
      have e : algebraMap A (Localization.AtPrime P) (s * b) = algebraMap A (Localization.AtPrime P) (a * r) := by
        rw [map_mul, map_mul, hc, mul_left_comm, IsLocalization.mk'_spec']
      have e' : s * b = a * r := IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors e
      refine ⟨s, s.2, r, ?_⟩
      rw [← mul_div_assoc, ← map_mul, e', map_mul, mul_div_cancel_left₀ _ ha'])
  refine ⟨c, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, hc, mul_div_cancel₀ _ ha']

theorem dvd_of_generisations {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (x : X)
    {a b : X.presheaf.stalk x} (ha : a ≠ 0)
    (h : ∀ (η : X) (hη : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
      (X.presheaf.stalkSpecializes hη).hom a ∣ (X.presheaf.stalkSpecializes hη).hom b) : a ∣ b := by
  have := (hX x).2
  refine dvd_of_height_one ha fun q _ hq => ?_
  let y : PrimeSpectrum (X.presheaf.stalk x) := ⟨q, inferInstance⟩
  obtain ⟨e, he⟩ := LocalRingGeneralisation.stalk_fromSpecStalk_equiv X x q
  have hs : X.fromSpecStalk x y ⤳ x := by
    have : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hcomp : ∀ t, e ((X.presheaf.stalkSpecializes hs).hom t) = algebraMap _ (Localization.AtPrime q) t := by
    intro t
    obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq t
    have h3 := congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU hs)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
    erw [h3]
    exact he U _ hxU s
  rw [← hcomp, ← hcomp]
  refine map_dvd e (h _ hs ?_)
  rw [ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
  rfl

theorem finite_dim_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {W : X.Opens} (hW : IsAffineOpen W)
    (V : X.Opens) {z : X} (hzW : z ∈ W) (hzV : z ∈ V) :
    {η : X | η ∈ W ∧ ringKrullDim (X.presheaf.stalk η) = 1 ∧ η ∉ V}.Finite := by
  obtain ⟨a, haV, hza⟩ := hW.exists_basicOpen_le ⟨z, hzV⟩ hzW
  have : Nonempty W := ⟨⟨z, hzW⟩⟩
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hza
  have hfin := (KrullAlg.finite_height_one ha).preimage
    (f := fun p : PrimeSpectrum Γ(X, W) => p.asIdeal) (fun _ _ _ _ e => PrimeSpectrum.ext e)
  refine (hfin.image (fun p => hW.fromSpec p)).subset ?_
  rintro η ⟨h1, h2, h3⟩
  letI : Algebra Γ(X, W) (X.presheaf.stalk η) := X.presheaf.algebra_section_stalk ⟨η, h1⟩
  haveI := hW.isLocalization_stalk ⟨η, h1⟩
  refine ⟨hW.primeIdealOf ⟨η, h1⟩, ⟨inferInstance, ?_, ?_⟩, hW.fromSpec_primeIdealOf ⟨η, h1⟩⟩
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hW.primeIdealOf ⟨η, h1⟩).asIdeal] at h2
    exact_mod_cast h2
  · by_contra hn
    refine h3 (haV ((X.mem_basicOpen a η h1).2 ?_))
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk η) (hW.primeIdealOf ⟨η, h1⟩).asIdeal a).2 hn

theorem associated_of_map {A V : Type} [CommRing A] [IsDomain A] [ValuationRing A] [CommRing V] [IsDomain V]
    (φ : A →+* V) [IsLocalHom φ] {a b : A} (h : Associated (φ a) (φ b)) (ha : φ a ≠ 0) : Associated a b := by
  have key : ∀ {a c : A}, Associated (φ a) (φ (a * c)) → φ a ≠ 0 → Associated a (a * c) := by
    intro a c h ha
    rw [map_mul] at h
    have : IsUnit (φ c) := isUnit_of_associated_mul h.symm ha
    exact (associated_mul_unit_left _ _ (isUnit_of_map_unit φ c this)).symm
  rcases ValuationRing.dvd_total a b with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact key h ha
  · exact (key h.symm (h.ne_zero_iff.1 ha)).symm

theorem valuationRing_stalk {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (η : X)
    (h : ringKrullDim (X.presheaf.stalk η) = 1) : ValuationRing (X.presheaf.stalk η) := by
  have := (hX η).2
  have hle : Ring.KrullDimLE 1 (X.presheaf.stalk η) := by
    rw [Ring.krullDimLE_iff, h]
    norm_num
  have : Ring.DimensionLEOne (X.presheaf.stalk η) := by
    refine ⟨fun {p} hp hprime => ?_⟩
    rcases Ring.krullDimLE_one_iff.mp hle p hprime with h | h
    · rw [IsDomain.minimalPrimes_eq_singleton_bot] at h
      exact absurd h hp
    · exact h
  have : IsDedekindDomain (X.presheaf.stalk η) :=
    (isDedekindDomain_iff _ (FractionRing (X.presheaf.stalk η))).mpr
      ⟨inferInstance, inferInstance, inferInstance, fun {y} hy => IsIntegrallyClosed.isIntegral_iff.mp hy⟩
  have h2 := (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk η)).out 3 2
  exact h2.1 this

theorem specializes_germ {X : Scheme.{0}} {W : X.Opens} {x η : X} (h : η ⤳ x) (hx : x ∈ W) (hη : η ∈ W) (s : Γ(X, W)) :
    (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ W x hx).hom s) = (X.presheaf.germ W η hη).hom s :=
  congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hx h)

end GlobalTheory.Poinc.TraitGlue
