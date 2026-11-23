module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmEqMapGm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedSectionOffClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameOfSectionUnitsOnClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleRigidLinearisationsSameLocalStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum



theorem exists_carried_frame_off_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact y hy
  have hβc : IsClosedMap β.base := by
    haveI : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hF.2.2
    haveI : IsFinite β := MorphismProperty.of_isPullback (P := @IsFinite) hβ.1.flip inferInstance
    exact β.isClosedMap
  obtain ⟨V, hyV, s, hs, hun, hcar⟩ := GlobalTheory.T.exists_carried_section_off_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact y hy
  obtain ⟨V', hyV', -, T, hT, htr⟩ := GlobalTheory.T.exists_lineBundleFrame_of_section_units_on_closedFibre _ _ β hβc U'.LG.L U'.LG.isLB V s hs y hyV hun
  refine ⟨V', hyV', T, hT, ?_⟩
  intro σ h bc hbc hP hPO
  refine (hcar σ).elim fun h₀ hc => hc.elim fun bc₀ hc => ?_
  refine hc.2.elim fun hP₀ hc' => ?_
  have hF₀ := htr _ _ hc'.2
  have e : bc₀.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) =
      bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) := hc.1.trans hbc.symm
  have s₁ := Classical.choose_spec hP.lg
  have s₀ := Classical.choose_spec hP₀.lg
  refine s₁.2.elim fun he₁ m₁ => s₀.2.elim fun he₀ m₀ => ?_
  have hg := GlobalTheory.T.uniformisationBundle_rigidLinearisations_same_localUnits R' D' A' G' hS' U' (specOf (Gal.hom σ)) _ _ e he₀ he₁ _ _ s₀.1 s₁.1 m₀.1 m₁.1
  intro z j k hz hfz hzk hfzj
  have h1 := hF₀ z j k hz (by rw [e]; exact hfz) hzk (by rw [e]; exact hfzj)
  rw [hg z j k hzk (by rw [e]; exact hfzj)] at h1
  rw [e] at h1
  exact h1

end GlobalTheory.Mum
