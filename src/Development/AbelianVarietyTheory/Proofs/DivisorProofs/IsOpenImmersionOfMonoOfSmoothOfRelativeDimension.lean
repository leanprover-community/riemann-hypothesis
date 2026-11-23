module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFormallyUnramifiedStandardSmoothSameRelDiStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Order.CompletePartialOrder
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem etale_of_formallyUnramified_of_smoothOfRelativeDimension {X Y Z : Scheme.{0}} (f : X ⟶ Y)
    (p : Y ⟶ Z) (g : ℕ) (hp : SmoothOfRelativeDimension g p)
    (hq : SmoothOfRelativeDimension g (f ≫ p)) [FormallyUnramified f] : Etale f := by
  refine (HasRingHomProperty.iff_exists_appLE (P := @Etale)
    (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      fun R S _ _ _ r _ => RingHom.etale_algebraMap.mpr (.of_isLocalizationAway r)).left).mpr fun x => ?_
  obtain ⟨U, hU, V, hV, hxV, e, H⟩ := hp.exists_isStandardSmoothOfRelativeDimension (f x)
  obtain ⟨W, hW, hxW, e'⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ f ⁻¹ᵁ V from hxV)
  have e'' : W ≤ (f ≫ p) ⁻¹ᵁ U := e'.trans (f.preimage_mono e)
  have h1 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) (f ≫ p) hq ⟨U, hU⟩ ⟨W, hW⟩ e''
  rw [RingHom.locally_iff_isLocalization RingHom.isStandardSmoothOfRelativeDimension_respectsIso]
    at h1
  obtain ⟨s, hs, hfs⟩ := h1
  have hs' := iSup_basicOpen_of_span_eq_top _ _ hs
  have hx : x ∈ (⨆ i ∈ (s : Set Γ(X, W)), X.basicOpen i) := by rw [hs']; exact hxW
  have hx' : ∃ r ∈ s, x ∈ X.basicOpen r := by simpa using hx
  obtain ⟨r, hr, hxr⟩ := hx'
  have hloc : IsLocalization.Away r Γ(X, X.basicOpen r) := hW.isLocalization_basicOpen r
  have er : X.basicOpen r ≤ f ⁻¹ᵁ V := (X.basicOpen_le r).trans e'
  have h2 : ((f ≫ p).appLE U (X.basicOpen r)
      ((X.basicOpen_le r).trans e'')).hom.IsStandardSmoothOfRelativeDimension g := by
    rw [← (f ≫ p).appLE_map e'' (homOfLE (X.basicOpen_le r)).op]
    exact hfs r hr _
  have h3 : (f.appLE V (X.basicOpen r) er).hom.FormallyUnramified :=
    HasRingHomProperty.appLE @FormallyUnramified f inferInstance ⟨V, hV⟩
      ⟨X.basicOpen r, hW.basicOpen r⟩ er
  refine ⟨⟨V, hV⟩, ⟨X.basicOpen r, hW.basicOpen r⟩, hxr, er, ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE f p U V _ e er, CommRingCat.hom_comp] at h2
  letI := (p.appLE U V e).hom.toAlgebra
  letI := (f.appLE V (X.basicOpen r) er).hom.toAlgebra
  letI := ((f.appLE V (X.basicOpen r) er).hom.comp (p.appLE U V e).hom).toAlgebra
  haveI : IsScalarTower Γ(Z, U) Γ(Y, V) Γ(X, X.basicOpen r) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact GlobalTheory.T.etale_of_formallyUnramified_standardSmooth_same_relDim Γ(Z, U) Γ(Y, V) Γ(X, X.basicOpen r) g H h2 h3

theorem isOpenImmersion_of_mono_of_smoothOfRelativeDimension :
    ∀ (X Y Z : Scheme.{0}) (f : X ⟶ Y) (p : Y ⟶ Z) (g : ℕ), SmoothOfRelativeDimension g p →
      SmoothOfRelativeDimension g (f ≫ p) → Mono f → IsOpenImmersion f := by
  intro X Y Z f p g hp hq hf
  have : Etale f := etale_of_formallyUnramified_of_smoothOfRelativeDimension f p g hp hq
  exact IsOpenImmersion.of_flat_of_mono f

end GlobalTheory
