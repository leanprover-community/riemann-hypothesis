module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientOfFiniteGroup
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverTargetOfIsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExistsIffTopExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionToNormalization

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

noncomputable section
namespace GlobalTheory.EqModel

theorem isProjOver_pi_const {R : Type} [CommRing R] (κ : Type) [Finite κ] (A : Over (Sp R))
    (h : IsProjOver A.hom) : IsProjOver (∏ᶜ fun _ : κ => A).hom := by
  let n := Nat.card κ
  let e : κ ≃ Fin n := Finite.equivFin κ
  let I₁ : (∏ᶜ fun _ : κ => A) ≅ ∏ᶜ fun _ : Fin n => A := (Pi.reindex e.symm (fun _ : κ => A)).symm
  let I₂ : (∏ᶜ fun _ : Fin n => A) ≅ ReciprocityTheory.ChartRestriction.G.Out.powObj A n :=
    (limit.isLimit _).conePointUniqueUpToIso (ReciprocityTheory.ChartRestriction.G.Out.powIsLimit A n)
  have : IsIso (I₁ ≪≫ I₂).hom.left := ((Over.forget _).mapIso (I₁ ≪≫ I₂)).isIso_hom
  have hp := Models.FamInh.isProjOver_powObj A h n
  have e' := ProjSpace.isProjOver_comp_of_isClosedImmersion (I₁ ≪≫ I₂).hom.left hp
  rwa [Over.w] at e'

theorem isOpenImmersion_toNormalization {V P X : Scheme.{0}} (c : V ⟶ P) (p : P ⟶ X) [IsSeparated p]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact c] [QuasiSeparated c] (h : c ≫ p = j) :
    IsOpenImmersion c.toNormalization := by
  first
  | (rename_i h_5 h_7 h_8 h_9; revert V P X c p h_5 j h_7 h_8 h_9 h; exact @_root_.GlobalTheory.NormalizationOpenImmersion.main)
  | exact @_root_.GlobalTheory.NormalizationOpenImmersion.main
  | exact _root_.GlobalTheory.NormalizationOpenImmersion.main
  | (apply _root_.GlobalTheory.NormalizationOpenImmersion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormalizationOpenImmersion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormalizationOpenImmersion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormalizationOpenImmersion.main ..)

theorem isQProjOver_of_isProjOver' {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsQProjOver f := by
  obtain ⟨N, i, _, e⟩ := h
  exact ⟨N, i, inferInstance, inferInstance, e⟩

theorem exists_projective_quotient {F : Type} [Field F] {X : Scheme.{0}} (s : X ⟶ Sp F) {Γ : Type}
    [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (hs : IsProjOver s) (hρ : ∀ g, (ρ g).asIso.hom ≫ s = s) :
    ∃ (W : Scheme.{0}) (q : X ⟶ W) (sW : W ⟶ Sp F), IsAffineQuotient ρ q ∧ q ≫ sW = s ∧
      IsProjOver sW ∧ IsFinite q ∧ Surjective q := by
  have := OrbitsInAffineOpens.of_isQProjOver (isQProjOver_of_isProjOver' hs) ρ
  obtain ⟨W, q, hq⟩ := QuotientGluing.exists_isAffineQuotient ρ
  have hqs := hq.comp_desc s hρ
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hs).1
  have : IsProper (q ≫ hq.desc s hρ) := by rw [hqs]; infer_instance
  have : LocallyOfFiniteType (q ≫ hq.desc s hρ) := by rw [hqs]; infer_instance
  have : IsProper (hq.desc s hρ) := hq.isProper _
  obtain ⟨L, hL⟩ := GaloisQuotient.exists_isAmpleLB_of_isAffineQuotient hq
    (isQProjOver_of_isProjOver' hs)
  exact ⟨W, q, hq.desc s hρ, hq, hqs, hL.isProjOver _, hq.isFinite (hq.desc s hρ), hq.surjective⟩

end GlobalTheory.EqModel
