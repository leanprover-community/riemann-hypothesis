import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResKOfResolutionPrincipalisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrictStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIntegralBlowupOfSmooth

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.ResK ReciprocityTheory.AnForm.R

namespace PositivityTheory.ResPlug

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

def ResW : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (M D : ℕ) (X : Scheme.{0}) (i : X ⟶ PSpace K M) (U : X.Opens),
    IsResInput M i U D →
    ∃ (X₁ : Scheme.{0}) (s : X₁ ⟶ X),
      IsProjOver (s ≫ i ≫ PSpace.str K M) ∧ Smooth (s ≫ i ≫ PSpace.str K M) ∧ IsIso (s ∣_ U) ∧
        Dense ((s ⁻¹ᵁ U : X₁.Opens) : Set X₁)

def PrincW : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp K),
    SmoothOfRelativeDimension d g → IsProjOver g → ∀ U : X.Opens, Dense (U : Set X) →
    ∃ (X' : Scheme.{0}) (s : X' ⟶ X),
      IsProjOver (s ≫ g) ∧ Smooth (s ≫ g) ∧ IsIso (s ∣_ U) ∧ FinalTheorems.Snc (preRed s (U : Set X)ᶜ U.isOpen.isClosed_compl)



theorem resK_of_weak (H₁ : ResW) (H₂ : PrincW) : ResKStatement := by
  intro K _ _ M D X i U hin
  obtain ⟨X₁, s, hproj₁, hsm₁, hiso₁, hd₁⟩ := H₁ K M D X i U hin
  obtain ⟨hi, hred, hdense, hU⟩ := hin
  have hD₁ : SmoothOfRelativeDimension D (s ≫ i ≫ PSpace.str K M) :=
    relDim_of_dense _ _ hd₁ (relDim_preimage s _ U hU)
  obtain ⟨X₂, t, hproj₂, hsm₂, hiso₂, hsnc₂⟩ := H₂ K D X₁ (s ≫ i ≫ PSpace.str K M) hD₁ hproj₁ (s ⁻¹ᵁ U) hd₁
  have hiso : IsIso ((t ≫ s) ∣_ U) := by
    rw [morphismRestrict_comp]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ hiso₂ hiso₁
  have hT : IsClosed ((t ≫ s).base ⁻¹' (U : Set X)ᶜ) :=
    U.isOpen.isClosed_compl.preimage (t ≫ s).base.hom.continuous
  have hsncT : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal ⟨_, hT⟩) := hsnc₂
  have hd₂ : Dense (((t ≫ s) ⁻¹ᵁ U : X₂.Opens) : Set X₂) := by
    exact Dense.mono (fun x hx => by simpa using hx) (dense_compl_of_snc _ hsncT)
  have hproj₂' : IsProjOver (t ≫ s ≫ i ≫ PSpace.str K M) := hproj₂
  have : CompactSpace X₂ := by
    have hP₂ := isProper_of_isProjOver hproj₂'
    exact QuasiCompact.compactSpace_of_compactSpace (t ≫ s ≫ i ≫ PSpace.str K M)
  have hsm : Smooth ((t ≫ s) ≫ i ≫ PSpace.str K M) := by simpa using hsm₂
  obtain ⟨hDim, hC⟩ := GlobalTheory.T.coords_statement K D X₂ ((t ≫ s) ≫ i ≫ PSpace.str K M) ((t ≫ s) ⁻¹ᵁ U) _ hT inferInstance hsm hd₂
    (relDim_preimage (t ≫ s) _ U hU) hsncT
  obtain ⟨r, j, hj, e⟩ := exists_closed_in_prod ((t ≫ s) ≫ i) (by simpa using hproj₂')
  exact ⟨r, X₂, j, t ≫ s, hj, e, hDim, hiso, hd₂, hC⟩






def PrincNeed : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (Y : Scheme.{0}) (f : Y ⟶ Sp k),
    IsIntegral Y → SmoothOfRelativeDimension d f → IsProjOver f →
    ∀ I : Y.IdealSheafData, I ≠ ⊥ →
      ∃ (Y' : Scheme.{0}) (s : Y' ⟶ Y),
        IsIntegral Y' ∧ SmoothOfRelativeDimension d (s ≫ f) ∧ IsProjOver (s ≫ f) ∧
        IsIso (s ∣_ I.support.compl) ∧ FinalTheorems.EffCartier (I.comap s)

def WeakResNeed : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W] (p : W ⟶ Sp F) (n : ℕ), IsProjOver p →
    topologicalKrullDim W = n →
    ∃ (W' : Scheme.{0}) (s : W' ⟶ W) (U : W.Opens), IsIntegral W' ∧ SmoothOfRelativeDimension n (s ≫ p) ∧
      IsProjOver (s ≫ p) ∧ (U : Set W).Nonempty ∧ IsIso (s ∣_ U)

def GenSmoothDim : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W] (p : W ⟶ Sp F) (n : ℕ), IsProjOver p →
    topologicalKrullDim W = n → ∃ U : W.Opens, (U : Set W).Nonempty ∧ SmoothOfRelativeDimension n (U.ι ≫ p)


theorem isIso_ι_restrict {W : Scheme.{0}} (U : W.Opens) : IsIso (U.ι ∣_ U) := by
  have : Surjective (U.ι ∣_ U) := ⟨fun x => by
    refine ⟨⟨⟨x.1, x.2⟩, x.2⟩, U.ι.isOpenEmbedding.injective ?_⟩
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun f : (U.ι ⁻¹ᵁ U).toScheme ⟶ W => f _) (morphismRestrict_ι U.ι U)).trans rfl)⟩
  exact (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, this⟩






end PositivityTheory.ResPlug
