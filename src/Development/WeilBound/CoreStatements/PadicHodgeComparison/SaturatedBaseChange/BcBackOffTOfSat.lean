module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedPairLineIff

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.LFun GlobalTheory.PRep Formalism.UG
open GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

def CompUnique : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ σ τ : LocIrr w n,
      IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ →
      IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → Nonempty (σ.ρ.Equiv τ.ρ)

def OneFactor : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (h : ∑ _i : Fin 1, 1 * n = n) (ρ : LocIrr w n) (σ : Fin 1 → LocIrr w (1 * n)),
      GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of ρ.ρ ρ.smooth ρ.irred) 1 (σ 0).ρ →
      Nonempty ((locProd (N := fun _ : Fin 1 => 1 * n) h w σ).Equiv ρ.ρ)

end PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

end
