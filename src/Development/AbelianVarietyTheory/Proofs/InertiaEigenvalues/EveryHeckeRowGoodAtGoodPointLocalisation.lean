import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGoodRowPointGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlaceStatement

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ExhaustRows

theorem main : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → SumRepresentations.Conclusion42 D → GoodFTAll D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), HG D.nd D.naut i' ∧ AtM D.nd D.naut i' σ := by
  intro D M hT hA Tn hS h42 hG i σ hne
  have hg : D.nd.goodRow σ := hG σ
  obtain ⟨P, hP⟩ := ((h42 i) σ hne).1.2
  obtain ⟨i', hi', P', x', hth, hx⟩ := GlobalTheory.T.theta_lift_has_point_at_localisation_same_place D M hT hA Tn hS i σ P hP
  obtain ⟨hxg, hat⟩ := GlobalTheory.T.thetaLift_goodRow_point_good D h42 i' σ P' x' hg hth hx
  exact ⟨hg, i', hi', ⟨x', hxg⟩, hat⟩

end GlobalTheory.ExhaustRows
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.every_heckeRow_good_at_goodPointLocalisation : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → SumRepresentations.Conclusion42 D → GoodFTAll D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), HG D.nd D.naut i' ∧ AtM D.nd D.naut i' σ := by
  atlas_forward_decl GlobalTheory.ExhaustRows.main
