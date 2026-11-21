import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaximalIdealIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfIsOfFinOrderOfCharpoly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullDegreeLabelForcesTrivialWildInertia

section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem isToricElt_of_isLamTie : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D), Z.Ok →
    IsLamTie X Z → IsToricElt X ∧ ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s := by
  intro D N X Z hZ h
  refine ⟨fun i hi => ?_, fun i hi lam => ?_⟩
  · obtain ⟨hS, ι, hι, hl⟩ := h i hi
    refine ⟨ι, hι, fun lam s hs => ?_⟩
    obtain ⟨j, a, s', ⟨-, hs', hv⟩, u, hu, hQ⟩ := hl lam
    obtain rfl : s = s' := by
      have h1 := hs.1
      have h2 := hs'.1
      omega
    have h1 : 1 ≤ s := by exact_mod_cast hs.2.1
    exact ⟨_, inferInstance, phi D.host, Z.kap j a s, cond0 D.host Z.w0, Z.lam0 (X.l i) j a, u,
      GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (X.l i) j a s h1 hs.2.2, hS, hv, hu, hQ⟩
  · obtain ⟨-, ι, -, hl⟩ := h i hi
    obtain ⟨j, a, s, ⟨-, hs, -⟩, -⟩ := hl lam
    exact ⟨s, hs⟩

end GlobalTheory.LamTie
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000

namespace GlobalTheory.TwGalInputs

theorem galois_inputs : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (G : GalSide D), GlobalTheory.TripleLocal.GalHodge D G.wd → BlochKatoReduction.adm1 (BlochKatoReduction.bk0 D) ∧ BlochKatoReduction.adm2 D ∧ BlochKatoReduction.adm8 D ∧ AllGood D.nexp ∧ D.nexp.sig_all ∧ (∃ N0, BlochKatoReduction.adm9 D N0) ∧ BlochKatoReduction.adm10 D ∧ ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i := by
  intro hC hArt hTor D G hGH
  have h2 : BlochKatoReduction.adm2 D := GlobalTheory.TripleAdm.adm2_of_isTriple D G.triple (GlobalTheory.T.full_degree_label_forces_trivial_wild_inertia D G.wd G.lab)
  have hF : GlobalTheory.TypeLeaf.FrobDense D :=
    GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 hC)
  have hg := GlobalTheory.TripleLocal.galois_hypotheses_of_isTriple G.chr hF hGH h2 G.triple
  have hs := GlobalTheory.Triple.satake_identity_of_isTriple D G.triple
  have hL := GlobalTheory.LamTie.isToricElt_of_isLamTie D _ D.ntw G.lam G.lamOk G.lamTie
  obtain ⟨N0, h9, h10, -⟩ := GlobalTheory.ToricAssembly.toric_properties hArt hTor D hL.1
  exact ⟨hg.1, h2, hg.2.1, hs.2.1, hs.2.2, ⟨N0, h9⟩, h10,
    GlobalTheory.SettingHypotheses.setHyp_of_isTriple_of_galHodge hC D G.wd G.cf G.chr hGH h2 G.triple G.lam G.lamOk G.lamTie G.rank G.primes⟩

end GlobalTheory.TwGalInputs
end
