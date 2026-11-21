import Development.DiscreteGroups.GlobalIrreducibility.NarrowBigHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.GenericUnlinkedGLOfSegRep2
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.DepthZeroInertiaBigOfNarrowBig
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GlobalArtinReciprocity
import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.SerLocOfTiesLe
import Development.DiscreteGroups.GlobalIrreducibility.ActKEEqSelfLe
import Development.DiscreteGroups.GlobalIrreducibility.RegularLocalOfDepthZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFiberTypesAll
import Development.DiscreteGroups.GlobalIrreducibility.TameUniformizerPower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameUniformizerPowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTameCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularLocalOfDepthZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepresentationComponentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CentralOfTameCoupledStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTruthOfLabelTieStatement

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands Matrix

namespace UpperTheory.Lit.Dz

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem multi_irr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ)
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (multiProd (Equiv.sigmaUnique (Fin m) fun _ => Fin 1) fun _ : Fin m => detRep (Fin 1) χ).IsIrreducible := by
  have hd : ∑ j : Fin m, ((fun _ : Fin m => IrrGL.ofChar χ hχ) j).1 = m := by simp [IrrGL.ofChar]
  have hP : (prodIrr (fun _ : Fin m => IrrGL.ofChar χ hχ) hd).IsIrreducible :=
    GlobalTheory.RgGu.Unl.lUnlinkedIrr_nu k (GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
      PositivityTheory.RgGu.segmentRepresentation) PositivityTheory.Geo.geometricLemmaFiltration (GlobalTheory.RgGu.Nup2.nuPair k) m m
      (fun _ => Segment.single _ (IrrGL.isCusp_ofChar _ hχ)) _ hd (fun _ _ => Segment.not_linked_self _)
      (fun _ => (single_spec (IrrGL.isCusp_ofChar _ hχ)).2.1)
  let φ := multiProdEquiv (Equiv.sigmaUnique (Fin m) fun _ => Fin 1)
    (fun _ : Fin m => GlobalTheory.LocGL.equivRep (IrrRep.det (Fin 1) χ hχ))
  obtain ⟨θ⟩ := GlobalTheory.T.product_representation_reorder_equiv k m m (fun _ => 1) (Equiv.sigmaUnique (Fin m) fun _ => Fin 1)
    (stdBlocks (fun _ : Fin m => 1) hd) _ (fun _ : Fin m => (IrrGL.ofChar χ hχ).rep)
  exact (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv φ).2
    ((GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv θ).2 hP)

end UpperTheory.Lit.Dz
end
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands Matrix DiscreteGroups.sglob.DzType

namespace UpperTheory.Lit.Dz

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem genA_free (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) :
    (psOne k m).IsIrreducible ∧ IsSpherical (psOne k m) ∧ HasCentralChar (psOne k m) 1 := by
  obtain ⟨E⟩ := GlobalTheory.LocGL.DetQuot.nonempty_equiv_multiProd (k := k) (eOne m)
    (θ := fun _ : Fin m => (1 : kˣ →* ℂˣ)) (Θ := (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) (fun g => by simp)
  have h1 : IsSmoothChar (1 : kˣ →* ℂˣ) := isSmoothChar_one
  refine ⟨(GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv E).2 (multi_irr k m 1 h1), ?_, ?_⟩
  · obtain ⟨f, hf, hf1⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (eOne m)
      (ρ := ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) (x := (1 : ℂ)) fun g _ => by simp
    show fixed (parInd (eOne m) (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ))) (GlobalTheory.SplitWeil.KO k (Fin m)) ≠ ⊥
    intro hbot
    have h0 : f ∈ (⊥ : Submodule ℂ _) := hbot ▸ hf
    rw [Submodule.mem_bot] at h0
    rw [h0] at hf1
    exact absurd hf1 (by simp)
  · have hc : HasCentralChar (multiProd (eOne m) fun _ : Fin m => detRep (Fin 1) (1 : kˣ →* ℂˣ)) 1 := by
      intro z f
      rw [GlobalTheory.BoundaryMaps.multiProd_scalar (eOne m) _ (fun _ => (1 : kˣ →* ℂˣ))
        (fun _ => by simpa using GlobalTheory.BoundaryMaps.hasCentralChar_detRep (k := k) 1 (1 : kˣ →* ℂˣ)) z f]
      simp
    exact GlobalTheory.LocGL.hasCentralChar_of_equiv E.symm hc

theorem genSph : GenSph := by
  intro E _ _ w g _ i hi ψ₀ _ ψ hψc hL m
  obtain ⟨hirr, hsph, hcen⟩ := genA_free (w.adicCompletion E) m
  let τ₀ : IrrRep (GL (Fin m) (w.adicCompletion E)) :=
    ⟨PS (w.adicCompletion E) m, psOne (w.adicCompletion E) m, isSmooth_parInd _ _, hirr⟩
  refine ⟨τ₀, 1, ?_, hcen, ?_⟩
  · obtain ⟨φ⟩ := IrrRep.nonempty_equiv_rep τ₀
    exact fixed_ne_bot_of_equiv' φ.symm hsph
  · obtain ⟨l, hl, hlv⟩ := exists_cell_functional (lowS_one i hi m) (lowS_KO i hi m) (lowS_upper i hi m)
      (lowS_diag i hi m) ψ hψc (psi_of_lifts i hi hL)
    exact ⟨l, cellVec (lowS_one i hi m) (lowS_diag i hi m), hl, hlv, fun x hx =>
      cellVec_fixed (lowS_one i hi m) (lowS_diag i hi m) ⟨x, hx, rfl⟩⟩

theorem narrowBig (art : GlobalTheory.Published.GlobalArtinReciprocity) (hL : GlobalTheory.Published.LocalLanglandsGL) : NarrowBig :=
  narrowBig_of lCusp lDepth lTame
    (lMatchBig_of lCusp lDepth (lOneOf (lTameRec art GlobalTheory.T.chevalley_units)) (lPin_of_dig dig) lKondo (lFinPair lFE) lPsi genSph
      (lRed DiscreteGroups.sglob.LConv.cuspGen) lTw (galEps_of_art (fun L Ω _ _ _ _ _ A v h => by
        obtain ⟨rc, ⟨a, ha, -⟩, -⟩ := hL.1 L Ω A v h
        exact ⟨a, ha⟩) (lTameRec art GlobalTheory.T.chevalley_units)))

end UpperTheory.Lit.Dz
end
end

section
namespace UpperTheory.Lit.Dz

theorem big (hL : GlobalTheory.Published.LocalLanglandsGL) : DiscreteGroups.sglob.DzType.DepthZeroInertiaBig :=
  depthZeroInertiaBig_of_narrowBig (narrowBig PositivityTheory.Stage1.PM.globalArtinReciprocity hL)
    PositivityTheory.Stage1.PM.globalArtinReciprocity hL

end UpperTheory.Lit.Dz
end
