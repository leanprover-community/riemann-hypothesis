import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveOfAdjointSeparatesLabelledParts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterInjectivePlacewise
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamAddSmulOfAgreeOffSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLValuesNonvanishing
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMatrixCoefficientEqZeroOfHeisenbergRelations
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFiniteDatumIsSchwartzBruhatHalf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMoveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZeroStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpanFullSphericalHeckeEigenpart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainEigenPartHasHeckeParametersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCuspSpaceFiniteDimOfHarishChandra
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainFockVectorLevelLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamsTrivialBoundRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParametersLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeParametersOfElementFromOneNonzeroValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainAdjointNonvanishingStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsAdjointOfRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsNeZeroOfLValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLocalZetaNonvanishingOfReal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainRealZetaNonvanishing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanThetaCorrespondenceTowersRealData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsInCuspSpan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardInductionFixedMetric

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChainHeckeParameter_injective_placewise : ∀ (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)), chainPar c B k w = chainPar c B' k w → B w = B' w := by
  first | exact @GlobalTheory.ChainOnto.chainPar_inj | exact GlobalTheory.ChainOnto.chainPar_inj | (intros; apply GlobalTheory.ChainOnto.chainPar_inj <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainHeckeParam_add_smul_of_agree_off_set : ∀ (D : D7) (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' → (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) → u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B := by
  first | exact @GlobalTheory.ChainOnto.isPar_add_smul | exact GlobalTheory.ChainOnto.isPar_add_smul | (intros; apply GlobalTheory.ChainOnto.isPar_add_smul <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem ontoAll_of_chainUp : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ChainUp D → OntoAll D := by
  intro D hFin hMet hEig hInd hUp hGap c hc s₀ hs₀ k hk s Θ hR
  obtain ⟨hs, hadj⟩ := hUp hGap c hc s₀ hs₀ k hk s Θ hR
  obtain ⟨ipD₀, ip₀, hm₀⟩ := hMet c hc 0 (Nat.zero_le _) s₀ hs₀
  obtain ⟨ipD, ip, hm⟩ := hMet c hc k hk s hs
  haveI : FiniteDimensional ℂ (s₀.CC c) := hFin c hc 0 (Nat.zero_le _) s₀ hs₀
  let Sab := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
  let R : GlobalTheory.LFun.Fam D.host.E → GlobalTheory.LFun.Fam D.host.E → Prop := fun B B' => ∀ w ∉ Sab, B w = B' w
  have hRe : Equivalence R :=
    ⟨fun _ _ _ => rfl, fun h w hw => (h w hw).symm, fun h h' w hw => (h w hw).trans (h' w hw)⟩
  have hlin₀ := GlobalTheory.T.thetaChainHeckeParam_add_smul_of_agree_off_set D c s₀
  refine GlobalTheory.T.surjective_of_adjoint_separates_labelled_parts (s₀.CC c) (s.CC c) (GlobalTheory.LFun.Fam D.host.E) (GlobalTheory.LFun.Fam D.host.E) ip₀ ip Θ
    (fun u B => IsPar u B) (fun x B => IsPar x B) R R (fun B => chainPar c B k)
    hm₀.herm hm₀.pos hm.pos hRe (hEig c hc 0 (Nat.zero_le _) s₀ hs₀) hlin₀.1 hlin₀.2 ?_ ?_ ?_
  · intro B B' h w hw
    exact GlobalTheory.T.thetaLiftChainHeckeParameter_injective_placewise D c k B B' w (h w hw)
  · intro ι x B hx hne
    refine hInd c hc k hk s hs ι x B hx ?_
    intro i i' hii'
    have := hne i i' hii'
    by_contra hcon
    push_neg at hcon
    exact this hcon
  · intro u B hu
    exact hadj ipD₀ ip₀ ipD ip hm₀ hm u B hu

end GlobalTheory.ChainOnto
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChain_surjective_of_adjoint_nonvanishing : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ChainUp D → OntoAll D := by
  atlas_forward_decl GlobalTheory.ChainOnto.ontoAll_of_chainUp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_LValues_nonvanishing : ∀ D : D7, ChainLW D := by
  first | exact @GlobalTheory.ChainOnto.chainLW_holds | exact GlobalTheory.ChainOnto.chainLW_holds | (intros; apply GlobalTheory.ChainOnto.chainLW_holds <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Classical

namespace GlobalTheory.ChainOnto.CoefSuppPf

theorem coefSupp : ∀ D : D7, CoefSupp D := by
  intro D _hgap c hc k _hk s s' hs hs' p hp m X hX φ g hg hnot
  obtain ⟨ξ, f₀, hvec⟩ := hp.vec
  have hthf : IsThetaFunO c.ψ s.V s'.V p.f := GlobalTheory.VecTheta.isThetaFunO_stepVec hvec
  obtain ⟨_hvac, e, he, hth⟩ := hvec
  obtain ⟨hr, ξL, hL⟩ := hs.lev
  have hQ : s.L.Q = ∅ := by rw [hL]; rfl
  have hPg : s.L.Pg = c.Pg := by rw [hL]; rfl
  have hrank : s.V.rank ≤ s'.V.rank := by
    rw [hs.rank, hs'.rank]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ k)) _
  have hint : ∀ v, (∀ PP ∈ s.L.Pg, PP.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v := by
    intro v hv
    apply hg v
    intro hmem
    simp only [Com.S, Finset.mem_image] at hmem
    obtain ⟨PP, hPP, hPPv⟩ := hmem
    exact hv PP (hPg ▸ hPP) hPPv
  have hsupp := fun x hx => by_contra fun h => hnot
    (GlobalTheory.T.finitePart_mem_level_of_thetaDatum_ne_zero D s.V s'.V s.Λ s.β s'.β s.L (c.chi (k + 1)) ξ e hs.selfDual hs.frame hrank hQ he g hint x hx h)
  have hsb := GlobalTheory.T.thetaChainStep_finiteDatum_isSchwartzBruhat_half D s.V s'.V s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ξ (s.L.Pg ∪ ∅) e
    hs.selfDual hs'.selfDual hs.frame hs'.frame he
  obtain ⟨n, a, y, hy, h1, h2⟩ := GlobalTheory.T.heisenberg_fix_and_kill_theta_off_support_move D c.ψ s.V s'.V hc.std s.Λ s'.Λ hs.selfDual hs'.selfDual
    (s.L.Pg ∪ ∅) e he f₀ _ p.f hsb hth g hsupp
  obtain ⟨H1, -⟩ := GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D c.ψ c.θ s.V s'.V hc.std hc.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n a y (fun i => (hy i).1) φ
  obtain ⟨H2, H0⟩ := GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D c.ψ c.θ s.V s'.V hc.std hc.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n (fun i => conj (a i)) (fun i => actO s.V s'.V g⁻¹ 1 (-(y i))) (fun i => (hy i).2) φ
  have R1 : ∑ i, a i • heisO c.ψ s.V s'.V (y i) (p.pt φ) = p.pt φ := by
    show ∑ i, a i • heisO c.ψ s.V s'.V (y i) (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H1, h1]
    rfl
  have R2 : ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i))) (p.pt φ) = 0 := by
    show ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i)))
      (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H2, h2, H0]
  exact GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations D c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω hp.weil m X hX (p.pt φ) (hp.theta φ) g n a y R1 R2

end GlobalTheory.ChainOnto.CoefSuppPf
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainCoef_vanishes_off_level : ∀ D : D7, CoefSupp D := by
  atlas_forward_decl GlobalTheory.ChainOnto.CoefSuppPf.coefSupp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicitySpace_span_fullSphericalHecke_eigenparts : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → LevFacts D → ForStage D fun c _ s => Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e} = ⊤ := by
  first | exact @GlobalTheory.OntoDecomp.multT_span_partFull | exact GlobalTheory.OntoDecomp.multT_span_partFull | (intros; apply GlobalTheory.OntoDecomp.multT_span_partFull <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem eigSpan_of_parts : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → MetEx D → LevFacts D → EigSpan D := by
  intro hC D hF _ hL c hc j hj s hs
  have hspan := GlobalTheory.T.multiplicitySpace_span_fullSphericalHecke_eigenparts hC D hF hL c hc j hj s hs
  have hpar := GlobalTheory.T.thetaChain_eigenPart_has_heckeParameters hC D c hc j hj s hs
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.2 ?_
  rintro u ⟨e, he⟩
  by_cases h0 : u = 0
  · rw [h0]; exact Submodule.zero_mem _
  · exact Submodule.subset_span ((hpar u e he).1 h0)

end GlobalTheory.ChainOnto
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_space_spanned_by_satake_eigen_elements : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → MetEx D → LevFacts D → EigSpan D := by
  atlas_forward_decl GlobalTheory.ChainOnto.eigSpan_of_parts
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainCuspSpaceFiniteDim_of_harishChandra : GlobalTheory.Published.HarishChandraFinite → ∀ D : D7, LevFacts D → FinDim D := by
  first | exact @GlobalTheory.ChainOnto.finDim_of_levFacts | exact GlobalTheory.ChainOnto.finDim_of_levFacts | (intros; apply GlobalTheory.ChainOnto.finDim_of_levFacts <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainInnerProductsExist_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  first | exact @GlobalTheory.ChainMetric.metEx | exact GlobalTheory.ChainMetric.metEx | (intros; apply GlobalTheory.ChainMetric.metEx <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem parBoundW_of_parBound {D : D7} (h : ParBound D) : ParBoundW D := by
  intro c hc j hj s hs u B hu
  exact GlobalTheory.LiftPole.Bounded.mono (h c hc j hj s hs u B hu) (by linarith)

theorem parBoundW (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) (hL : LevFacts D) : ParBoundW D :=
  parBoundW_of_parBound (GlobalTheory.T.thetaChain_heckeParams_trivialBound_rapidDecay hP D hL)

end GlobalTheory.ChainOnto
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_chain_occurring_params_norm_half_rank_bound : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LevFacts D → ParBoundW D := by
  atlas_forward_decl GlobalTheory.ChainOnto.parBoundW
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChain_adjoint_nonvanishing_step : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  first | exact @GlobalTheory.ChainOnto.stepUp | exact GlobalTheory.ChainOnto.stepUp | (intros; apply GlobalTheory.ChainOnto.stepUp <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftUpwardsAdjoint_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdj D := by
  first | exact @GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay | exact GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay | (intros; apply GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftUpwards_ne_zero_of_lValue : ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → MetEx D → LevFacts D → ZetaNe D → UpNe D := by
  first | exact @GlobalTheory.ChainOnto.upNe_of_heckeForm | exact GlobalTheory.ChainOnto.upNe_of_heckeForm | (intros; apply GlobalTheory.ChainOnto.upNe_of_heckeForm <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainLocalZetaNonvanishing_of_real : ∀ D : D7, MetEx D → LevFacts D → LevelLaw D → CoefSupp D → RealZeta D → ZetaNe D := by
  first | exact @GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real | exact GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real | (intros; apply GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftUpwards_in_cuspSpan : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.ChainOnto.LevFacts D → GlobalTheory.ChainOnto.LevelLaw D → GlobalTheory.ChainOnto.UpSpan D := by
  first | exact @GlobalTheory.ChainOnto.upSpan_of | exact GlobalTheory.ChainOnto.upSpan_of | (intros; apply GlobalTheory.ChainOnto.upSpan_of <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem ontoAll_of_classicalTheorems : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → UpPar D → OntoAll D := by
  intro hHCF hCRD hDSC hHCM hCW D hHF hUP
  have hLF : LevFacts D := GlobalTheory.T.thetaChain_level_properties D
  have hFD : FinDim D := GlobalTheory.T.thetaChainCuspSpaceFiniteDim_of_harishChandra hHCF D hLF
  have hMet : MetEx D := GlobalTheory.T.thetaChainInnerProductsExist_of_rapidDecay hCRD D
  have hES : EigSpan D := GlobalTheory.T.multiplicity_space_spanned_by_satake_eigen_elements hCRD D hFD hMet hLF
  have hPI : ParIndep D := GlobalTheory.T.thetaChain_heckeParameters_linearIndependent D
  have hPOV : ParOfVal D := GlobalTheory.T.hecke_parameters_of_element_from_one_nonzero_value hCRD D hMet hLF
  have hPB : ParBoundW D := GlobalTheory.T.theta_chain_occurring_params_norm_half_rank_bound hCRD D hLF
  have hLL : LevelLaw D := GlobalTheory.T.thetaLiftChain_fockVector_levelLaws D
  have hCS : CoefSupp D := GlobalTheory.T.thetaChainCoef_vanishes_off_level D
  have hArch : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D := GlobalTheory.T.archimedeanThetaCorrespondence_towers_real_data hDSC hHCM D
  have hRZ : RealZeta D := GlobalTheory.T.thetaChain_realZeta_nonvanishing hHCM D hArch
  have hZN : ZetaNe D := GlobalTheory.T.thetaChainLocalZetaNonvanishing_of_real D hMet hLF hLL hCS hRZ
  have hUN : UpNe D := GlobalTheory.T.thetaLiftUpwards_ne_zero_of_lValue D hHF hMet hLF hZN
  have hUS : UpSpan D := GlobalTheory.T.thetaLiftUpwards_in_cuspSpan hDSC hHCM hCRD hCW D hLF hLL
  have hUA : UpAdj D := GlobalTheory.T.thetaLiftUpwardsAdjoint_of_rapidDecay hCRD D
  have hSU : StepUp D := GlobalTheory.T.thetaLiftChain_adjoint_nonvanishing_step D hFD hPOV hUS hUA hUP hUN
  have hCL : ChainLW D := GlobalTheory.T.thetaChain_LValues_nonvanishing D
  have hCU : ChainUp D := chainUp_of D hMet hPB hCL hSU
  exact GlobalTheory.T.thetaLiftChain_surjective_of_adjoint_nonvanishing D hFD hMet hES hPI hCU

end GlobalTheory.ChainOnto
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChain_onto_cuspForms_of_innerProduct : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → UpPar D → OntoAll D := by
  atlas_forward_decl GlobalTheory.ChainOnto.ontoAll_of_classicalTheorems
end
