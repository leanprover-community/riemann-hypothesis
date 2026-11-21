import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarAndSizeBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarAndSizeBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleAtInertStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleAtInert
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SetPointGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedPlacesDeclaredStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedPlacesDeclared
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTerStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestPtOfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftColumnRowSetupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftColumnRowSetup
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrCrysAtRangePrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmH0SetupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmH0Setup
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointCondH0allCanon
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientSubContinuitySetupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientSubContinuitySetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointConditionAdm5Statement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointConditionAdm5
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreExtraStatement

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink.InertStep
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.InertK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admitted i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i) := by
  intro hP D L P nch HW F Cm X C₂ hS hC hconds2 hBCD i htw hg hR hin π hπ
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG5x, hG6, hBK, hCont, hSS, hDec, hEps, hTie, hShape, hFont, hH2, hCFT⟩ :=
    _root_.GlobalTheory.T.set_pt_of_setup_not_twisted hP D L P nch HW F Cm X C₂ hS i hg π hπ
  have hcB : ∀ i', GlobalTheory.HubLoc.cBnum (D.nd.l i') ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i' := by
    intro i'
    rw [hS.canon.cB]
    exact le_rfl
  have hX := _root_.GlobalTheory.closingFamilyX_alt_alt hP.font hP.fin D HW F L X (_root_.GlobalTheory.JumpStatement.holds_all_alt D)
    (hS.facts.admJ L hS.par) hS.par67 hS.facts.Conclusion1.1 hS.facts.large.2.1 hS.canon.fam hcB
  obtain ⟨M0, h0, hJ⟩ := hX.2.1 i hR π
  have hTB : TruncatedSeriesCountingIdentities.admTB i (X.r i) π (X.cB i) :=
    GlobalTheory.T.localBlochKatoCondition_of_wachModules D HW F i (X.r i) (X.ρ i) π M0 h0 (X.cB i)
      (GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler hP.bk hP.tate hP.euler D HW F Cm) (GlobalTheory.T.crystallineLatticeWachModuleExists_proof D HW F Cm) (GlobalTheory.crysOnCond_all D HW F) hFont hJ
  have h11 : 11 ≤ D.nd.l i := by
    have := D.nd.lPrime i
    exact GlobalTheory.Survey.InertPlacesGoodSet.eleven_le this.out hin (le_trans (by norm_num) hS.split)
  have hD := hS.canon.data
  have hROW : TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) := by
    by_cases hB : KillingConditions.IsRowB L (D.nd.l i)
    · rw [hD.rowB i hin hB]
      exact GlobalTheory.T.longOrbits_rowColength_inertLocalisation D L P HW C₂ i (X.r i) (X.ρ i) π (X.dc i) hconds2 hC hS.par67 h11
        ((hBCD i htw hin π hπ).1 hB)
    · have hband : X.band i = fun lam => bandOf L HW 320 i (X.r i) (X.ρ i) lam := by
        funext lam
        exact propext (hD.band i lam)
      rw [hD.rowCD i hin hB, hband]
      exact GlobalTheory.T.rowsCD_rowCondition_localBounds D L P HW F C₂ i (X.r i) (X.ρ i) π (X.dc i)
        (GlobalTheory.T.localLiftingTheoremB_of_blochKato_tateDuality_eulerChar hP.bk hP.tate hP.euler D HW F Cm 320 le_rfl)
        (GlobalTheory.T.prv_twenty_five_of_blochKato_tateDuality_eulerChar hP.bk hP.tate hP.euler D HW F Cm)
        (GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hP.bk hP.tate hP.euler D HW F Cm) hS.par67 h11 hπ ((hBCD i htw hin π hπ).2 hB)
  have hLIFT : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i (X.r i) (X.dc i) (X.e' i) := by
    intro w hw hwc
    rw [hD.col i hin] at hwc
    simp at hwc
  exact ⟨hG1, hG2, hG3, hG4, hG5, hG5x, hG6, hBK, hTB, hROW, hLIFT, hCont, hSS, hDec, hEps, hTie, hShape, hFont,
    hH2, hCFT⟩
end GlobalTheory.NLink.InertStep
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adm_at_inert_of_range : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.InertK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admitted i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i) := by
  atlas_forward_decl _root_.GlobalTheory.NLink.InertStep.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.LiftExpSplit
open Module
variable {D : D7}
end GlobalTheory.LiftExpSplit
end
namespace GlobalTheory.LiftExpSplit
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → EmbeddingTypes.LiftExponentColumn i (X.r i) (X.dc i) (X.eS i) ∧ EmbeddingTypes.LiftExponentDualPlaces i (X.r i) (X.dc i) (X.eS i) := by
  intro hP D L P nch HW F Cm X C₂ hS i hTw hg hR hsp
  have hAJ : _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L := hS.facts.admJ L hS.par
  have hJ : AdmissibleParameterJ.JumpConditions L := _root_.GlobalTheory.JumpStatement.holds_all_alt D L hAJ
  obtain ⟨⟨ep, hA⟩, -, -, -, he, -, -⟩ := hJ
  have hgood : ∀ i, GoodR D.nd i (X.r i) := hS.canon.fam.good
  have hAA : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D := hS.facts.toCore.admA
  have hUC := _root_.GlobalTheory.HubX.unrCrysAtRangePrime_alt hP.font D L X hgood hAA.1 hAA.2.2.2.1 hAA.2.2.2.2.2.2
    hS.facts.g2.1 hS.facts.block hS.facts.muUnr i hTw hg hR hsp
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hG2 : EmbeddingTypes.admG2 i (X.r i) ep := _root_.GlobalTheory.T.admG2_of_setup_jumps hP D L P nch HW F Cm X C₂ hS ep hA i
  have h2 : D.nd.l i ≠ 2 := fun h => hR.1 (Or.inl (h ▸ D.host.two_mem_small))
  have heS : X.eS i = eA L 23 (D.nd.l i) := hS.canon.data.eS i hsp
  have h54 : LiftingTheory.LiftTheoremAllCases D HW F 23 32 32 :=
    (GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hP.bk hP.tate hP.euler D HW F Cm).2.2.2.2.2.2.2
  have hcont : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (X.r i) := continuous_family_of D i (X.r i) (hgood i)
  have hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i := GlobalTheory.T.fontaineAtPlacesOverL D i
  have hj := D.nd.j_range i
  have hhB : AdmissibleParameterJ.hJ L + 2 = Formalism.MainNotions.TwistedPlaces.hB L := by
    unfold AdmissibleParameterJ.hJ Formalism.MainNotions.TwistedPlaces.hB; ring
  have hwinT : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ,
      JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) τ
        (Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L)) := by
    intro w hw C x τ a ha
    obtain ⟨g, ρ, -, hx, -⟩ := hA i (X.r i) (hgood i) w hw C τ
    have hq := (hx x a).1.mp ha
    have hb := he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq
    have hb2 := he.2.1
    apply mem_window L a
    have hc : (((a : ℚ) : ℝ)) = (a : ℝ) := by push_cast; rfl
    rw [hc] at hb
    linarith
  have hwinD : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ,
      JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))) τ
        (Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L)) := by
    intro w hw C x τ a ha
    obtain ⟨g, ρ, -, hx, -⟩ := hA i (X.r i) (hgood i) w hw C τ
    have hq := (hx x a).2.2.1.mp ha
    have hb := he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq
    have hb2 := he.2.1
    apply mem_window L a
    have hc : (((-(a : ℚ) - 1 : ℚ)) : ℝ) = -(a : ℝ) - 1 := by push_cast; rfl
    rw [hc] at hb
    rw [abs_le] at hb ⊢
    constructor <;> linarith [hb.1, hb.2]
  rw [heS]
  refine ⟨?_, ?_⟩
  · intro w hw _ C hC
    exact lift_of_window i w hw C hC (hUC.1 w hw) h2 (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))
      (fun x v => locC_cont D i _ (rTwO_cont D i (X.r i) hcont x) w hw C v) (hFont w hw C)
      (Formalism.MainNotions.N.hN L) (Formalism.MainNotions.N.hN L) (fun x => (hG2 hg0 hg1 w hw C).2.1 x) (fun x => hwinT w hw C x)
      HW F (by norm_num) h54 _ (shape_le_eA L 23 (D.nd.l i))
  · intro w hw _ C hC
    exact lift_of_window i w hw C hC (hUC.1 w hw) h2 (fun x => TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))
      (fun x v => locC_cont D i _ (rDuO_cont i (X.r i) hcont x) w hw C v) (hFont w hw C)
      (Formalism.MainNotions.N.hN L) (Formalism.MainNotions.N.hN L) (fun x => hUC.2 w hw C hC x) (fun x => hwinD w hw C x)
      HW F (by norm_num) h54 _ (shape_le_eA L 23 (D.nd.l i))
end GlobalTheory.LiftExpSplit
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftExponentColumn_and_dualPlaces : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → EmbeddingTypes.LiftExponentColumn i (X.r i) (X.dc i) (X.eS i) ∧ EmbeddingTypes.LiftExponentDualPlaces i (X.r i) (X.dc i) (X.eS i) := by
  atlas_forward_decl _root_.GlobalTheory.LiftExpSplit.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink.PowerSmulVanishing
set_option maxHeartbeats 1600000 in
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.H0ColumnLengthBound i (X.ρ i) π (X.dc i) (X.c0 i) := by
  intro hP D L P nch HW F Cm X C₂ hS i hTw hg hRA hSp π hπ
  have hJ : AdmissibleParameterJ.JumpConditions L := _root_.GlobalTheory.JumpStatement.holds_all_alt D L (hS.facts.admJ L hS.par)
  obtain ⟨M0, h0, hl2, hJC⟩ := _root_.GlobalTheory.HubX.jointCondH0all_canon_alt hP.font D L HW (rowC C₂) X hS.canon hJ
    hS.facts.Conclusion1.1 (GlobalTheory.FontaineAdm.fontaineProperties_all_places D) i hTw hg hRA hSp π hπ
  have hlq : D.nd.l i ≠ D.host.q := fun h => hRA.2.1 (Or.inl h)
  have hld : D.nd.l i ≠ D.host.d := fun h => hRA.2.1 (Or.inr h)
  intro _ u hu w hw hconj C hC L2 hstd
  obtain ⟨-, hall⟩ := hJC u hu w hw hconj
  have hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := GlobalTheory.HubLoc.kw_le_Kur_all D i (fun h => hRA.1 (Or.inl h)) hlq hld w hw
  have hg1 : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl2 (le_trans (le_inf le_rfl hur) le_sup_left)
  have hT2c : Continuous fun g => T2O D.nd i (X.ρ i) π g :=
    GlobalTheory.HTW.RecS.Model.continuous_twistedDual_rhoO i (X.ρ i) π (hS.canon.fam.cont i π)
  have hc : ∀ v, Continuous fun g => matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i (X.ρ i) π)) g v :=
    fun v => (GlobalTheory.CrysChiOne.locC_cont' C _ hT2c).matrix_mulVec continuous_const
  obtain ⟨hcr, hwin, hnj, hc0⟩ := hall C hg1 hc L2
  have hW := GlobalTheory.T.crystallineLatticeWachModuleExists_proof D HW F Cm (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg1 (GlobalTheory.HubX.tTwoLocalLattice D i (X.ρ i) π C hc L2) M0 h0 hcr hwin
  have hkill := GlobalTheory.T.torsion_exponent_kills_invariants_of_good hP.bk hP.tate hP.euler D HW F Cm (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg1 M0 h0
    (GlobalTheory.HubX.tTwoLocalLattice D i (X.ρ i) π C hc L2) hW hnj
  unfold EmbeddingTypes.lenInvD
  haveI : IsDiscreteValuationRing ↥(OL C.LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr C.LL
  haveI : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := Formalism.BasicNotions.Examples₂.LB.OL_frac C.LL
  refine EmbeddingTypes.len_le_of_kill (Br.PD D.loc D.nbr i w hw) L2.T hstd _ (X.c0 i u) ?_
  intro x hx
  exact pow_smul_eq_zero_of_le _ hc0 (hkill x fun g => hx g)
end GlobalTheory.NLink.PowerSmulVanishing
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h0_column_length_bound_of_setup : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.H0ColumnLengthBound i (X.ρ i) π (X.dc i) (X.c0 i) := by
  atlas_forward_decl _root_.GlobalTheory.NLink.PowerSmulVanishing.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.NLink.AmbSub
variable {D : D7}
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambSub i (X.r i) π (X.dc i) ∧ EmbeddingTypes.ambCont i (X.r i) (X.ρ i) π ∧ EmbeddingTypes.ColumnH0Vanishing i (X.ρ i) π (X.dc i) := by
  intro hP D L P nch HW F Cm X C₂ hSet i hi π hπ
  have hS := _root_.GlobalTheory.T.set_pt_of_setup_not_twisted hP D L P nch HW F Cm X C₂ hSet i hi π hπ
  obtain ⟨_, hG2, _, _, _, _, _, _, hCont, _, _, _, _, _, hFont, _, _⟩ := hS
  have hρ : Continuous fun g => ((X.ρ i π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) := hSet.canon.fam.cont i π
  have hcx : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) (v : Fin D.R.nV → ↥C.LL.1),
      Continuous fun g => (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x) g).mulVec v :=
    fun w hw C x v => locC_cont D i _ (rTwO_cont D i (X.r i) hCont x) w hw C v
  have hcr : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) := by
    intro w hw C x
    rw [locC_rTwO]
    exact (hG2 w hw C).2 x
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ w hw _ C A hA
    have hJ : ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) τ
        {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) π))) τ a} := by
      intro x τ
      refine jumps_of_multV_eq (O := ↥(OL C.LL)) (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)) (hcx w hw C)
        (hFont w hw C) x π (hcr w hw C x) (hcr w hw C π) τ (fun a => ?_)
      rw [locC_rTwO, locC_rTwO]
      exact (hG2 w hw C).1.2.1 τ x π a
    exact subsum_crys (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)) (hcx w hw C) (hFont w hw C)
      (hcr w hw C) hJ A hA
  · intro w hw C
    refine ⟨fun x v => hcx w hw C x v, fun _ => ⟨fun v => ?_, fun v => ?_⟩⟩
    · exact locC_cont D i _ (WpO_cont i (X.ρ i) π hρ) w hw C v
    · exact locC_cont D i _ (GlobalTheory.TwistedDualLoc.continuous_T2O D i (X.ρ i) π hρ) w hw C v
  · intro _ w hw _ C
    exact (hG2 w hw C).1.2.2.2.2.2.1
end GlobalTheory.NLink.AmbSub
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambSub_ambCont_h0_of_setup : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambSub i (X.r i) π (X.dc i) ∧ EmbeddingTypes.ambCont i (X.r i) (X.ρ i) π ∧ EmbeddingTypes.ColumnH0Vanishing i (X.ρ i) π (X.dc i) := by
  atlas_forward_decl _root_.GlobalTheory.NLink.AmbSub.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink
theorem splitPrime_hyps_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∃ ep, EmbeddingTypes.hypDecl i (X.dc i) ep ∧ (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∧ ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.admitted i (X.r i) (X.ρ i) π (X.dc i) ep (X.eS i) (X.c0 i) (X.cB i) := by
  intro Pr D L P nch HW F Cm X C₂ S i hTw hg hR hSp
  have fa := S.facts
  have hJ : AdmissibleParameterJ.ConclusionJa D := (_root_.GlobalTheory.JumpStatement.holds_all_alt D L (fa.admJ L S.par)).1
  have hb : ((0 : ℕ) : ℝ) ≤ L.sc.b := by
    rw [Nat.cast_zero]; exact (Real.exp_pos _).le
  have hL : (1 : ℝ) ≤ L.sc.L := by have := S.big; linarith
  have hub := _root_.GlobalTheory.T.split_bound_of_params_alt Pr.font Pr.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 S.canon P hL le_rfl hb
    (fa.admJ L S.par) S.par67 fa.toCore.admA fa.Conclusion1.1 fa.Conclusion1.2.2 fa.Conclusion2.1 fa.Conclusion2.2.2 fa.rhoBar fa.large.2.1
    fa.large.2.2 fa.nct fa.trip fa.same fa.block fa.muUnr fa.depthG
  obtain ⟨_, _, _, _, _, _, _, hRest, hTB, hRow, _⟩ := hub
  obtain ⟨hDecl, hRam, hType, hPt, _⟩ := hRow i hTw hg hR hSp
  refine ⟨hJ.choose, hDecl hJ, hRam, ?_⟩
  intro π hπ
  have sp := _root_.GlobalTheory.T.set_pt_of_setup_not_twisted Pr D L P nch HW F Cm X C₂ S i hg π hπ
  obtain ⟨g1, _, g3, g4, _, g5x, g6, bk, cont, ss, dec, eps, tie, shape, font, h2, cft⟩ := sp
  have hG2 := _root_.GlobalTheory.T.admG2_of_setup_jumps Pr D L P nch HW F Cm X C₂ S hJ.choose hJ.choose_spec i
  have hG5 := _root_.GlobalTheory.T.admG5_of_setup Pr D L P nch HW F Cm X C₂ S i hg π hπ
  obtain ⟨lc, lr⟩ := _root_.GlobalTheory.T.liftExponentColumn_and_dualPlaces Pr D L P nch HW F Cm X C₂ S i hTw hg hR hSp
  have hH0 := _root_.GlobalTheory.T.h0_column_length_bound_of_setup Pr D L P nch HW F Cm X C₂ S i hTw hg hR hSp π hπ
  obtain ⟨sub, acont, a56⟩ := _root_.GlobalTheory.T.ambSub_ambCont_h0_of_setup Pr D L P nch HW F Cm X C₂ S i hg π hπ
  obtain ⟨l51, l52, _⟩ := GlobalTheory.charpoly_span_and_hom_relations_of_admissible D i (X.r i) (X.ρ i) π g1
  obtain ⟨unr, dual, t2, aw, fil, h1f, a51, _⟩ := hPt π hπ
  have blk := (hRest i hg π hπ).block
  obtain ⟨M0, h0, jtb⟩ := hTB i hR π
  have tb9 : TruncatedSeriesCountingIdentities.admTB i (X.r i) π (X.cB i) :=
    GlobalTheory.T.localBlochKatoCondition_of_wachModules D HW F i (X.r i) (X.ρ i) π M0 h0 (X.cB i)
      (GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler Pr.bk Pr.tate Pr.euler D HW F Cm) (GlobalTheory.T.crystallineLatticeWachModuleExists_proof D HW F Cm) (GlobalTheory.crysOnCond_all D HW F) font jtb
  have tb : EmbeddingTypes.admTB i (X.r i) π (X.dc i) (X.cB i) := fun w hw _ C hC => tb9 w hw C hC
  have bka : LargeLevelLemmas.BlochKatoAnnihilators i := GlobalTheory.T.blochKatoAnnihilator_all_of_tateDuality_eulerChar Pr.bk Pr.tate Pr.euler D i
  have fin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i := GlobalTheory.T.tateFinitenessAll_of_localTateDuality Pr.tate D i
  exact ⟨g1, hG2, g3, g4, hG5, g5x, g6, a56, a51, l51, l52, ⟨bk, bka⟩, lc, lr, hH0, tb, unr, cont, ss, dec, eps, tie,
    shape, font, h2, fin, cft, blk, dual, t2, aw, fil, h1f, sub, acont, hType _⟩
end GlobalTheory.NLink
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_places_declared' : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∃ ep, EmbeddingTypes.hypDecl i (X.dc i) ep ∧ (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∧ ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.admitted i (X.r i) (X.ρ i) π (X.dc i) ep (X.eS i) (X.c0 i) (X.cB i) := by
  atlas_forward_decl _root_.GlobalTheory.NLink.splitPrime_hyps_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NSizes
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X 120 := by
  intro hP D L P nch HW F Cm X C₂ hS
  have hb : ((0 : ℕ) : ℝ) ≤ L.sc.b := by
    simp only [Nat.cast_zero]
    exact (Real.exp_pos _).le
  have hub := _root_.GlobalTheory.T.split_bound_of_params_alt hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P
    (le_trans (by norm_num) hS.big) le_rfl hb (hS.facts.admJ L hS.par) hS.par67 hS.facts.toCore.admA
    hS.facts.Conclusion1.1 hS.facts.Conclusion1.2.2 hS.facts.Conclusion2.1 hS.facts.Conclusion2.2.2 hS.facts.rhoBar hS.facts.large.2.1
    hS.facts.large.2.2 hS.facts.nct hS.facts.trip hS.facts.same hS.facts.block hS.facts.muUnr hS.facts.depthG
  obtain ⟨-, -, -, -, hCB, hC0, ⟨M0, h0', hW⟩, -⟩ := hub
  intro i hT hg hR
  refine ⟨hCB i hT hg hR, ?_, ?_⟩
  · have h := GlobalTheory.T.maxLength_localInvariants_twisted_fractionModInteger_le D i (X.dc i).col (fun h => hR.1 (Or.inl h)) (fun h => hR.2.1 (Or.inl h))
      (fun h => hR.2.1 (Or.inr h)) (fun u hu => ((X.dc i).cover u).1 (Or.inr hu))
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  · intro hsp u hu
    refine ⟨hC0 i hT hg hR hsp u hu, fun π hπ => ?_⟩
    obtain ⟨hu', s, hs, hc, hcrys, hJ, hnj, hcle⟩ := hW i hT hg hsp u hu π hπ
    have hWat := GlobalTheory.T.crystallineLatticeWachModuleExists_proof D HW F Cm (D.nd.l i) (D.nbr i u hu').Kw s (D.nbr i u hu').LL hs
    have hHW := hWat (GlobalTheory.HubX.wLat D i (X.ρ i) π u hu' hc) M0 h0' hcrys hJ
    have hkill := GlobalTheory.T.torsion_exponent_kills_invariants_of_good hP.bk hP.tate hP.euler D HW F Cm (D.nd.l i) (D.nbr i u hu').Kw s (D.nbr i u hu').LL hs
      M0 h0' (GlobalTheory.HubX.wLat D i (X.ρ i) π u hu' hc) hHW hnj
    have hlen := GlobalTheory.T.lenUnit_invariants_twistedLattice_le_of_killingExponent D HW i (X.ρ i) π u hu' s hs hc (X.c0 i u) _ rfl (by
      intro x hx
      have e := hkill x hx
      rw [← Nat.sub_add_cancel hcle, pow_add, mul_smul, e, smul_zero])
    have h1 := hC0 i hT hg hR hsp u hu
    have hr : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
    calc (Br.h0W i u (X.ρ i) π : ℝ) ≤ (D.R.r : ℝ) * (X.c0 i u : ℕ) := hlen
      _ ≤ (D.R.r : ℝ) * (120 * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L) := mul_le_mul_of_nonneg_left h1 hr
      _ = 120 * D.R.r * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L := by ring
end GlobalTheory.NSizes
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantsBoundNonsplit_of_setup : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X 120 := by
  atlas_forward_decl _root_.GlobalTheory.NSizes.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink
theorem rowsAD_in_setting_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ),
    _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) →
    KillingConditions.StarAD L X ∧ KillingConditions.BBLe L X 7200 := by
  intro hP D L P nch HW F Cm X C₂ hS hC hp2 hBCD
  have hstep : KillingConditions.StepAD L X :=
    { a09 := _root_.GlobalTheory.T.adm_at_inert_of_range hP D L P nch HW F Cm X C₂ hS hC hp2 hBCD
      a78 := _root_.GlobalTheory.T.unramified_places_declared' hP D L P nch HW F Cm X C₂ hS
      goodR := hS.canon.fam.good }
  have hst1 : TruncatedSeriesCountingIdentities.IntegralityFromMetric D := GlobalTheory.T.integralityFromMetric_of_designConditionAll hP.artin hP.bk hP.tate hP.euler D hS.facts.duties.2.2.1
  have h78 := GlobalTheory.T.splitCase_bound_at_point_of_admitted_items_alt hP.artin hP.tate hP.euler D
  have hG2 : ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π :=
    fun i hi π hπ => (_root_.GlobalTheory.T.set_pt_of_setup_not_twisted hP D L P nch HW F Cm X C₂ hS i hi π hπ).2.1
  refine ⟨GlobalTheory.T.starInequality_rowsAD_of_global_theorems D L HW X (rowC C₂) hS.canon.data hstep hst1 h78 hG2 hS.kill hS.sha, ?_⟩
  have h := GlobalTheory.T.nonPlacePart_localBound_le_middleRange D L P HW X (rowC C₂) 120 (by norm_num) hS.canon.data
    (_root_.GlobalTheory.T.invariantsBoundNonsplit_of_setup hP D L P nch HW F Cm X C₂ hS)
  have e : (60 : ℝ) * 120 = 7200 := by norm_num
  rwa [e] at h
end GlobalTheory.NLink
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_ad_and_bb_le_of_joint_cond : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) → KillingConditions.StarAD L X ∧ KillingConditions.BBLe L X 7200 := by
  atlas_forward_decl _root_.GlobalTheory.NLink.rowsAD_in_setting_alt
end
end
