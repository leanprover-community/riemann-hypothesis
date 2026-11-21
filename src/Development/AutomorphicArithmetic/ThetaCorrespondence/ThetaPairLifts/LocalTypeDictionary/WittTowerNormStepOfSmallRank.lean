import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleFactorStepSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageRankFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageExtensionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedFamilyTripleExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageExtensionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSuccessorCoefficients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleFactorStepFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageFitFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramesForTriangleStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangleStageFrameFactorisation
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoConst
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleWeilTransferMatching
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoPass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralsAgreeOfIntegrableKernel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DvReBaseMain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsTwoTriplesAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsTwoTriplesAgreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageFitFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureRigidifications
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureRigidificationsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTowerStageNormFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsTripleCoherence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleFactorStepFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSuccessorCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageRankFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleFactorStepSecondStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SmallTriple
open GlobalTheory.Grid MeasureTheory
variable {D : D7}
private theorem eta_sq_eq_one_alt {η : (AF D.host.F)ˣ →* Circle} (h : IsEta D η) (a : (AF D.host.F)ˣ) : η a ^ 2 = 1 := by
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have e := h.2.2.1 (idF D a)
  have e2 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := by
    ext1
    show Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) (a : AF D.host.F)) = ((a ^ 2 : (AF D.host.F)ˣ) : AF D.host.F)
    let b := (Module.finBasis D.host.F D.host.E).baseChange (AF D.host.F)
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin, h2, Units.val_pow_eq_pow_val]
  rwa [e2, map_pow] at e
private theorem restriction_eta_add_two {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ (n + 2)) : ResEta D χ n :=
  ⟨h.1, fun η hη a => by rw [h.2 η hη a, pow_add, eta_sq_eq_one_alt hη, mul_one]⟩
private theorem exists_weil_representation (hP : GlobalTheory.Published.WeilRepresentationUnitaryPair) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (ε : Bool) (S W : HSp D) {χS χW : (AE D)ˣ →* Circle} (h1 : IsHeckeChar D χS) (h2 : IsHeckeChar D χW)
    (h3 : ResEta D χS S.rank) (h4 : ResEta D χW W.rank) : ∃ ω : WRep S W, IsWeil ψ ε S W χS χW ω := by
  obtain ⟨om, h⟩ := hP D ψ (sgn ε S) W χS χW hψ h1 h2 h3 h4
  exact ⟨om.comp ((ofSgn ε S).symm.toMonoidHom.prodMap (MonoidHom.id _)), h⟩
private theorem exists_vacuum_vector (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) : ∃ f, IsVacO ψ θ S T sS sT ΛS ΛT f := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T sS sT hS hT ΛS ΛT dS dT
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  let _ : MeasurableSpace (WO S T) := measMx _ _
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have h1 := (hf 1).1
  simp only [one_mul] at h1
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.T.exists_normalise_meanSquare_of_cocompact' (WO S T) (ratL T S) K hK hcov f h1.cont f0 (by
    rintro _ ⟨g, rfl⟩ w
    have e := h1.quasi g w
    have e' := congrArg norm e
    rw [norm_mul, hψ.1.2.1, one_mul] at e'
    exact e')
  exact ⟨fun w => c * f w, hψ, hθ, (hf c).1, (hf c).2.1, (hf c).2.2, ⟨(μ, 𝓕), hμ⟩,
    fun p hp => hc p.1 p.2 hp.1 hp.2.1 hp.2.2⟩
theorem exists_small_triple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (T : Type) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E)
    (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)) (rB : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig B') (rW : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig WW₁),
    IsInfFam θ → X.Is ψ θ α β νH S → rB.Is → rW.Is → B'.rank + 2 = A'.rank → WW₁.rank + 2 = WW.rank →
    ∃ Y : Tri T A B' WW₁, Y.rA = X.rA ∧ Y.rA' = rB ∧ Y.rW = rW ∧ Y.Is ψ θ α β νH S := by
  intro hP D T A A' WW B' WW₁ X ψ θ α β νH S rB rW hθ hX hB hW eB eW
  have hψ : IsStdChar D ψ (-1) := hX.isVac.1
  have hA := hX.rigA
  choose ω hω using fun t => exists_weil_representation hP.weilRepresentationUnitaryPair hψ true A WW₁ (hX.weil t).hecS (hX.weil t).hecT
    (hX.weil t).resS (restriction_eta_add_two (eW ▸ (hX.weil t).resT))
  choose ω' hω' using fun t => exists_weil_representation hP.weilRepresentationUnitaryPair hψ false B' WW₁ (hX.weil' t).hecS (hX.weil' t).hecT
    (restriction_eta_add_two (eB ▸ (show ResEta D (α t) A'.rank from (hX.weil' t).resS))) (restriction_eta_add_two (eW ▸ (hX.weil' t).resT))
  have hneg : IsSelfDualC (neg A) X.rA.Λ := by
    refine ⟨hA.1.1, fun y => (hA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  obtain ⟨vac, hv⟩ := exists_vacuum_vector ψ θ hψ hθ (neg A) WW₁ (fun τ => -X.rA.s τ) rW.s
    (fun τ => isCartanInv_sgn true _ τ (hA.2.2 τ).1) (fun τ => (hW.2.2 τ).1) X.rA.Λ rW.Λ hneg hW.1
  obtain ⟨vac', hv'⟩ := exists_vacuum_vector ψ θ hψ hθ B' WW₁ rB.s rW.s
    (fun τ => (hB.2.2 τ).1) (fun τ => (hW.2.2 τ).1) rB.Λ rW.Λ hB.1 hW.1
  have hν : ∀ t, IsHeckeChar D (α t / β t) := fun t => (hX.weil' t).hecT
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D ψ θ A WW₁ X.rA rW _ _ _ _ _ hA hW (hν t) (hX.idem t)
    (GlobalTheory.ConstRatio.ideal_ne_bot X S t) hv
  choose f' hf' _ using fun t => GlobalTheory.T.exists_thetaFunction_standardPairSecond D ψ θ B' WW₁ rB rW _ _ _ _ A.rank _ hB hW (hν t) (hX.idem t)
    (GlobalTheory.ConstRatio.ideal_ne_bot X S t) hv'
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas B'
  have hr := hX.rank
  exact ⟨⟨X.rA, rB, rW, ω, ω', vac, vac', X.e, X.c, f, f', X.m, X.fd, m', fd'⟩, rfl, rfl, rfl,
    ⟨by omega, hA, hB, hW, hω, hω', hv, hv', hX.idem, hX.expo, hf, hf', hX.meas, hm'⟩⟩
end GlobalTheory.SmallTriple
end
theorem _root_.GlobalTheory.T.exists_small_triple_of_weil_vacuum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (T : Type) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E)
    (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)) (rB : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig B') (rW : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig WW₁),
    IsInfFam θ → X.Is ψ θ α β νH S → rB.Is → rW.Is → B'.rank + 2 = A'.rank → WW₁.rank + 2 = WW.rank →
    ∃ Y : Tri T A B' WW₁, Y.rA = X.rA ∧ Y.rA' = rB ∧ Y.rW = rW ∧ Y.Is ψ θ α β νH S := _root_.GlobalTheory.SmallTriple.exists_small_triple
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStepK.PiLocalization₂
theorem quadratic_tower_step_base_stage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → ∃ (B' WW₁ : HSp D) (Y : Tri T A B' WW₁),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ GlobalTheory.SqStepK.IsStepB X Y := by
  intro hP _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W S hψ hN i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXI⟩ := hX
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hrk := hXI.rank
  have hb1 : 2 * qq D j + 3 ≤ rankV D i j := by
    simp only [rankV, qq, Formalism.BasicNotions.Ranks.r]; omega
  have hb2 : 2 * pp D j ≤ rankV D (i + 1) (j + 1) := by
    simp only [rankV, pp, Formalism.BasicNotions.Ranks.r]; omega
  obtain ⟨B', Λ₁, ι, x, y, hs, hsig, hsd, hneg⟩ := GlobalTheory.T.hyperbolicPlane_split_selfDual_hermitian_complement D A' X.rA'.Λ q hXI.rigA'.1 hnA' (by omega) (by omega)
  obtain ⟨WW₁, ΛW, ι', x', y', hs', hsig', hsd', hneg'⟩ :=
    GlobalTheory.T.hyperbolicPlane_split_selfDual_hermitian_complement D WW X.rW.Λ (p + q) hXI.rigW.1 (by simpa only [add_assoc] using hnW) (by omega) (by omega)
  obtain ⟨rB, eB, hB⟩ := GlobalTheory.RigExists.exists_rig D B' Λ₁ hsig hsd
  obtain ⟨rW, eW, hW⟩ := GlobalTheory.RigExists.exists_rig D WW₁ ΛW hsig' hsd'
  obtain ⟨Y, e1, e2, e3, hY⟩ := _root_.GlobalTheory.T.exists_small_triple_of_weil_vacuum hP D T A A' WW B' WW₁ X W.ψ W.θ _ _ _ _ rB rW W.θ_is hXI hB hW
    (by have := hs.1; omega) (by have := hs'.1; omega)
  refine ⟨B', WW₁, Y, ⟨hp, by omega, hrA, by have := hs.1; omega, hnA, hneg, hneg', hY⟩, e1, ⟨ι, x, y, ?_⟩, ⟨ι', x', y', ?_⟩⟩
  · rw [e2, eB]; exact hs
  · rw [e3, eW]; exact hs'
end GlobalTheory.SqStepK.PiLocalization₂
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_tower_step_stage_induction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → ∃ (B' WW₁ : HSp D) (Y : Tri T A B' WW₁),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ GlobalTheory.SqStepK.IsStepB X Y := by
  first | exact @_root_.GlobalTheory.SqStepK.PiLocalization₂.quadratic_tower_step_base_stage | exact _root_.GlobalTheory.SqStepK.PiLocalization₂.quadratic_tower_step_base_stage | (intros; apply _root_.GlobalTheory.SqStepK.PiLocalization₂.quadratic_tower_step_base_stage <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.exists_good_geometry_over_carried_frames : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank),
        GlobalTheory.SqStepBig.Over X Γ ∧ Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧
        ∀ s, (s = t ∨ s = μ₀) → GlobalTheory.SqStepBig.Carried G W i j X Bs FA FA' FW Γ s := by
  intro _
  refine GlobalTheory.SqStepBig.gbig_two GlobalTheory.T.towerStage_seesawDictionary_framesSignatures GlobalTheory.T.towerStage_seesawDictionary_framesSignatures ?_
  intro D T Lc sc G μ₀ C x b q1 _ W _ i j p q A A' WW X lam t Bs hX _ hB
  obtain ⟨FA, FA', FW, a, b, -, -, -, hd⟩ := q1 W i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ := hX
  obtain ⟨⟨hψ, -⟩, hBs, hemb, -, -, hκ⟩ := hB
  have hsz := GlobalTheory.StageDict.stage_sizes i j hp hq hrA hrA'
  obtain ⟨Γ, hp', hq', hg, hS⟩ := UpperTheory.exists_geo_of_signature_rank_bounds D W.ψ T A A' WW X FA FA' FW hXi.rank Bs p q hBs hψ hemb hXi.rigA hXi.rigA' hXi.rigW
    hXi.meas hXi.meas' hnA hnA' hnW hsz.1 hsz.2.1 hsz.2.2.1 hκ
  refine ⟨FA, FA', FW, Γ, ⟨⟨rfl, hS.JA, hS.latA.1⟩, ⟨rfl, hS.JB, hS.latB.1⟩, ⟨hXi.rank.symm, hS.pairA.JW, hS.latA.2⟩⟩,
    hp', hq', hg, fun s _ => ?_⟩
  obtain ⟨-, -, f1, f2, k1, k2⟩ := hd s
  refine ⟨f1, f2, k1, k2, fun om om' hT => ?_⟩
  obtain ⟨cA, cB, hO, -⟩ := UpperTheory.exists_seesaw_intertwiners_of_triple D W.ψ W.θ hXi.isVac.2.inf T A A' WW X FA FA' FW hXi.rank Bs Γ hS
    (GlobalTheory.SqStep.chs G i j s) om om' hT (X.ω s) (X.ω' s) (hXi.weil s) (hXi.weil' s)
  exact ⟨_, cA, cB, hO⟩
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.StageGeo.geometric_stage_constant_on_pure_tensors :
    _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : MeasureTheory.Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : Base D.host.F D.host.E) (Γ : Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → GlobalTheory.SquareAgree.IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    IsHaarFD W₁ ν₁ 𝓕₁ → IsWeil ψ false W₁ X α (α / β) ωB →
    (∀ g ∈ GfC W₁, ∀ Φ ∈ algF ψ θ false A₁ B, ωB (g, 1) Φ ∈ algF ψ θ false A₁ B) →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank) (c : ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ Xc om om' R Rf c →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb,
    ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ)
      (φ' : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, φ' v ∈ GlobalTheory.WeilM.SB _) → (∀ v ∉ Xc.T, φ v = Γ.M.vac v) → (∀ v ∉ Xc.T, φ' v = Γ.M'.vac v) →
    R.p f = R.p' f' → (∀ v ∈ Xc.T, Rf.p v (φ v) = Rf.p' v (φ' v)) →
    ∀ (Φ : WO W X → ℂ) (Φ' : WO W₁ X → ℂ), GlobalTheory.SquareAgree.IsDatum Γ.M ψ cA (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) Φ →
      GlobalTheory.SquareAgree.IsDatum Γ.M' ψ cB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ') Φ' →
      (∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) →
      thetaInt ωA ν 𝓕 Φ = c • thetaInt ωB ν₁ 𝓕₁ Φ' := by
  intro hP hK D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hν₁ hw hstab R Rf c hM hc f hf f' hf' φ φ'
    s s' v v' hR hfin Φ Φ' hD hD' hint
  have hT := hM.triple
  obtain ⟨hDec, hK'⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hT
  obtain ⟨-, hC⟩ := hK' R Rf hM
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by rw [← hO.psi]; exact hT.base.std
  have hstd := hT.geo.hM'.std
  obtain ⟨-, hco, hex, -⟩ := hC.1 Bs.v₁ hT.chars.good
  have hv₁ : Bs.v₁ ∉ Xc.T := hT.chars.good.1
  have hcof : ∀ᶠ w in Filter.cofinite, φ' w = Γ.M'.vac w :=
    Filter.Eventually.mono Xc.T.finite_toSet.compl_mem_cofinite fun w hw => v' w hw
  have hφstd : ∀ᶠ w in Filter.cofinite, φ' w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers D.host.F} 1 :=
    (hcof.and hstd).mono fun w h => h.1.trans h.2
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor Bs.v₁ f' φ' hφstd
  obtain ⟨φo, hφo, hp⟩ := hex Bs.τ₁ (Rf.p' Bs.v₁ (φ' Bs.v₁))
  have hφoSB : φo ∈ GlobalTheory.WeilM.SB _ := hφo.1
  have hδ : φ' Bs.v₁ - φo ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' Bs.v₁ :=
    (hco _ (sub_mem (s' Bs.v₁) hφoSB)).1 (by rw [map_sub, hp, sub_self])
  have hupd : ∀ w, Function.update φ' Bs.v₁ φo w ∈ GlobalTheory.WeilM.SB _ := by
    intro w
    by_cases hw : w = Bs.v₁
    · subst hw; rw [Function.update_self]; exact hφoSB
    · rw [Function.update_of_ne hw]; exact s' w
  have hcof' : ∀ᶠ w in Filter.cofinite, Function.update φ' Bs.v₁ φo w = Γ.M'.vac w := by
    filter_upwards [hcof, Filter.eventually_cofinite_ne Bs.v₁] with w h1 hne
    rw [Function.update_of_ne hne]; exact h1
  obtain ⟨Φ₀D, eD⟩ : ∃ Φ₀D, Φ₀D = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' (Function.update φ' Bs.v₁ φo) := ⟨_, rfl⟩
  have h0a : Φ₀D ∈ GlobalTheory.SquareAgree.algD Γ.M' Bs.ψ Bs.emb := Submodule.subset_span ⟨f', _, hf', hupd, hcof', eD⟩
  have h0s : Φ₀D ∈ Γ.M'.So Bs.ψ Bs.τ₁ :=
    Submodule.subset_span ⟨f', _, hupd, hcof', by rw [Function.update_self]; exact hφo, eD⟩
  have hdiff : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' - Φ₀D ∈ GlobalTheory.SquareAgree.CoinvPass.relD Γ.M' om' Bs.ψ Bs.emb Bs.v₁ := by
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) (φ' Bs.v₁) r := by
      rw [hrt, Function.update_eq_self]
    rw [e1, eD, ← hrt, ← GlobalTheory.SquareAgree.CoinvPass.tens_sub']
    exact GlobalTheory.SquareAgree.CoinvPass.tens_mem_relD Γ.M' om' Bs.ψ Bs.emb Bs.v₁ hstd hf' s' hcof hr hrt _ hδ
  have hpm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) Φ₀D := by
    refine ⟨insert Bs.v₁ Xc.T, Finset.subset_insert _ _, 1, 1, fun _ => f, fun _ => φ, fun _ => f',
      fun _ => Function.update φ' Bs.v₁ φo, fun _ => ⟨hf, s, fun w hw => v w fun h => hw (Finset.mem_insert_of_mem h)⟩,
      fun _ => ⟨hf', hupd, fun w hw => ?_⟩, by simp, by simp [eD], ?_⟩
    · beta_reduce
      rw [Function.update_of_ne fun h : w = Bs.v₁ => hw (h ▸ Finset.mem_insert_self _ _)]
      exact v' w fun h => hw (Finset.mem_insert_of_mem h)
    · rw [Fin.sum_univ_one, Fin.sum_univ_one, hR]
      congr 2
      funext w
      obtain ⟨w, hw⟩ := w
      by_cases h : w = Bs.v₁
      · subst h
        show Rf.p Bs.v₁ (φ Bs.v₁) = Rf.p' Bs.v₁ (Function.update φ' Bs.v₁ φo Bs.v₁)
        rw [Function.update_self, hp, v _ hv₁, v' _ hv₁]
        exact (hM.fin.sph _ hv₁).1
      · show Rf.p w (φ w) = Rf.p' w (Function.update φ' Bs.v₁ φo w)
        rw [Function.update_of_ne h]
        exact hfin w ((Finset.mem_insert.1 hw).resolve_left h)
  have hm := GlobalTheory.SquareAgree.PolMatchConst.match_of_polMatch Bs Γ Xc om om' R Rf hT _ _ hpm h0s
  obtain ⟨Φ₀, hΦ₀, hD0⟩ := hO.algB' Φ₀D h0a
  have hc1 : (-1 : D.host.E) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hk : GlobalTheory.SquareAgree.kapX X e hO.JX 1 = 1 := by
    apply Subtype.ext
    simp [GlobalTheory.SquareAgree.kapX]
  have key : ∀ Ψ ∈ GlobalTheory.SquareAgree.CoinvPass.relD Γ.M' om' Bs.ψ Bs.emb Bs.v₁,
      ∃ Φ ∈ finRel ωB (algF ψ θ false A₁ B), GlobalTheory.SquareAgree.IsDatum Γ.M' ψ cB Ψ Φ := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, hg, Ψ₀, hΨ₀, rfl⟩ := hz
      obtain ⟨Φ₁, hΦ₁, hD1⟩ := hO.algB' Ψ₀ hΨ₀
      have hgu : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc1 hO.JW₁ g) = g :=
        (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc1 hO.JW₁).right_inv g
      have hW := hO.weilB Ψ₀ Φ₁ hD1 (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc1 hO.JW₁ g) 1
      rw [hgu, hk] at hW
      exact ⟨_, Submodule.subset_span ⟨_, GlobalTheory.SquareAgree.CoinvPass.conjUInv_mem_GfC W₁ Γ.V' (-1) hc1 hO.JW₁ Bs.v₁ g hg, Φ₁, hΦ₁,
        rfl⟩, GlobalTheory.SquareAgree.CoinvPass.isDatum_sub hψ hW hD1⟩
    | zero => exact ⟨0, zero_mem _, GlobalTheory.SquareAgree.CoinvPass.isDatum_zero⟩
    | add a b _ _ ha hb =>
      obtain ⟨Φa, ha, hDa⟩ := ha
      obtain ⟨Φb, hb, hDb⟩ := hb
      exact ⟨Φa + Φb, add_mem ha hb, GlobalTheory.SquareAgree.CoinvPass.isDatum_add hψ hDa hDb⟩
    | smul c a _ ha =>
      obtain ⟨Φa, ha, hDa⟩ := ha
      exact ⟨c • Φa, Submodule.smul_mem _ c ha, GlobalTheory.SquareAgree.CoinvPass.isDatum_smul c hDa⟩
  obtain ⟨Ψ, hΨ, hDΨ⟩ := key _ hdiff
  have hrel : Φ' - Φ₀ ∈ finRel ωB (algF ψ θ false A₁ B) :=
    GlobalTheory.SquareAgree.CoinvPass.isDatum_unique cB.surjective (GlobalTheory.SquareAgree.CoinvPass.isDatum_sub hψ hD' hD0) hDΨ ▸ hΨ
  obtain ⟨hbd, hconv, -⟩ := hDec.2 Φ₀D h0s
  obtain ⟨N, C, hmod⟩ := GlobalTheory.T.theta_integral_moderate_growth_of_bounded_kernel D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hν₁ hT Φ₀ Φ₀D hD0
    hconv (by
      obtain ⟨C, k, hC⟩ := hbd 0
      exact ⟨C, k, fun g h => by simpa using hC g h⟩)
  have hlin : ∀ g h, thetaKO ωB g h (Φ' - Φ₀) = thetaKO ωB g h Φ' - thetaKO ωB g h Φ₀ := fun g h => by
    simp only [thetaKO, map_sub, _root_.Pi.sub_apply]
  have hint' : ∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h (Φ' - Φ₀)) 𝓕₁ ν₁ := fun h => by
    simp only [hlin]; exact (hint h).sub (hmod h).1
  have h0 := _root_.GlobalTheory.ThetaAgreeConv.thetaIntegral_eq_zero_of_finiteRelation hP hK hθ hTr hν₁ hw hstab hrel hint'
  funext h
  have e0 := congrFun h0 h
  have e1 : thetaInt ωB ν₁ 𝓕₁ Φ' h = thetaInt ωB ν₁ 𝓕₁ Φ₀ h := by
    simp only [thetaInt, hlin, _root_.Pi.zero_apply] at e0 ⊢
    rw [MeasureTheory.integral_sub (hint h) (hmod h).1] at e0
    exact sub_eq_zero.1 e0
  rw [_root_.Pi.smul_apply, e1,
    GlobalTheory.SquareAgree.thetaInt_eq_modelI D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (GlobalTheory.SquareAgree.kapX X e hO.JX) _ Φ hO.measW hO.domW
      (hO.theta_eq_A hD) h,
    GlobalTheory.SquareAgree.thetaInt_eq_modelI D W₁ X _ _ _ Γ.M' (-1) hO.JW₁ ν₁ 𝓕₁ ωB om' (GlobalTheory.SquareAgree.kapX X e hO.JX) Φ₀D Φ₀
      hO.measW₁ hO.domW₁ (hO.theta_eq_B hD0) h,
    hc _ _ hm (GlobalTheory.SquareAgree.kapX X e hO.JX h), smul_eq_mul]
end
end

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.StageGeo
variable {D : D7} {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))}
  {FA : Fr A} {FA' : Fr A'} {FW : Fr WW} {Bs : Base D.host.F D.host.E} {Γ : Geo D.sp.cm.sig A.rank A'.rank}
theorem geometric_stage_constant_ratio (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    (hX : X.Is ψ θ α β νH S) (hG : IsStageGeo ψ X FA FA' FW hX.rank Bs Γ) {a b : D.what₂.Tau → ℚ}
    (hd : ∀ t : T, IsTriple A A' WW (α t) (β t) ∧ (∀ τ, HasInfExp D (α t) τ (a τ) ∧ HasInfExp D (β t) τ (b τ)) ∧
      IsFinF ψ θ true FA FW (X.f t) ∧ IsFinF ψ θ false FA' FW (X.f' t) ∧
      (∀ P g h, thetaKO (X.ω t) g h (fockF ψ θ true FA FW (X.f t) P) = X.ker ψ θ t P h g) ∧
      ∀ P g h, thetaKO (X.ω' t) g h (fockF ψ θ false FA' FW (X.f' t) P) = X.ker' ψ θ t P h g)
    {lam : T → ℂ} (hF : GlobalTheory.ConstRatio.Factor X ψ θ lam) {t₁ t₂ : T} {X₁ X₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E}
    (r₁ : Reads α β S Bs t₁ X₁) (r₂ : Reads α β S Bs t₂ X₂) {R om₁ om₁' Rf₁ om₂ om₂' Rf₂} {c₁ c₂ : ℂ}
    (m₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X₁ om₁ om₁' R Rf₁) (m₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X₂ om₂ om₂' R Rf₂)
    (k₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ X₁ om₁ om₁' R Rf₁ c₁) (k₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ X₂ om₂ om₂' R Rf₂ c₂) :
    c₁ * lam t₂ = c₂ * lam t₁ := by
  have hψ := hX.isVac.1
  have hθ := hX.isVac.2.inf
  obtain ⟨g, g0, hg⟩ := exists_vac (ε := true) hG.pairA hG.latA hX.isVac
  obtain ⟨g', g0', hg'⟩ := exists_vac (ε := false) hG.pairB hG.latB hX.isVac'
  have hco : ∀ {κ : Type} (T₀ : Finset (HeightOneSpectrum (𝓞 D.host.F)))
      {φ vac : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (κ → Fv D.host.F v) → ℂ}, (∀ v ∉ T₀, φ v = vac v) →
      ∀ᶠ v in Filter.cofinite, φ v = vac v := fun T₀ _ _ h =>
    Filter.Eventually.mono T₀.finite_toSet.compl_mem_cofinite fun v hv => h v hv
  obtain ⟨Φ, Φ', hΦ, hΦ', eΦ, eΦ'⟩ : ∃ (Φ : PolF D WW.rank A.rank →ₗ[ℂ] SInf D.host.F (Fin A.rank × Fin (A.rank + A'.rank)))
      (Φ' : PolF D WW.rank A'.rank →ₗ[ℂ] SInf D.host.F (Fin A'.rank × Fin (A.rank + A'.rank))),
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧ LinearMap.range Φ' = Γ.M'.Pol Bs.ψ Bs.emb ∧
      (∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) → ∀ P,
        thO Γ.M ψ (sgn true A).gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ P) φ) =
          fockF ψ θ true FA FW (thO Γ.M ψ (sgn true A).gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) P) ∧
      ∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) → ∀ P,
        thO Γ.M' ψ (sgn false A').gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ' P) φ) =
          fockF ψ θ false FA' FW (thO Γ.M' ψ (sgn false A').gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' φ)) P := by
    obtain ⟨φ, φ', s, s', v, v', n, n', -, e, e'⟩ := exists_fin hX hG r₁ m₁ hg hg'
    obtain ⟨Φ, h1, h2⟩ := UpperTheory.thetaLift_pure_tensor_of_isFinF D ψ true A WW _ hX.rank Bs Γ.V Γ.W Γ.M hG.pairA θ hθ FA FW hG.cartA g g0 φ s (hco _ v) n
      (e ▸ (hd t₁).2.2.1)
    obtain ⟨Φ', h1', h2'⟩ := UpperTheory.thetaLift_pure_tensor_of_isFinF D ψ false A' WW _ hX.rank Bs Γ.V' Γ.W Γ.M' hG.pairB θ hθ FA' FW hG.cartB g' g0' φ' s'
      (hco _ v') n' (e' ▸ (hd t₁).2.2.2.1)
    exact ⟨Φ, Φ', h1, h1', h2, h2'⟩
  obtain ⟨-, Pi, p, p', J, -, hJ, -, hI, hI', P', hP', hint⟩ := hF
  have mP' : Φ' P' ∈ Γ.M'.Pol Bs.ψ Bs.emb := hΦ' ▸ LinearMap.mem_range_self _ _
  obtain ⟨f, mf, ef⟩ : R.p' (Φ' P') ∈ (Γ.M.Pol Bs.ψ Bs.emb).map R.p := by rw [m₁.real.quot.onto]; trivial
  obtain ⟨P, rfl⟩ : f ∈ LinearMap.range Φ := hΦ ▸ mf
  obtain ⟨Pr, qm, qm', -, -, hLM⟩ := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM D ψ θ hψ hθ A A' WW FA FA' FW a b
  have key : ∀ t Xc om om' Rf c, Reads α β S Bs t Xc → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ Xc om om' R Rf c → lam t • p P = c • p' P' := by
    intro t Xc om om' Rf c r m k
    obtain ⟨hT, hE, -, -, hk, hk'⟩ := hd t
    obtain ⟨Pim, rf, rl, pm, pm', hmm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hP.howeDualityReal hP hK hM D ψ θ hψ hθ A A' WW FA FA' FW _ _ hT
      (hLM _ _ hT hE).1 (X.ω t) (X.ω' t) (hX.weil t) (hX.weil' t)
    obtain ⟨φ, φ', s, s', v, v', -, -, l, e, e'⟩ := exists_fin hX hG r m hg hg'
    obtain ⟨cA, cB, hO, dA, dB⟩ := UpperTheory.exists_seesaw_intertwiners_of_triple D ψ θ hθ T A A' WW X FA FA' FW hX.rank Bs Γ hG Xc om om' m.triple (X.ω t) (X.ω' t)
      (by rw [r.eα, r.eβ]; exact hX.weil t) (by rw [r.eα, r.eβ]; exact hX.weil' t)
    rw [r.eα, r.eβ] at hO
    have d1 := dA _ (GlobalTheory.TensUniq.pure_mem_schA (Φ P) φ s (((hco _ v).and m.triple.geo.hM.std).mono fun v h => h.1.trans h.2))
    have d2 := dB _ (GlobalTheory.TensUniq.pure_mem_schA (Φ' P') φ' s'
      (((hco _ v').and m.triple.geo.hM'.std).mono fun v h => h.1.trans h.2))
    rw [eΦ φ s (hco _ v), ← e] at d1
    rw [eΦ' φ' s' (hco _ v'), ← e'] at d2
    have h1 := _root_.GlobalTheory.StageGeo.geometric_stage_constant_on_pure_tensors hP hK D ψ θ A A' WW FA FA' FW _ _ _ _ _ _ _ _ _ Bs Γ Xc om om' cA cB hθ hT hO hX.meas' (hX.weil' t)
      hmm.mapB.stabM.1 R Rf c m k _ mf _ mP' φ φ' s s' v v' ef l _ _ d1 d2 (fun h => by
        simp only [hk']
        exact hint t h)
    have h2 : X.I ψ θ t P = c • X.I' ψ θ t P' := by
      funext h
      have h3 := congrFun h1 h
      simp only [thetaInt, _root_.Pi.smul_apply, hk, hk'] at h3
      exact h3
    refine hJ t ?_
    rw [map_smul, map_smul, ← hI, ← hI' t P' (hint t), h2]
  have q₁ := key _ _ _ _ _ _ r₁ m₁ k₁
  have q₂ := key _ _ _ _ _ _ r₂ m₂ k₂
  refine smul_left_injective ℂ hP' ?_
  show (c₁ * lam t₂) • p' P' = (c₂ * lam t₁) • p' P'
  rw [mul_comm c₁, mul_comm c₂, mul_smul, mul_smul, ← q₁, ← q₂, smul_comm]
end GlobalTheory.StageGeo
end
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RealMapsChars
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.RealMapsChars
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealMapsChars in
theorem GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) oa oa' ob ob' R,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xa oa oa' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xb ob ob' →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ oa oa' R → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ ob ob' R := by
  intro hP F E _ _ _ _ _ σ B a a' Γ Xa Xb oa oa' ob ob' R hA hB hR
  obtain ⟨hV, hV'⟩ := GlobalTheory.T.weilOperators_eq_at_realPlaces_same_exponents F E σ B a a' Γ Xa Xb oa oa' ob ob' hA hB
  have lV : ∀ g ∈ UAt σ Γ.V (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), oa (g, 1) Φ = ob (g, 1) Φ :=
    fun g hg Φ hΦ => hV g 1 hg one_mem_uAt Φ hΦ
  have lV' : ∀ g ∈ UAt σ Γ.V' (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), oa' (g, 1) Φ = ob' (g, 1) Φ :=
    fun g hg Φ hΦ => hV' g 1 hg one_mem_uAt Φ hΦ
  have lW : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), oa (1, h) Φ = ob (1, h) Φ :=
    fun h hh Φ hΦ => hV 1 h one_mem_uAt hh Φ hΦ
  have lW' : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), oa' (1, h) Φ = ob' (1, h) Φ :=
    fun h hh Φ hΦ => hV' 1 h one_mem_uAt hh Φ hΦ
  have bV : ∀ g ∈ UAt σ Γ.V (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), ob (g, 1) Φ = oa (g, 1) Φ :=
    fun g hg Φ hΦ => (lV g hg Φ hΦ).symm
  have bV' : ∀ g ∈ UAt σ Γ.V' (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), ob' (g, 1) Φ = oa' (g, 1) Φ :=
    fun g hg Φ hΦ => (lV' g hg Φ hΦ).symm
  have bW : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), ob (1, h) Φ = oa (1, h) Φ :=
    fun h hh Φ hΦ => (lW h hh Φ hΦ).symm
  have bW' : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), ob' (1, h) Φ = oa' (1, h) Φ :=
    fun h hh Φ hΦ => (lW' h hh Φ hΦ).symm
  refine ⟨⟨hR.quot.onto, ?_, ?_⟩, ⟨hR.quot'.onto, ?_, ?_⟩, ?_, ?_, hR.nontriv, ?_⟩
  · intro γ hγ f hf f₁ h
    exact hR.quot.lie γ hγ f hf f₁ (actsD_of_eqOn (fun t => bV _ (hγ.2 _)) h)
  · intro k hk f hf f₁ h
    exact hR.quot.cpt k hk f hf f₁ (acts_of_eqOn (bV k hk.1) h)
  · intro γ hγ f hf f₁ h
    exact hR.quot'.lie γ hγ f hf f₁ (actsD_of_eqOn (fun t => bV' _ (hγ.2 _)) h)
  · intro k hk f hf f₁ h
    exact hR.quot'.cpt k hk f hf f₁ (acts_of_eqOn (bV' k hk.1) h)
  · intro γ hγ f hf f' hf' f₁ f₁' h h'
    exact hR.lie γ hγ f hf f' hf' f₁ f₁' (actsD_of_eqOn (fun t => bW _ (hγ.2 _)) h)
      (actsD_of_eqOn (fun t => bW' _ (hγ.2 _)) h')
  · intro k hk f hf f' hf' f₁ f₁' h h'
    exact hR.cpt k hk f hf f' hf' f₁ f₁' (acts_of_eqOn (bW k hk.1) h) (acts_of_eqOn (bW' k hk.1) h')
  · intro N h1 h2
    refine hR.irred N (fun γ hγ f hf f₁ h => h1 γ hγ f hf f₁ (actsD_of_eqOn (fun t => lW _ (hγ.2 _)) h))
      (fun k hk f hf f₁ h => h2 k hk f hf f₁ (acts_of_eqOn (lW k hk.1) h))
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characters_real_valued_of_equal_exponent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) oa oa' ob ob' R,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xa oa oa' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xb ob ob' →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ oa oa' R → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ ob ob' R := by
  first | exact @_root_.GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent | exact _root_.GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent | (intros; apply _root_.GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Helpers
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StageGeo
private theorem common_factor_of_pair_relation {T K : Type} [Group K] {t u : T} (ν : T → K →* Circle) (lam : T → ℂ) (h0 : ∀ s, lam s ≠ 0)
    (good : T → ℂ → Prop)
    (H : ∀ s₁ s₂ c₁ c₂, (s₁ = t ∨ s₁ = u) → (s₂ = t ∨ s₂ = u) → good s₁ c₁ → good s₂ c₂ →
      ∃ k, (ν s₂ k : ℂ) * c₁ * lam s₂ = (ν s₁ k : ℂ) * c₂ * lam s₁) :
    ∃ (κ : ℂ) (k : K), ∀ s c, (s = t ∨ s = u) → good s c → c = κ * ((ν s k : ℂ) * lam s) := by
  have same : ∀ s c₁ c₂, (s = t ∨ s = u) → good s c₁ → good s c₂ → c₁ = c₂ := fun s c₁ c₂ hs g₁ g₂ => by
    obtain ⟨k, hk⟩ := H s s c₁ c₂ hs hs g₁ g₂
    exact mul_left_cancel₀ (Circle.coe_ne_zero _) (mul_right_cancel₀ (h0 s) hk)
  have nz : ∀ s k, (ν s k : ℂ) * lam s ≠ 0 := fun s k => mul_ne_zero (Circle.coe_ne_zero _) (h0 s)
  by_cases ht : ∃ c, good t c
  · obtain ⟨c₁, g₁⟩ := ht
    by_cases hu : ∃ c, good u c
    · obtain ⟨c₂, g₂⟩ := hu
      obtain ⟨k, hk⟩ := H t u c₁ c₂ (.inl rfl) (.inr rfl) g₁ g₂
      refine ⟨c₁ / ((ν t k : ℂ) * lam t), k, ?_⟩
      rintro s c (rfl | rfl) g
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inl rfl) g g₁
      · rw [same _ _ _ (.inr rfl) g g₂, div_mul_eq_mul_div, eq_div_iff (nz _ _)]
        linear_combination -hk
    · refine ⟨c₁ / ((ν t 1 : ℂ) * lam t), 1, ?_⟩
      rintro s c (rfl | rfl) g
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inl rfl) g g₁
      · exact absurd ⟨c, g⟩ hu
  · by_cases hu : ∃ c, good u c
    · obtain ⟨c₂, g₂⟩ := hu
      refine ⟨c₂ / ((ν u 1 : ℂ) * lam u), 1, ?_⟩
      rintro s c (rfl | rfl) g
      · exact absurd ⟨c, g⟩ ht
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inr rfl) g g₂
    · refine ⟨0, 1, ?_⟩
      rintro s c (rfl | rfl) g
      · exact absurd ⟨c, g⟩ ht
      · exact absurd ⟨c, g⟩ hu
private theorem reSpace_eq_of_same {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {X Y : Spc F E n}
    (hJ : X.J = Y.J) (hL : X.L = Y.L) : reS X Y = Y := by
  cases X; cases Y; cases hJ; cases hL; rfl
theorem exists_pivot_pair {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} {a a' : ℕ}
    {Γ : Geo σ a a'} {Xa Xb : Chars F E} {oa oa' ob ob'} (ha : IsTriple B Γ Xa oa oa') (hb : IsTriple B Γ Xb ob ob') :
    ∃ R Ra Rb ca cb, IsMatched B Γ Xa oa oa' R Ra ∧ IsMatched B Γ Xb ob ob' R Rb ∧ IsConst B Γ Xa oa oa' R Ra ca ∧
      IsConst B Γ Xb ob ob' R Rb cb ∧ cb ≠ 0 := by
  obtain ⟨R, Ra, h1⟩ := hM F E σ B a a' Γ Xa oa oa' ha
  obtain ⟨R', Rb, h2⟩ := hM F E σ B a a' Γ Xb ob ob' hb
  have h3 : IsMatched B Γ Xb ob ob' R Rb := ⟨hb, _root_.GlobalTheory.T.characters_real_valued_of_equal_exponent hP F E σ B a a' Γ Xa Xb oa oa' ob ob' R ha hb h1.real, h2.fin⟩
  obtain ⟨⟨-, ⟨ca, hca, -⟩, -⟩, -⟩ := (hK.1 F E σ B a a' Γ Xa oa oa' ha).2 R Ra h1
  obtain ⟨⟨-, ⟨cb, hcb, -⟩, h0⟩, -⟩ := (hK.1 F E σ B a a' Γ Xb ob ob' hb).2 R Rb h3
  exact ⟨R, Ra, Rb, ca, cb, h1, h3, hca, hcb, h0 cb hcb⟩
variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
private theorem readings_of_split_units {G : GridData Lc sc} {μ₀ : T} (hL : Lc.Is μ₀) (i j : Fin D.R.m) (s : T) {Bs : Base D.host.F D.host.E}
    (hsub : (GlobalTheory.SqStep.chs G i j s).T ⊆ Bs.P)
    (hin : ∀ v : Bs.P, v.1 ∈ (GlobalTheory.SqStep.chs G i j s).T → GlobalTheory.AdelicU.splitPrime (Bs.τ v) ∈ locPl G s)
    (hU : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      GlobalTheory.AdelicU.splitPrime τ ∈ locPl G s → AUnit τ) :
    Reads (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))
      (locPl G) Bs s (GlobalTheory.SqStep.chs G i j s) := by
  classical
  refine ⟨rfl, rfl, fun w => ⟨fun hw => ?_, ?_⟩, fun v hv => hU _ _ (hin v hv)⟩
  · have hv : w.under (𝓞 D.host.F) ∈ (GlobalTheory.SqStep.chs G i j s).T := by
      by_cases h0 : w ∈ G.pl.W0
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h0
        rw [G.pl.under_w hv]
        exact Finset.mem_union_left _ hv
      · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hw, h0⟩, rfl⟩)
    exact ⟨⟨_, hsub hv⟩, hv, GlobalTheory.FunObj.Good.under_injOn hL G s (hin ⟨_, hsub hv⟩ hv) hw (GlobalTheory.AdelicU.splitPrime_under _)⟩
  · rintro ⟨v, hv, rfl⟩
    exact hin v hv
private theorem base_split_prime_in_local_places {G : GridData Lc sc} {μ₀ : T} (hL : Lc.Is μ₀) {W : G.Weil} {i j : Fin D.R.m} {t : T}
    {Bs : Base D.host.F D.host.E} (hB : GlobalTheory.SqStep.BaseFits G W i j t Bs) (v : Bs.P) (hv : v.1 ∈ (GlobalTheory.SqStep.chs G i j μ₀).T) :
    GlobalTheory.AdelicU.splitPrime (Bs.τ v) ∈ locPl G μ₀ := by
  classical
  rw [GlobalTheory.SqStepArith.chs_T_base G hL i j] at hv
  have hw : G.pl.w v.1 ∈ G.pl.W0 := Finset.mem_image_of_mem _ hv
  have h1 := hB.2.2.2 v (Finset.mem_union_left _ hv)
  have e := GlobalTheory.FunObj.Good.under_injOn hL G t h1 (Finset.mem_union_left _ hw)
    ((GlobalTheory.AdelicU.splitPrime_under _).trans (G.pl.under_w hv).symm)
  rw [e]
  exact Finset.mem_union_left _ hw
private theorem stage_regular_geometry {ψ : AddChar (AF D.host.F) ℂ} {A A' WW : HSp D} {X : Tri T A A' WW} {FA : GlobalTheory.ChainFr.Fr A}
    {FA' : GlobalTheory.ChainFr.Fr A'} {FW : GlobalTheory.ChainFr.Fr WW} {hr : A.rank + A'.rank = WW.rank} {Bs : Base D.host.F D.host.E}
    {Γ Γ₀ : Geo D.sp.cm.sig A.rank A'.rank} (hO : GlobalTheory.SqStepBig.Over X Γ) (g : Γ.IsGood Bs) (g₀ : Γ₀.IsGood Bs)
    (ep : Γ₀.p = Γ.p) (eq : Γ₀.q = Γ.q) (h : IsStageGeo ψ X FA FA' FW hr Bs Γ₀)
    (JA : Γ.V.J = (1 : D.host.E) • A.gram) (JB : Γ.V'.J = (-1 : D.host.E) • A'.gram)
    (m1 : Γ.M.μ = X.m.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A 1 JA)) (d1 : Γ.M.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A 1 JA '' X.fd)
    (m2 : Γ.M'.μ = X.m'.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A' (-1) JB)) (d2 : Γ.M'.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A' (-1) JB '' X.fd') :
    (reG Γ Γ₀.V Γ₀.V' Γ₀.W).IsGood Bs ∧ IsStageGeo ψ X FA FA' FW hr Bs (reG Γ Γ₀.V Γ₀.V' Γ₀.W) := by
  obtain ⟨⟨r1, -, l1⟩, ⟨r2, -, l2⟩, r3, j3, l3⟩ := hO
  have L1 : Γ.V.L = Γ₀.V.L := Submodule.ext fun y => (l1 y).trans (h.latA.1 y).symm
  have L2 : Γ.V'.L = Γ₀.V'.L := Submodule.ext fun y => (l2 y).trans (h.latB.1 y).symm
  have L3 : Γ.W.L = Γ₀.W.L := Submodule.ext fun y => (l3 y).trans (h.latA.2 y).symm
  have J3 : Γ.W.J = Γ₀.W.J := j3.trans h.pairA.JW.symm
  have e1 : reS Γ.V Γ₀.V = Γ₀.V := reSpace_eq_of_same (JA.trans h.JA.symm) L1
  have e2 : reS Γ.V' Γ₀.V' = Γ₀.V' := reSpace_eq_of_same (JB.trans h.JB.symm) L2
  have e3 : reS Γ.W Γ₀.W = Γ₀.W := reSpace_eq_of_same J3 L3
  have hV : (reS Γ.V Γ₀.V).IsHerm D.sp.cm.sig Bs (A.rank - Γ.p) Γ.p := by rw [e1, ← ep]; exact g₀.hV
  have hV' : (reS Γ.V' Γ₀.V').IsHerm D.sp.cm.sig Bs Γ.q (A'.rank - Γ.q) := by rw [e2, ← eq]; exact g₀.hV'
  have hW : (reS Γ.W Γ₀.W).IsSkew D.sp.cm.sig Bs (A.rank + A'.rank - (Γ.p + Γ.q)) (Γ.p + Γ.q) := by
    rw [e3, ← ep, ← eq]; exact g₀.hW
  have G : (reG Γ Γ₀.V Γ₀.V' Γ₀.W).IsGood Bs :=
    ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hV, hV', hW, ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
      ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩
  refine ⟨G, ⟨h.pairA.base, h.pairA.psi, JA, J3.trans h.pairA.JW, ⟨_, _, hV⟩, ⟨_, _, hW⟩, G.hM⟩,
    ⟨h.pairB.base, h.pairB.psi, JB, J3.trans h.pairB.JW, ⟨_, _, hV'⟩, ⟨_, _, hW⟩, G.hM'⟩, ⟨l1, l3⟩, ⟨l2, l3⟩, h.cartA, h.cartB,
    JA, JB, m1, d1, m2, d2, h.basA, h.basB, h.basW⟩
end Helpers
theorem _root_.GlobalTheory.T.pivot_reduction_divisibility : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank),
        GlobalTheory.SqStepBig.Over X Γ → Γ.p = p → Γ.q = q → Γ.IsGood Bs →
        (∀ s, (s = t ∨ s = μ₀) → GlobalTheory.SqStepBig.Carried G W i j X Bs FA FA' FW Γ s) →
        ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank A'.rank) (P' : PolF D WW.rank A'.rank),
          (∀ s, (s = t ∨ s = μ₀) → ∀ h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ s P' h) X.fd' X.m') →
          ∃ (P : PolF D WW.rank A.rank) (k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ), ∀ s, (s = t ∨ s = μ₀) →
            ∀ om om' Rf (c : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf →
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf c →
              ∀ h, ((GlobalTheory.SqStep.chs G i j s).ν k : ℂ) * X.I W.ψ W.θ s P h = c * X.I' W.ψ W.θ s P' h := by
  intro hP hK hM
  obtain ⟨a1, h1⟩ := GlobalTheory.T.towerStage_seesawDictionary_framesSignatures
  obtain ⟨a2, h2⟩ := GlobalTheory.StageGeo.aUnit_locPl
  refine ⟨max a1 a2, fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨c2, x2, g2⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max c1 c2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have q1 := g1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G
  have q2 := g2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G
  intro W hψ i j p q A A' WW X lam t Bs hX hF hB FA FA' FW Γ hO hp hq hg hs R P' hint
  obtain ⟨F₀, F₀', FW₀, a, b, -, -, -, hd⟩ := q1 W i j p q A A' WW X hX
  obtain ⟨-, -, -, -, nA, nA', nW, hXi⟩ := hX
  have b1 := hg.eBig
  have b2 := hg.aBig
  have b3 := hg.lt
  have b4 := hg.even
  rw [hp, hq] at b1 b2
  obtain ⟨Γ₀, p₀, q₀, g₀, s₀⟩ := UpperTheory.exists_geo_of_signature_rank_bounds D W.ψ T A A' WW X F₀ F₀' FW₀ hXi.rank Bs p q hB.2.1 hB.1.1 hB.2.2.1
    hXi.rigA hXi.rigA' hXi.rigW hXi.meas hXi.meas' nA nA' nW b4 (by omega) b2 hg.kappa
  have rd : ∀ s, (s = t ∨ s = μ₀) → GlobalTheory.StageGeo.Reads (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (locPl G) Bs s (GlobalTheory.SqStep.chs G i j s) := by
    rintro s (rfl | rfl)
    · exact readings_of_split_units hL i j _ hB.1.2.1 hB.1.2.2.2 (q2 _)
    · exact readings_of_split_units hL i j _ hB.2.2.2.2.1.sub (base_split_prime_in_local_places hL hB.1) (q2 _)
  obtain ⟨κ, k, hκ⟩ := common_factor_of_pair_relation (t := t) (u := μ₀) (fun s => (GlobalTheory.SqStep.chs G i j s).ν) lam hF.1
    (fun s c => ∃ om om' Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf c) (by
    rintro s₁ s₂ c₁ c₂ h₁ h₂ ⟨o₁, o₁', R₁, m₁, k₁⟩ ⟨o₂, o₂', R₂, m₂, k₂⟩
    obtain ⟨e, cA, cB, hv⟩ := (hs s₁ h₁).2.2.2.2 o₁ o₁' m₁.triple
    obtain ⟨G₂, S₂⟩ := stage_regular_geometry hO hg g₀ (p₀.trans hp.symm) (q₀.trans hq.symm) s₀ hv.JW hv.JW₁ hv.measW hv.domW hv.measW₁ hv.domW₁
    have t₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs (GlobalTheory.ThK.reG Γ Γ₀.V Γ₀.V' Γ₀.W) (GlobalTheory.SqStep.chs G i j s₁) o₁ o₁' :=
      ⟨m₁.triple.base, G₂, m₁.triple.chars, m₁.triple.weil, m₁.triple.weil'⟩
    have t₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs (GlobalTheory.ThK.reG Γ Γ₀.V Γ₀.V' Γ₀.W) (GlobalTheory.SqStep.chs G i j s₂) o₂ o₂' :=
      ⟨m₂.triple.base, G₂, m₂.triple.chars, m₂.triple.weil, m₂.triple.weil'⟩
    obtain ⟨R', Sa, Sb, da, db, n₁, n₂, l₁, l₂, hdb⟩ := _root_.exists_pivot_pair hP hK hM t₁ t₂
    have E1 := _root_.GlobalTheory.StageGeo.geometric_stage_constant_ratio hP hK hM hXi S₂ hd hF (rd s₁ h₁) (rd s₂ h₂) n₁ n₂ l₁ l₂
    obtain ⟨k, E2⟩ := _root_.GlobalTheory.ReBase.rebase_ratio_real_part hP hK m₁ m₂ n₁ n₂ k₁ k₂ l₁ l₂
    refine ⟨k⁻¹, ?_⟩
    have z₁ : (((GlobalTheory.SqStep.chs G i j s₁).ν k : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have z₂ : (((GlobalTheory.SqStep.chs G i j s₂).ν k : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    rw [Circle.coe_div] at E2
    rw [map_inv, map_inv, Circle.coe_inv, Circle.coe_inv]
    generalize (((GlobalTheory.SqStep.chs G i j s₁).ν k : Circle) : ℂ) = n₁ at z₁ E2 ⊢
    generalize (((GlobalTheory.SqStep.chs G i j s₂).ν k : Circle) : ℂ) = n₂ at z₂ E2 ⊢
    have E3 : da * c₂ * n₂ = n₁ * (db * c₁) := by rw [E2]; field_simp
    have E4 : n₁ * c₁ * lam s₂ = n₂ * c₂ * lam s₁ :=
      mul_left_cancel₀ hdb (by linear_combination (-lam s₂) * E3 + c₂ * n₂ * E1)
    calc n₂⁻¹ * c₁ * lam s₂ = n₁⁻¹ * n₂⁻¹ * (n₁ * c₁ * lam s₂) := by field_simp
      _ = n₁⁻¹ * c₂ * lam s₁ := by rw [E4]; field_simp)
  obtain ⟨-, Pm, pp, pp', J, hsurj, -, -, hI, hI', -⟩ := hF
  obtain ⟨P, eP⟩ := hsurj (κ • pp' P')
  refine ⟨P, k, fun s hs' om om' Rf c m kc h => ?_⟩
  rw [hI, hI' s P' (hint s hs'), eP, map_smul, hκ s c hs' ⟨om, om', Rf, m, kc⟩]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStepBig
theorem quadratic_tower_large_step_stage_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∃ Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank, GlobalTheory.SqStepBig.Over X Γ ∧ Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧
        ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf c →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ c₀ →
          ∃ k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ, c * lam μ₀ =
            (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * (c₀ * lam t) := by
  intro hP hK hM
  refine GlobalTheory.SqStepBig.gbig_two (_root_.GlobalTheory.T.exists_good_geometry_over_carried_frames hP) (_root_.GlobalTheory.T.pivot_reduction_divisibility hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b q1 q2 W hψ i j p q A A' WW X lam t Bs hX hF hB
  obtain ⟨FA, FA', FW, Γ, hO, hp, hq, hg, hs⟩ := q1 W hψ i j p q A A' WW X lam t Bs hX hF hB
  refine ⟨Γ, hO, hp, hq, hg, ?_⟩
  intro R om om' Rf om₀ om₀' Rf₀ c c₀ m1 m0 k1 k0
  obtain ⟨h0, Pim, pp, pp', J, hsurj, hJ, hi, hI, hI', P', hP'0, hi'⟩ := id hF
  obtain ⟨P, k, H⟩ := q2 W hψ i j p q A A' WW X lam t Bs hX hF hB FA FA' FW Γ hO hp hq hg hs R P'
    (fun s _ h => hi' s h)
  have key : ∀ s, (s = t ∨ s = μ₀) → ∀ om om' Rf (c : ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf c →
      ((((GlobalTheory.SqStep.chs G i j s).ν k : ℂ) * lam s) • pp P) = c • pp' P' := by
    intro s hs' om om' Rf c m kc
    apply hJ s
    rw [map_smul, map_smul, mul_smul, ← hI, ← hI' s P' (hi' s)]
    funext h
    simp only [Pi.smul_apply, smul_eq_mul]
    exact H s hs' om om' Rf c m kc h
  have e1 := key t (Or.inl rfl) om om' Rf c m1 k1
  have e0 := key μ₀ (Or.inr rfl) om₀ om₀' Rf₀ c₀ m0 k0
  have e2 : ((((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) * c) • pp' P' =
      ((((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) * c₀) • pp' P' := by
    calc ((((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) * c) • pp' P'
        = (((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) • (c • pp' P') := mul_smul _ _ _
      _ = (((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) • ((((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) • pp P) := by
          rw [e1]
      _ = (((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) • ((((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) • pp P) :=
          smul_comm _ _ _
      _ = (((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) • (c₀ • pp' P') := by rw [e0]
      _ = ((((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) * c₀) • pp' P' := (mul_smul _ _ _).symm
  have e3 := sub_eq_zero.2 e2
  rw [← sub_smul] at e3
  have hz := (smul_eq_zero.1 e3).resolve_right hP'0
  have hn : (((GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  refine ⟨k, ?_⟩
  rw [Circle.coe_div, div_mul_eq_mul_div, eq_div_iff hn]
  linear_combination hz
end GlobalTheory.SqStepBig
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.tower_stage_fit_factor_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∃ Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank, GlobalTheory.SqStepBig.Over X Γ ∧ Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧
        ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf c →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ c₀ →
          ∃ k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ, c * lam μ₀ =
            (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * (c₀ * lam t) := by
  first | exact @_root_.GlobalTheory.SqStepBig.quadratic_tower_large_step_stage_dictionary | exact _root_.GlobalTheory.SqStepBig.quadratic_tower_large_step_stage_dictionary | (intros; apply _root_.GlobalTheory.SqStepBig.quadratic_tower_large_step_stage_dictionary <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqTower.StageExists
set_option maxHeartbeats 1000000 in
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.HeckeCharsOfSquare in
theorem exists_quadratic_tower_stage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ)
    (A A' WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)), IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    p ≤ pp D j → q ≤ qq D j → A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p →
    A'.rank + 2 * qq D j = rankV D i j + 2 * q → NegIdx A p → NegIdx A' q → NegIdx WW (p + q) → A.rank + A'.rank = WW.rank →
      ∃ X : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j p q X ∧ X.rA.Λ = ΛA ∧ X.rA'.Λ = ΛA' ∧ X.rW.Λ = ΛW := by
  intro _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G W hψ i j p q A A' WW ΛA ΛA' ΛW sA sA' sW hp hq kA kA'
    nA nA' nW hrk => ?_⟩⟩
  obtain ⟨rA, eA, hA⟩ := rig_exists nA _ sA
  obtain ⟨rA', eA', hA'⟩ := rig_exists nA' _ sA'
  obtain ⟨rW, eW, hW⟩ := rig_exists nW _ sW
  have ch := TopExists.chars G hL W i j
  have hθ := W.θ_is
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  choose ω hω using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη true A WW (ch t).2.1
    (ch t).2.2.2.1 (resEta_of_mod (ch t).2.2.2.2.2.1 (by omega)) (resEta_of_mod (ch t).2.2.2.2.2.2.2 (by omega))
  choose ω' hω' using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη false A' WW (ch t).1
    (ch t).2.2.1 (resEta_of_mod (ch t).2.2.2.2.1 (by omega)) (resEta_of_mod (ch t).2.2.2.2.2.2.1 (by omega))
  obtain ⟨vac, hv⟩ := (vac_exists hψ hθ nA nW hA hW).1
  obtain ⟨vac', hv'⟩ := (vac_exists hψ hθ nA' nW hA' hW).2
  choose e he using TopExists.idem_exists G hL W
  choose c hc using fun t w => GlobalTheory.ConstRatio.exists_expAt (nuH G t i j) w
  have hI : ∀ t, (∏ w ∈ locPl G t, w.asIdeal ^ c t w) ≠ ⊥ := fun t =>
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D W.ψ W.θ _ WW rA rW _ _ _ _ _ hA hW (ch t).2.2.1 (he t) (hI t) hv
  choose f' hf' _ using fun t =>
    GlobalTheory.T.exists_thetaFunction_standardPairSecond D W.ψ W.θ _ WW rA' rW _ _ _ _ A.rank _ hA' hW (ch t).2.2.1 (he t) (hI t) hv'
  obtain ⟨m, fd, hm⟩ := GlobalTheory.ConstRatio.exists_meas A
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas A'
  exact ⟨⟨rA, rA', rW, ω, ω', vac, vac', e, c, f, f', m, fd, m', fd'⟩,
    ⟨hp, hq, kA, kA', nA, nA', nW,
      ⟨hrk, hA, hA', hW, hω, hω', hv, hv', he, fun t w _ => hc t w, hf, hf', hm, hm'⟩⟩, eA, eA', eW⟩
end GlobalTheory.SqTower.StageExists
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_tower_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ)
    (A A' WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)), IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    p ≤ pp D j → q ≤ qq D j → A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p →
    A'.rank + 2 * qq D j = rankV D i j + 2 * q → NegIdx A p → NegIdx A' q → NegIdx WW (p + q) → A.rank + A'.rank = WW.rank →
      ∃ X : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j p q X ∧ X.rA.Λ = ΛA ∧ X.rA'.Λ = ΛA' ∧ X.rW.Λ = ΛW := by
  first | exact @_root_.GlobalTheory.SqTower.StageExists.exists_quadratic_tower_stage | exact _root_.GlobalTheory.SqTower.StageExists.exists_quadratic_tower_stage | (intros; apply _root_.GlobalTheory.SqTower.StageExists.exists_quadratic_tower_stage <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.divisibility_along_quadratic_tower : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E a) (V' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E a')
    (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E (a + a')) (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (R R₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (oa ob : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (oa' ob' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (Ra Rb Sa Sb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a') (ca cb da db : ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B Γ Xa oa oa' R Ra → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B Γ Xb ob ob' R Rb →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B (GlobalTheory.ThK.reG Γ V V' Z) Xa oa oa' R₂ Sa → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B (GlobalTheory.ThK.reG Γ V V' Z) Xb ob ob' R₂ Sb →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst B Γ Xa oa oa' R Ra ca → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst B Γ Xb ob ob' R Rb cb →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst B (GlobalTheory.ThK.reG Γ V V' Z) Xa oa oa' R₂ Sa da → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst B (GlobalTheory.ThK.reG Γ V V' Z) Xb ob ob' R₂ Sb db →
      ∃ k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)ˣ, da * cb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (db * ca) := by
  intro hP hK _ F E _ _ _ _ _ σ B a a' Γ V V' Z Xa Xb R R₂ oa ob oa' ob' Ra Rb Sa Sb ca cb da db m1 m2 n1 n2 k1 k2 l1 l2
  exact _root_.GlobalTheory.ReBase.rebase_ratio_real_part hP hK m1 m2 n1 n2 k1 k2 l1 l2
end
end

section
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.WeilExGen
theorem exists_weil_representation_realization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om :=
  fun h => h.weilRepresentationExists
end GlobalTheory.WeilExGen
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStepBig
open GlobalTheory.Square
end GlobalTheory.SqStepBig
end
noncomputable section
namespace GlobalTheory.SqStepBig
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LFun
section IndefiniteRowSideFullHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem theta_tower_step_exists_triple (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} (hB : B.IsGood σ) {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {X : Chars F E}
    (c : X.IsGood B a a') : ∃ om om', IsTriple B Γ X om om' := by
  have hd : ∀ {χ χ' : Chr F E}, IsHecke F E χ → IsHecke F E χ' → IsHecke F E (χ / χ') := fun h h' =>
    ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]⟩
  obtain ⟨om, hom⟩ := _root_.GlobalTheory.WeilExGen.exists_weil_representation_realization hP F E σ B hB a (a + a') Γ.V Γ.W _ _ _ _ g.hV g.hW Γ.M g.hM X.β (X.β / X.α)
    c.heckeβ (hd c.heckeβ c.heckeα) c.resβ (resEtaPow_quot c.resβ c.resα)
  obtain ⟨om', hom'⟩ := _root_.GlobalTheory.WeilExGen.exists_weil_representation_realization hP F E σ B hB a' (a + a') Γ.V' Γ.W _ _ _ _ g.hV' g.hW Γ.M' g.hM' X.α (X.α / X.β)
    c.heckeα (hd c.heckeα c.heckeβ) c.resα (by rw [Nat.add_comm]; exact resEtaPow_quot c.resα c.resβ)
  exact ⟨om, om', hB, g, c, hom, hom'⟩
theorem exists_pivot_pair (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} {a a' : ℕ}
    {Γ : Geo σ a a'} {Xa Xb : Chars F E} {oa oa' ob ob'} (ha : IsTriple B Γ Xa oa oa') (hb : IsTriple B Γ Xb ob ob') :
    ∃ R Ra Rb ca cb, IsMatched B Γ Xa oa oa' R Ra ∧ IsMatched B Γ Xb ob ob' R Rb ∧ IsConst B Γ Xa oa oa' R Ra ca ∧
      IsConst B Γ Xb ob ob' R Rb cb ∧ cb ≠ 0 := by
  obtain ⟨R, Ra, h1⟩ := hM F E σ B a a' Γ Xa oa oa' ha
  obtain ⟨R', Rb, h2⟩ := hM F E σ B a a' Γ Xb ob ob' hb
  have h3 : IsMatched B Γ Xb ob ob' R Rb := ⟨hb, _root_.GlobalTheory.T.characters_real_valued_of_equal_exponent hP F E σ B a a' Γ Xa Xb oa oa' ob ob' R ha hb h1.real, h2.fin⟩
  obtain ⟨⟨-, ⟨ca, hca, -⟩, -⟩, -⟩ := (hK.1 F E σ B a a' Γ Xa oa oa' ha).2 R Ra h1
  obtain ⟨⟨-, ⟨cb, hcb, -⟩, h0⟩, -⟩ := (hK.1 F E σ B a a' Γ Xb ob ob' hb).2 R Rb h3
  exact ⟨R, Ra, Rb, ca, cb, h1, h3, hca, hcb, h0 cb hcb⟩
theorem theta_tower_step_pair_real_part (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} (hB : B.IsGood σ)
    {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {Xa Xb : Chars F E} (xa : Xa.IsGood B a a') (xb : Xb.IsGood B a a') {la lb : ℂ}
    (H : ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), IsMatched B Γ Xa om om' R Rf → IsMatched B Γ Xb om₀ om₀' R Rf₀ →
      IsConst B Γ Xa om om' R Rf c → IsConst B Γ Xb om₀ om₀' R Rf₀ c₀ →
      ∃ k : (AE F E)ˣ, c * lb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (c₀ * la))
    {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')} (g₂ : (reG Γ V V' Z).IsGood B) :
    ∃ oa oa' ob ob' R Ra Rb da db, IsMatched B (reG Γ V V' Z) Xa oa oa' R Ra ∧ IsMatched B (reG Γ V V' Z) Xb ob ob' R Rb ∧
      IsConst B (reG Γ V V' Z) Xa oa oa' R Ra da ∧ IsConst B (reG Γ V V' Z) Xb ob ob' R Rb db ∧ db ≠ 0 ∧
      ∃ k : (AE F E)ˣ, da * lb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (db * la) := by
  obtain ⟨oa, oa', ha⟩ := _root_.GlobalTheory.SqStepBig.theta_tower_step_exists_triple hP hB g xa
  obtain ⟨ob, ob', hb⟩ := _root_.GlobalTheory.SqStepBig.theta_tower_step_exists_triple hP hB g xb
  have ha₂ : IsTriple B (reG Γ V V' Z) Xa oa oa' := ⟨hB, g₂, xa, ha.weil, ha.weil'⟩
  have hb₂ : IsTriple B (reG Γ V V' Z) Xb ob ob' := ⟨hB, g₂, xb, hb.weil, hb.weil'⟩
  obtain ⟨R, Ra, Rb, ca, cb, m1, m2, k1, k2, hcb⟩ := _root_.GlobalTheory.SqStepBig.exists_pivot_pair hP hK hM ha hb
  obtain ⟨R₂, Sa, Sb, da, db, n1, n2, l1, l2, hdb⟩ := _root_.GlobalTheory.SqStepBig.exists_pivot_pair hP hK hM ha₂ hb₂
  obtain ⟨k, hk⟩ := H R oa oa' Ra ob ob' Rb ca cb m1 m2 k1 k2
  obtain ⟨k', hk'⟩ := _root_.GlobalTheory.T.divisibility_along_quadratic_tower hP hK hM F E σ B a a' Γ V V' Z Xa Xb R R₂ oa ob oa' ob' Ra Rb Sa Sb ca cb da db
    m1 m2 n1 n2 k1 k2 l1 l2
  refine ⟨oa, oa', ob, ob', R₂, Sa, Sb, da, db, n1, n2, l1, l2, hdb, k * k', mul_left_cancel₀ hcb ?_⟩
  have e : ((Xa.ν (k * k') / Xb.ν (k * k') : Circle) : ℂ) =
      ((Xa.ν k / Xb.ν k : Circle) : ℂ) * ((Xa.ν k' / Xb.ν k' : Circle) : ℂ) := by
    rw [map_mul, map_mul, ← div_mul_div_comm, Circle.coe_mul]
  rw [e]
  linear_combination lb * hk' + ((Xa.ν k' / Xb.ν k' : Circle) : ℂ) * db * hk
end IndefiniteRowSideFullHecke
theorem theta_tower_step_norm_identity : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ),
      GlobalTheory.SqTower.IsStageC W i j (p + 1) 0 X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ), GlobalTheory.SqTower.IsStageC W i j p 0 Y ∧ Y.IsConst W.ψ W.θ c ∧
        ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
          (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (C : ℂ) (ζ : D.what₂.LL),
          GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧
          lam t = C * D.what₂.embLL ζ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (1 - (e : ℤ)) *
            GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (e : ℂ) * c t ∧
          lam μ₀ = C * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (1 - (e : ℤ)) *
            GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (e : ℂ) * c μ₀ := by
  intro hP hK hM
  refine gbig_of_three (gbig_both GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage (_root_.GlobalTheory.T.tower_stage_fit_factor_alt hP hK hM)) (gbig_both (_root_.GlobalTheory.T.quadratic_tower_exists hP) GlobalTheory.T.squareNu_ratio_values_roots_of_unity)
    (_root_.GlobalTheory.T.exists_factor_of_isStageC hP hK hM) ?_
  rintro D T Lc sc G μ₀ C x b ⟨qb, qd⟩ ⟨qs, qx⟩ qf W S hψ hN i j p A A' WW X lam e hX hF he
  obtain ⟨e₁, e₂, s, hα⟩ := hK.2.2
  obtain ⟨emb, hemb⟩ := qb W hψ i j _ _ A A' WW X hX
  obtain ⟨B₀, he₀, f₀⟩ := hemb μ₀
  obtain ⟨Γ₀, o₀, p₀, q₀, g₀, -⟩ := qd W hψ i j _ _ A A' WW X lam μ₀ B₀ hX hF f₀
  have b1 := g₀.eBig
  have b2 := g₀.aBig
  have b3 := g₀.lt
  have hV₀ := g₀.hV
  have hW₀ := g₀.hW
  rw [p₀, q₀] at b1 b2 hW₀
  rw [p₀] at hV₀
  obtain ⟨n, hn⟩ : ∃ n, A.rank = n + 2 := ⟨A.rank - 2, by omega⟩
  obtain ⟨Y', V₁, H₀, hY', hV₁, hH₀⟩ := GlobalTheory.T.exists_hyperbolicPlane_split_hermitianLatticeSpace _ _ _ B₀ f₀.2.1 A.rank n hn (by omega) Γ₀.V _ _ (by omega) (by omega) hV₀
    0 (n + 1) (by omega) (by omega)
  obtain ⟨Z', W₁, H₀', hZ', hW₁, hH₀'⟩ := GlobalTheory.T.skewHermitian_selfDual_lattice_hyperbolic_plane_splitting _ _ _ B₀ f₀.2.1 (A.rank + A'.rank) (n + A'.rank) (by omega) (by omega) Γ₀.W
    _ _ (by omega) (by omega) hW₀ 0 (n + 1) (by omega) (by omega)
  obtain ⟨B, ΛB, sB, nB, oB⟩ := GlobalTheory.T.exists_selfDual_orientedModel_conjugate_hermitian D B₀ f₀.2.1 f₀.2.2.1 n _ _ V₁ hV₁
  obtain ⟨WW₁, ΛW, sW, nW, oW⟩ := GlobalTheory.T.exists_selfDual_orientedModel_scaled_skewHermitian D B₀ f₀.2.1 f₀.2.2.1 _ _ _ W₁ hW₁
  obtain rfl : n = B.rank := oB.1.symm
  obtain ⟨s1, s2, s3, s4, -, s6, -, s8⟩ := id hX
  obtain ⟨Y, hY, y1, y2, y3⟩ := qs W hψ i j p 0 B A' WW₁ ΛB X.rA'.Λ ΛW sB s8.rigA'.1 sW (by omega) s2 (by omega) s4
    (by simpa using nB) s6 (by simpa using nW) oW.1.symm
  obtain ⟨c, hc⟩ := qf W S hψ hN i j p 0 B A' WW₁ Y hY
  haveI : Nonempty T := ⟨μ₀⟩
  refine ⟨B, A', WW₁, Y, c, hY, hc.isConst, fun t => ?_⟩
  obtain ⟨Bs, hes, f⟩ := hemb t
  have hee : Bs.emb = B₀.emb := hes.trans he₀.symm
  have f₁ : Fit G W i j t μ₀ Bs B.rank A'.rank := Fit.down_left (hn ▸ f)
  obtain ⟨Γ, o, pΓ, qΓ, g, HX⟩ := qd W hψ i j _ _ A A' WW X lam t Bs hX hF f
  obtain ⟨Γ₁, o₁, pΓ₁, qΓ₁, g₁, HY⟩ := qd W hψ i j _ _ B A' WW₁ Y c t Bs hY hc f₁
  obtain ⟨U, U₁, H, u1, u2, u3, u4, hH⟩ := GlobalTheory.T.adaptedHyperbolicPlane_rescale_rebasis _ _ _ f.2.1.cm B₀ Bs hee _ _ _ V₁ H₀ 0 (B.rank + 1) (by omega) (by omega)
    hY'.lat hV₁.lat hH₀
  obtain ⟨Z, Z₁, H', z1, z2, z3, z4, hH'⟩ := GlobalTheory.T.adaptedHyperbolicPlane_rescale_rebasis _ _ _ f.2.1.cm B₀ Bs hee _ _ _ W₁ H₀' 0 (B.rank + 1) (by omega) (by omega)
    hZ'.lat hW₁.lat hH₀'
  have eV : reS Γ.V U = reS (reS Γ₀.V Y') U := reS_congr U (o₀.1.eq o.1)
  have eW : reS Γ.W Z = reS (reS Γ₀.W Z') Z := reS_congr Z (o₀.2.2.eq o.2.2)
  have eV₁ : reS Γ₁.V U₁ = reS V₁ U₁ := reS_congr U₁ (oB.eq (y1 ▸ o₁.1))
  have eW₁ : reS Γ₁.W Z₁ = reS W₁ Z₁ := reS_congr Z₁ (oW.eq (y3 ▸ o₁.2.2))
  have eV' : reS Γ₁.V' Γ.V' = reS Γ.V' Γ.V' := reS_congr Γ.V' (o.2.1.eq (y2 ▸ o₁.2.1))
  have hV' : (reS Γ.V' Γ.V').IsHerm D.sp.cm.sig Bs Γ.q (A'.rank - Γ.q) := g.hV'
  have g₂ : (reG Γ U Γ.V' Z).IsGood Bs := isGood_reG g (by rw [eV, pΓ]; exact isHerm_rebase hee hY' u1 u3) hV'
    (by rw [eW, pΓ, qΓ]; exact isSkew_rebase hee hZ' z1 z3)
  have g₃ : (reG Γ₁ U₁ Γ.V' Z₁).IsGood Bs := by
    refine isGood_reG g₁ ?_ (by rw [eV', qΓ₁, ← qΓ]; exact hV') ?_
    · rw [eV₁, pΓ₁]
      convert isHerm_rebase hee hV₁ u2 u4 using 1 <;> omega
    · rw [eW₁, pΓ₁, qΓ₁]
      convert isSkew_rebase hee hW₁ z2 z4 using 1 <;> omega
  obtain ⟨oa, oa', ob, ob', R, Ra, Rb, da, db, m1, m2, k1, k2, hdb, k, hk⟩ :=
    _root_.GlobalTheory.SqStepBig.theta_tower_step_pair_real_part hP hK hM f.2.1 g f.2.2.2.1 f.2.2.2.2.1 HX g₂
  obtain ⟨pa, pa', pb, pb', R₁, Sa, Sb, ca, cb, n1, n2, l1, l2, hcb, k', hk'⟩ :=
    _root_.GlobalTheory.SqStepBig.theta_tower_step_pair_real_part hP hK hM f.2.1 g₁ f₁.2.2.2.1 f₁.2.2.2.2.1 HY g₃
  obtain ⟨C₀, -, HC⟩ := stepAlpha_cast (hα _ _ D.sp.cm.sig) Bs hn he (reG Γ U Γ.V' Z) (reG Γ₁ U₁ Γ.V' Z₁) H H' R R₁ eV' qΓ qΓ₁
    (by show Γ₁.p + 1 = Γ.p; rw [pΓ, pΓ₁]) (by show H.IsAdapted _ _ (reS Γ.V U) (reS Γ₁.V U₁) _ _; rw [eV, eV₁]; exact hH)
    (by show H'.IsAdapted _ _ (reS Γ.W Z) (reS Γ₁.W Z₁) _ _; rw [eW, eW₁]; exact hH')
  have E1 := HC _ _ _ _ _ _ _ m1 n1 _ _ k1 l1
  have E0 := HC _ _ _ _ _ _ _ m2 n2 _ _ k2 l2
  obtain ⟨ζ, hζ, eζ⟩ := qx W S hN i j t k
  obtain ⟨ζ', hζ', eζ'⟩ := qx W S hN i j t k'
  have hz : D.what₂.embLL ζ ≠ 0 := eζ ▸ Circle.coe_ne_zero _
  have hz0 : ζ ≠ 0 := fun h => hz (by rw [h, map_zero])
  rw [eζ] at hk
  rw [eζ'] at hk'
  have hc0 := hc.1 μ₀
  refine ⟨Bs, e₁, e₂, s, H.𝔟, H'.𝔟, C₀ * lam μ₀ * cb / (db * c μ₀), ζ' * ζ⁻¹, f.1, hζ'.mul (awayUnit_inv hz0 hζ), ?_, ?_⟩
  · change da = _ * _ * charL _ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) _ * _ at E1
    rw [map_mul, map_inv₀]
    generalize stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s H.𝔟 H'.𝔟 (1 - (e : ℤ)) = u at E1 ⊢
    generalize charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (e : ℂ) = L at E1 ⊢
    field_simp
    linear_combination (-c μ₀) * hk + lam μ₀ * c μ₀ * E1 + C₀ * u * L * lam μ₀ * hk'
  · change db = _ * _ * charL _ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) _ * _ at E0
    generalize stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s H.𝔟 H'.𝔟 (1 - (e : ℤ)) = u at E0 ⊢
    generalize charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (e : ℂ) = L at E0 ⊢
    field_simp
    linear_combination lam μ₀ * E0
end GlobalTheory.SqStepBig
end
noncomputable section
namespace GlobalTheory.SqStepBig
open GlobalTheory.Square
theorem theta_tower_norm_step_large_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j (p + 1) 0 X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p 0 Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t = y t * Lf t (e : ℂ) * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  intro hP hK hM
  refine gbig_of_three (_root_.GlobalTheory.SqStepBig.theta_tower_step_norm_identity hP hK hM) GlobalTheory.T.thetaStepFactor_ratio_unit_gaussSumQuotient GlobalTheory.T.partialHeckeLFunction_square_eq_primitive ?_
  intro D T Lc sc G μ₀ C x b q1 q2 q3 W S hψ hN i j p A A' WW X lam e Lf hX hF he hL
  obtain ⟨B, B', WW₁, Y, c, hY, hc, H⟩ := q1 W S hψ hN i j p A A' WW X lam e hX hF he
  have he2 := two_le_half hX he
  have hlam := hF.1
  have hne : ∀ t, Lf t e * c t ≠ 0 := fun t => by
    obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, C', ζ, -, -, et, -⟩ := H t
    rw [q3 i j t e (Lf t) he2 (hL t)] at et
    have h := hlam t
    rw [et] at h
    exact mul_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul h)) (right_ne_zero_of_mul h)
  refine ⟨B, B', WW₁, Y, c, fun t => lam t / (Lf t e * c t), hY, hc, fun t => ⟨div_ne_zero (hlam t) (hne t), ?_⟩, fun t => ?_⟩
  · rw [mul_assoc, div_mul_cancel₀ _ (hne t)]
  · obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, C', ζ, hB, hζ, et, e0⟩ := H t
    rw [q3 i j t e (Lf t) he2 (hL t)] at et
    rw [q3 i j μ₀ e (Lf μ₀) he2 (hL μ₀)] at e0
    have ht := hlam t
    have h0 := hlam μ₀
    rw [et] at ht
    rw [e0] at h0
    have key := stepRatio_swap (C := C') (q2 W S hψ hN i j t Bs e₁ e₂ s 𝔟 𝔠 (1 - (e : ℤ)) hB
      (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul ht))))
      (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h0))) hζ
    beta_reduce
    rw [et, e0, mul_assoc _ (Lf t e), mul_assoc _ (Lf μ₀ e), mul_div_cancel_right₀ _ (hne t),
      mul_div_cancel_right₀ _ (hne μ₀)]
    exact key
end GlobalTheory.SqStepBig
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.witt_tower_norm_step_of_large_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j (p + 1) 0 X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p 0 Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t = y t * Lf t (e : ℂ) * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  first | exact @_root_.GlobalTheory.SqStepBig.theta_tower_norm_step_large_rank | exact _root_.GlobalTheory.SqStepBig.theta_tower_norm_step_large_rank | (intros; apply _root_.GlobalTheory.SqStepBig.theta_tower_norm_step_large_rank <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HermitianSkewAdaptation
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.PlaneSkew
open GlobalTheory.AdelicU (IsSplitBasis)
open scoped Matrix
section Planes
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
end Planes
section Transport
open GlobalTheory.SqStepK GlobalTheory.SqStepBig
variable {D : D7}
end Transport
section Cast
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem const_pair_alt (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} (hB : B.IsGood σ)
    {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {Xa Xb : Chars F E} (xa : Xa.IsGood B a a') (xb : Xb.IsGood B a a') {la lb : ℂ}
    (hlb : lb ≠ 0)
    (H : ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), IsMatched B Γ Xa om om' R Rf → IsMatched B Γ Xb om₀ om₀' R Rf₀ →
      IsConst B Γ Xa om om' R Rf c → IsConst B Γ Xb om₀ om₀' R Rf₀ c₀ →
      ∃ k : (AE F E)ˣ, c * lb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (c₀ * la))
    {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')} (g₂ : (reG Γ V V' Z).IsGood B) :
    ∃ (R : RealMaps F a a') (d : ℂ) (k : (AE F E)ˣ), d ≠ 0 ∧
      GlobalTheory.SqStepK.HasConstR B (reG Γ V V' Z) R Xa (d * ((Xa.ν k / Xb.ν k : Circle) : ℂ) * la) ∧
      GlobalTheory.SqStepK.HasConstR B (reG Γ V V' Z) R Xb (d * ((Xb.ν k / Xb.ν k : Circle) : ℂ) * lb) := by
  obtain ⟨oa, oa', ob, ob', R, Ra, Rb, da, db, m1, m2, k1, k2, hdb, k, hk⟩ := _root_.GlobalTheory.SqStepBig.theta_tower_step_pair_real_part hP hK hM hB g xa xb H g₂
  refine ⟨R, db / lb, k, div_ne_zero hdb hlb, ⟨oa, oa', Ra, m1, ?_⟩, ⟨ob, ob', Rb, m2, ?_⟩⟩
  · convert k1 using 1
    field_simp
    linear_combination -hk
  · convert k2 using 1
    rw [div_self', Circle.coe_one, mul_one, div_mul_cancel₀ _ hlb]
end Cast
open GlobalTheory.SqStepBig in
theorem tower_stage_successor_relation_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
      (Y : Tri T A B' WW₁) (lam c : T → ℂ) (e : ℕ), GlobalTheory.SqTower.IsStageC W i j p (q + 1) X →
      GlobalTheory.SqTower.IsStageC W i j p q Y → GlobalTheory.SqStepK.IsStepB X Y → Factor X W.ψ W.θ lam → Factor Y W.ψ W.θ c →
      A.rank = A'.rank + 2 * e → ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (b : ℕ)
        (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank (b + 2)) (Γ₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank b)
        (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (b + 2) b) (H' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (A.rank + (b + 2)) (A.rank + b))
        (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank (b + 2)) (R₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank b) (d d₁ : ℂ)
        (k k₁ : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ),
        GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ A'.rank = b + 2 ∧ Γ₁.V = Γ.V ∧ Γ₁.p = Γ.p ∧ Γ₁.q + 1 = Γ.q ∧
        H.IsAdapted D.sp.cm.sig Bs Γ.V' Γ₁.V' 0 (b + 1) ∧ H'.IsAdapted D.sp.cm.sig Bs Γ.W Γ₁.W A.rank (A.rank + b + 1) ∧
        d ≠ 0 ∧ d₁ ≠ 0 ∧ ∀ t' ∈ ({t, μ₀} : Set T),
          GlobalTheory.SqStepK.HasConstR Bs Γ R (GlobalTheory.SqStep.chs G i j t')
            (d * (((GlobalTheory.SqStep.chs G i j t').ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * lam t') ∧
          GlobalTheory.SqStepK.HasConstR Bs Γ₁ R₁ (GlobalTheory.SqStep.chs G i j t')
            (d₁ * (((GlobalTheory.SqStep.chs G i j t').ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) * c t') := by
  intro hP hK hM
  refine gbig_of_three GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage (_root_.GlobalTheory.T.tower_stage_fit_factor_alt hP hK hM) GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage ?_
  rintro D T Lc sc G μ₀ C x b qb qd - W S hψ hN i j p q A A' WW B' WW₁ X Y lam c e hX hY ⟨hA, ⟨ι, x, y, hs⟩, ι', x', y', hs'⟩ hF hc he t
  obtain ⟨emb, hemb⟩ := qb W hψ i j _ _ A A' WW X hX
  obtain ⟨Bs, -, f⟩ := hemb t
  have hn : A'.rank = B'.rank + 2 := hs.1
  have f₁ : Fit G W i j t μ₀ Bs A.rank B'.rank := Fit.down_right (hn ▸ f)
  obtain ⟨Γ, o, pΓ, qΓ, g, HX⟩ := qd W hψ i j _ _ A A' WW X lam t Bs hX hF f
  obtain ⟨Γ₁, o₁, pΓ₁, qΓ₁, g₁, HY⟩ := qd W hψ i j _ _ A B' WW₁ Y c t Bs hY hc f₁
  obtain ⟨U, H, hU, hH⟩ := plane_herm f.2.1 hs (neg_ne_zero.2 one_ne_zero) o.2.1 o₁.2.1 g.hV' g₁.hV' (i₀ := 0) (i₁ := B'.rank + 1)
    (by omega) (by omega)
  obtain ⟨Z, H', hZ, hH'⟩ := plane_skew f.2.1 hs' o.2.2 o₁.2.2 g.hW g₁.hW (i₀ := A.rank) (i₁ := A.rank + B'.rank + 1)
    (by omega) (by omega)
  have eV : reS Γ₁.V Γ.V = reS Γ.V Γ.V := reS_congr Γ.V (o.1.eq (hA ▸ o₁.1))
  have hV : (reS Γ.V Γ.V).IsHerm D.sp.cm.sig Bs (A.rank - Γ.p) Γ.p := g.hV
  have g₂ : (reG Γ Γ.V U Z).IsGood Bs := isGood_reG g hV hU hZ
  have g₃ : (reG Γ₁ Γ.V Γ₁.V' Γ₁.W).IsGood Bs := isGood_reG g₁ (by rw [eV, pΓ₁, ← pΓ]; exact hV) g₁.hV' g₁.hW
  obtain ⟨R, d, k, hd, c1, c2⟩ := _root_.GlobalTheory.HermitianSkewAdaptation.const_pair_alt hP hK hM f.2.1 g f.2.2.2.1 f.2.2.2.2.1 (hF.1 μ₀) HX g₂
  obtain ⟨R₁, d₁, k₁, hd₁, c3, c4⟩ := _root_.GlobalTheory.HermitianSkewAdaptation.const_pair_alt hP hK hM f.2.1 g₁ f₁.2.2.2.1 f₁.2.2.2.2.1 (hc.1 μ₀) HY g₃
  obtain ⟨Γ', K, K', R', e1, e2, e3, e4, e5, e6⟩ := cast_rank Bs hn (reG Γ Γ.V U Z) (reG Γ₁ Γ.V Γ₁.V' Γ₁.W) H H' R eV
    (pΓ₁.trans pΓ.symm) (by show Γ₁.q + 1 = Γ.q; rw [qΓ, qΓ₁]) hH hH'
  refine ⟨Bs, B'.rank, Γ', _, K, K', R', R₁, d, d₁, k, k₁, f.1, hn, e1, e2, e3, e4, e5, hd, hd₁, ?_⟩
  rintro t' (rfl | rfl)
  · exact ⟨e6 _ _ c1, c3⟩
  · exact ⟨e6 _ _ c2, c4⟩
end GlobalTheory.HermitianSkewAdaptation
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.tower_stage_successor_coefficients_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
      (Y : Tri T A B' WW₁) (lam c : T → ℂ) (e : ℕ), GlobalTheory.SqTower.IsStageC W i j p (q + 1) X →
      GlobalTheory.SqTower.IsStageC W i j p q Y → GlobalTheory.SqStepK.IsStepB X Y → Factor X W.ψ W.θ lam → Factor Y W.ψ W.θ c →
      A.rank = A'.rank + 2 * e → ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (b : ℕ)
        (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank (b + 2)) (Γ₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank b)
        (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (b + 2) b) (H' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (A.rank + (b + 2)) (A.rank + b))
        (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank (b + 2)) (R₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank b) (d d₁ : ℂ)
        (k k₁ : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ),
        GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ A'.rank = b + 2 ∧ Γ₁.V = Γ.V ∧ Γ₁.p = Γ.p ∧ Γ₁.q + 1 = Γ.q ∧
        H.IsAdapted D.sp.cm.sig Bs Γ.V' Γ₁.V' 0 (b + 1) ∧ H'.IsAdapted D.sp.cm.sig Bs Γ.W Γ₁.W A.rank (A.rank + b + 1) ∧
        d ≠ 0 ∧ d₁ ≠ 0 ∧ ∀ t' ∈ ({t, μ₀} : Set T),
          GlobalTheory.SqStepK.HasConstR Bs Γ R (GlobalTheory.SqStep.chs G i j t')
            (d * (((GlobalTheory.SqStep.chs G i j t').ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * lam t') ∧
          GlobalTheory.SqStepK.HasConstR Bs Γ₁ R₁ (GlobalTheory.SqStep.chs G i j t')
            (d₁ * (((GlobalTheory.SqStep.chs G i j t').ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) * c t') := by
  first | exact @_root_.GlobalTheory.HermitianSkewAdaptation.tower_stage_successor_relation_alt | exact _root_.GlobalTheory.HermitianSkewAdaptation.tower_stage_successor_relation_alt | (intros; apply _root_.GlobalTheory.HermitianSkewAdaptation.tower_stage_successor_relation_alt <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStepK
section Values
open GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Values
theorem seesaw_first_reduction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ), GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, c t ≠ 0) ∧ ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
          (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          lam t * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c μ₀ =
            lam μ₀ * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c t := by
  intro hP hK hM
  obtain ⟨e₁, e₂, s, hSB⟩ := hK.2.1
  refine gbig_three_is (_root_.GlobalTheory.T.quadratic_tower_step_stage_induction hP hK hM) (_root_.GlobalTheory.T.tower_stage_successor_coefficients_alt hP hK hM) (_root_.GlobalTheory.T.exists_factor_of_isStageC hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b hL hy hd hf W S hψ hN i j p q A A' WW X lam e hX hF he
  obtain ⟨B', WW₁, Y, hY, hst⟩ := hy W S hψ hN i j p q A A' WW X hX
  obtain ⟨c, hc⟩ := hf W S hψ hN i j p q A B' WW₁ Y hY
  haveI : Nonempty T := ⟨μ₀⟩
  refine ⟨A, B', WW₁, Y, c, hY, hc.isConst, hc.1, fun t => ?_⟩
  obtain ⟨Bs, bb, Γ, Γ₁, H, H', R, R₁, d, d₁, k, k₁, hfit, hb, hV, hp, hq, hH, hH', hd0, hd10, hk⟩ :=
    hd W S hψ hN i j p q A A' WW B' WW₁ X Y lam c e hX hY hst hF hc he t
  obtain ⟨C₀, hC₀, hstep⟩ := hSB D.host.F D.host.E D.sp.cm.sig Bs A.rank bb Γ Γ₁ H H' R R₁ hV hp hq hH hH'
  have hE : (A.rank - (bb + 2)) / 2 = e := by omega
  have key : ∀ t' ∈ ({t, μ₀} : Set T),
      d * (((GlobalTheory.SqStep.chs G i j t').ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * lam t' *
      GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t').ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
      (C₀ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t') e₁ e₂ s H.𝔟 H'.𝔟 (-(e : ℤ))) =
      d₁ * (((GlobalTheory.SqStep.chs G i j t').ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) * c t' := by
    intro t' ht'
    obtain ⟨⟨om, om', Rf, hm, hκ⟩, ⟨om₁, om₁', Rf₁, hm₁, hκ₁⟩⟩ := hk t' ht'
    obtain ⟨u, hu1, hu2⟩ := hstep _ om om' Rf om₁ om₁' Rf₁ hm hm₁ _ _ hκ hκ₁
    rw [hE] at hu1 hu2
    have e1 : (((e : ℕ) : ℂ) + 1) = ((e + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e1] at hu2
    change _ * GlobalTheory.LFun.charL _ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) _ = _ at hu2
    rw [hu2, mul_right_comm, hu1, one_mul]
  have good : ∀ t' ∈ ({t, μ₀} : Set T), GlobalTheory.LFun.IsHecke D.host.F D.host.E (GlobalTheory.SqStep.chs G i j t').ν ∧
      ∀ᶠ w in Filter.cofinite, GlobalTheory.LFun.UnrAt (GlobalTheory.SqStep.chs G i j t').ν w := by
    intro t' ht'
    obtain ⟨⟨om, om', Rf, hm, -⟩, -⟩ := hk t' ht'
    exact nu_good hm.triple.chars
  obtain ⟨gt, ut⟩ := good t (by simp)
  obtain ⟨gμ, uμ⟩ := good μ₀ (by simp)
  obtain ⟨n, hn, hv⟩ := val_quot_pow G hL W S hN i j t
  obtain ⟨𝔟, r, hr, st, sμ⟩ := exists_stepFac_twist Bs (X := GlobalTheory.SqStep.chs G i j t) (Y := GlobalTheory.SqStep.chs G i j μ₀)
    ⟨gt.1.div' gμ.1, fun y => by simp only [MonoidHom.div_apply, gt.2 y, gμ.2 y, div_one]⟩
    ((ut.and uμ).mono fun w hw => by rw [div_eq_mul_inv]; exact hw.1.mul hw.2.inv) hn hv e₁ e₂ s H.𝔟 H'.𝔟 (-(e : ℤ)) (k / k₁)
  have kt := key t (by simp)
  have kμ := key μ₀ (by simp)
  rw [div_self', div_self', Circle.coe_one, mul_one, mul_one] at kμ
  have ek : (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) =
      (((GlobalTheory.SqStep.chs G i j t).ν (k / k₁) / (GlobalTheory.SqStep.chs G i j μ₀).ν (k / k₁) : Circle) : ℂ) *
        (((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) := by
    rw [← Circle.coe_mul, div_mul_div_comm, ← map_mul, ← map_mul, div_mul_cancel]
  rw [ek] at kt
  have z₀ := Circle.coe_ne_zero ((GlobalTheory.SqStep.chs G i j t).ν (k / k₁) / (GlobalTheory.SqStep.chs G i j μ₀).ν (k / k₁))
  have z₁ := Circle.coe_ne_zero ((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁)
  have nt := mul_ne_zero (mul_ne_zero hd10 z₁) (hc.1 t)
  have nμ : d₁ * c μ₀ ≠ 0 := mul_ne_zero hd10 (hc.1 μ₀)
  rw [← kt] at nt
  rw [← kμ] at nμ
  refine ⟨Bs, e₁, e₂, s, 𝔟, H'.𝔟, hfit, ?_, ?_, right_ne_zero_of_mul (left_ne_zero_of_mul nt),
    right_ne_zero_of_mul (left_ne_zero_of_mul nμ), ?_⟩
  · rw [st]
    exact mul_ne_zero (mul_ne_zero z₀ hr) (right_ne_zero_of_mul (right_ne_zero_of_mul nt))
  · rw [sμ]
    exact mul_ne_zero hr (right_ne_zero_of_mul (right_ne_zero_of_mul nμ))
  · rw [st, sμ]
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hd0 hC₀) z₁) ?_
    linear_combination (r * c μ₀) * kt -
      (r * c t * (((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ)) * kμ
end GlobalTheory.SqStepK
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.seesaw_first_reduction_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ), GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, c t ≠ 0) ∧ ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
          (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          lam t * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c μ₀ =
            lam μ₀ * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c t := by
  first | exact @_root_.GlobalTheory.SqStepK.seesaw_first_reduction | exact _root_.GlobalTheory.SqStepK.seesaw_first_reduction | (intros; apply _root_.GlobalTheory.SqStepK.seesaw_first_reduction <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStep
theorem theta_tower_norm_step_small_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t * Lf t ((e + 1 : ℕ) : ℂ) = y t * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  intro hP hK hM
  refine gbig_three (_root_.GlobalTheory.T.seesaw_first_reduction_level hP hK hM) GlobalTheory.T.thetaStepFactor_ratio_unit_gaussSumQuotient GlobalTheory.T.partialHeckeLFunction_square_eq_primitive ?_
  intro D T Lc sc G μ₀ C x b hk ha hl W S hψ hN i j p q A A' WW X lam e Lf hX hF he hLf
  obtain ⟨B, B', WW₁, Y, c, hY, hc, hc0, H⟩ := hk W S hψ hN i j p q A A' WW X lam e hX hF he
  have he1 : 1 ≤ e := by
    obtain ⟨h1, h2, a1, a2, -⟩ := hX
    have e2 : rankV D (↑i + 1) (↑j + 1) = rankV D ↑i ↑j + D.R.t + sLen D := by simp only [rankV]; ring
    have h3 := D.R.three_m_lt_t
    have hpp : pp D j ≤ D.R.m := by unfold pp; omega
    have hqq : qq D j ≤ D.R.m := by unfold qq; omega
    omega
  have hLeq : ∀ t, GlobalTheory.LFun.charL (chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) =
      Lf t ((e + 1 : ℕ) : ℂ) := fun t => hl i j t (e + 1) (Lf t) (by omega) (hLf t)
  refine ⟨B, B', WW₁, Y, c, fun t => lam t * Lf t ((e + 1 : ℕ) : ℂ) / c t, hY, hc, fun t => ⟨?_, ?_⟩, fun t => ?_⟩
  · obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, -, -, -, hL0, -, -⟩ := H t
    rw [hLeq t] at hL0
    exact div_ne_zero (mul_ne_zero (hF.1 t) hL0) (hc0 t)
  · rw [div_mul_cancel₀ _ (hc0 t)]
  · obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, hfit, hsf, hsf0, -, -, heq⟩ := H t
    rw [hLeq t, hLeq μ₀] at heq
    obtain ⟨bb, g, g', hb, hg, e3⟩ := ha W S hψ hN i j t Bs e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) hfit hsf
    refine ⟨bb, g, g', hb, hg, ?_⟩
    have h0 := hc0 μ₀
    have ht := hc0 t
    rw [e3] at heq
    have key := mul_right_cancel₀ hsf (show (lam t * Lf t ((e + 1 : ℕ) : ℂ) * c μ₀) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) =
      (D.what₂.embLL (bb * ∏ v ∈ G.pl.S0, ((g v : D.what₂.LL) / (g' v : D.what₂.LL))) * (lam μ₀ * Lf μ₀ ((e + 1 : ℕ) : ℂ)) * c t) *
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) by linear_combination heq)
    field_simp
    linear_combination key
end GlobalTheory.SqStep
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.witt_tower_norm_step_of_small_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t * Lf t ((e + 1 : ℕ) : ℂ) = y t * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  first | exact @_root_.GlobalTheory.SqStep.theta_tower_norm_step_small_rank | exact _root_.GlobalTheory.SqStep.theta_tower_norm_step_small_rank | (intros; apply _root_.GlobalTheory.SqStep.theta_tower_norm_step_small_rank <;> assumption)
end
end
