import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentComponentMemFrameStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointJointAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElementStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalProjectionEqOfIdempotentPatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointSupportedOfConjHalf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIdempotentMulOfUnitTopBlockReductionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFiniteThetaDatumNeZeroFrameAdjointSpec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfTypePlaceReductions

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrixAdjoint_jointAction : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (g : GA D T) (x : WO S T), frMapAdj S T βS βT (actO S T 1 g x) = HMul.hMul (frMapAdj S T βS βT x) ((βT⁻¹ * Formalism.IndefR.Lev.finE T g * βT)⁻¹ : GL (Fin T.rank) (EAf D)).1 := by
  first | exact @GlobalTheory.AdjAct.frMapAdj_actO | exact GlobalTheory.AdjAct.frMapAdj_actO | (intros; apply GlobalTheory.AdjAct.frMapAdj_actO <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrixAdjoint_supported_of_conjHalf : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T), e * e = e → IsHalf (cA D e) x → ∀ i j, toEAf D e * frMapAdj S T βS βT x i j = frMapAdj S T βS βT x i j := by
  first | exact @GlobalTheory.HalfSupp.frMapAdj_supp | exact GlobalTheory.HalfSupp.frMapAdj_supp | (intros; apply GlobalTheory.HalfSupp.frMapAdj_supp <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFiniteThetaDatum_ne_zero_frameAdjoint_spec : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D) (x : WO S T), levDatum S T βS βT LT Q m e x ≠ 0 → IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧ (∀ PP, PP ∈ LT.Pg ∨ PP ∈ Q → IsUnit (topL T.rank (redM PP (frMapAdj S T βS βT x))).det) ∧ ∃ a : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1), (∀ PP : ↥LT.Pg, ((a PP : GL (Fin T.rank) (kP PP.1)) : Matrix (Fin T.rank) (Fin T.rank) (kP PP.1)) = topL T.rank (redM PP.1 (frMapAdj S T βS βT x))) ∧ (∀ PP : ↥LT.Pg, a PP ∈ blockTri (blkOf LT.r LT.t)) ∧ (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H := by
  first | exact @GlobalTheory.FinZeta.levDatum_ne_zero_spec | exact GlobalTheory.FinZeta.levDatum_ne_zero_spec | (intros; apply GlobalTheory.FinZeta.levDatum_ne_zero_spec <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SuppLev

theorem supp_level : ∀ (D : D7) (S T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC T ΛT → IsFrame βT ΛT → T.rank ≤ S.rank → LT.Q = ∅ → IsIdemSum e Z → (∀ PP, PP ∈ Z ↔ PP ∈ LT.Pg ∨ PP ∈ Q) → ∀ g ∈ GfC T, ∀ x, levDatum S T βS βT LT Q m e x ≠ 0 → levDatum S T βS βT LT Q m e (actO S T 1 g x) ≠ 0 → ∃ k ∈ levG T βT LT, ∀ PP ∈ Z, projV T (PP.under (𝓞 D.host.F)) g = projV T (PP.under (𝓞 D.host.F)) k := by
  classical
  intro D S T ΛT βS βT LT Q m Z e hsd hfr hrk hQ hZe hZ g hg x hx hx'
  have hu' := GlobalTheory.T.frameMatrixAdjoint_jointAction S T βS βT g x
  obtain ⟨hh, hI, hU, a, ha1, ha2, ha3⟩ := GlobalTheory.T.levelFiniteThetaDatum_ne_zero_frameAdjoint_spec S T βS βT LT Q m e x hx
  obtain ⟨-, hI', hU', b, hb1, hb2, hb3⟩ := GlobalTheory.T.levelFiniteThetaDatum_ne_zero_frameAdjoint_spec S T βS βT LT Q m e _ hx'
  simp only [hu'] at hI' hU' hb1
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hZe
  have hsupp := GlobalTheory.T.frameMatrixAdjoint_supported_of_conjHalf S T βS βT e x hee hh
  obtain ⟨h1, h2, hred⟩ := GlobalTheory.T.integral_idempotent_mul_of_unit_topBlock_reductions S.rank T.rank hrk Z e hZe _ _ hI hI' hsupp
    (fun PP hP => hU PP ((hZ PP).1 hP)) (fun PP hP => hU' PP ((hZ PP).1 hP))
  have hUA := GlobalTheory.LevSplit.finE_mem_UA T g
  obtain ⟨h3, h4⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral T ΛT βT hsd hfr _ hUA _ rfl e h1 h2
  obtain ⟨hεε, hεc⟩ := GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed Z e hZe
  obtain ⟨k, hk, hmt⟩ := GlobalTheory.T.exists_idempotent_component_of_group_element T g (e + cA D e) hg hεε hεc
  refine ⟨k, ?_, fun PP hP => (GlobalTheory.T.localProjection_eq_of_idempotent_patch T _ g k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one Z e hZe PP hP) hmt).symm⟩
  have hfk := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame T βT g k (e + cA D e) hmt
  obtain ⟨hSt, hR⟩ := GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction T.rank βT _ _ Z e hZe h1 h2 h3 h4 hfk
  refine ⟨hk, ?_⟩
  refine GlobalTheory.T.mem_level_of_type_place_reductions T βT LT _ hQ (GlobalTheory.LevSplit.finE_mem_UA T k) hSt a b ha2 hb2 ha3 hb3 fun PP => ?_
  apply Units.ext
  rw [Units.val_mul, hR PP.1 ((hZ PP.1).2 (Or.inl PP.2)), ha1, hb1]
  exact hred PP.1 ((hZ PP.1).2 (Or.inl PP.2))

end GlobalTheory.SuppLev
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_level_of_levelDatum_ne_zero_translate : ∀ (D : D7) (S T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC T ΛT → IsFrame βT ΛT → T.rank ≤ S.rank → LT.Q = ∅ → IsIdemSum e Z → (∀ PP, PP ∈ Z ↔ PP ∈ LT.Pg ∨ PP ∈ Q) → ∀ g ∈ GfC T, ∀ x, levDatum S T βS βT LT Q m e x ≠ 0 → levDatum S T βS βT LT Q m e (actO S T 1 g x) ≠ 0 → ∃ k ∈ levG T βT LT, ∀ PP ∈ Z, projV T (PP.under (𝓞 D.host.F)) g = projV T (PP.under (𝓞 D.host.F)) k := by
  atlas_forward_decl GlobalTheory.SuppLev.supp_level
end
