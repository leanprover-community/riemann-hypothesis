import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdentityIntegralUnitaryFrameCoordinatesOfUnitGra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonCoefficientMapLiftPresentation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLiftReadingOfDecoratedLatticePresentatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupActionLiftFormsRightTranslation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdelicUnitaryConjIntegralFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceSupportLevelStandardCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLevelSplitsAtOffLevelSplitPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointFinitePartEqRealOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjUniformizerIsUniformizerConjPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitIdempotentAtConjugatePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrimeIdempotentMulEqZeroOfVanishingAtPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCompletedSelfDualLatticeIffIntegralStdFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameTransportEtaSupportedAtPlaceIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementInvLatticeClausesOfFrameConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementUniformizerRatioDeterminant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelTypeTrivialSplitPlaceSupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertNeighboursLiftsDoubleCosetTranslates

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.identity_integralUnitaryFrameCoordinates_of_unitGram : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (i : Fin X.toD7.R.m) (t : TupU I U), (Vc X.toD7 i).gram = 1 → LiftBrg.FrameOK X I U i t 1 1 := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.frameOK_one_of_gram_eq_one | exact GlobalTheory.Mem.R3.LiftBrg.frameOK_one_of_gram_eq_one | (intros; apply GlobalTheory.Mem.R3.LiftBrg.frameOK_one_of_gram_eq_one <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_coefficientMap_liftPresentation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∃ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) ∧
      ∀ t : TupU I U, ∃ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 P ∧
        (∀ v, P.coef v = c v) ∧ Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef P (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) := by
  first | exact @GlobalTheory.Mem.R3.LiftPresStd.exists_oneCoef_presStd | exact GlobalTheory.Mem.R3.LiftPresStd.exists_oneCoef_presStd | (intros; apply GlobalTheory.Mem.R3.LiftPresStd.exists_oneCoef_presStd <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardLiftReading_of_decoratedLatticePresentations : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m), L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∀ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) →
    ∀ P : ∀ t, LiftBrg.PresL X I hX U Xg tr L cV i t, (∀ t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 (P t)) →
      (∀ t v, (P t).coef v = c v) → BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (P t).extL φ) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.brgStdV_of_readsStd_one | exact GlobalTheory.Mem.R3.LiftBrg.brgStdV_of_readsStd_one | (intros; apply GlobalTheory.Mem.R3.LiftBrg.brgStdV_of_readsStd_one <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitary_conj_integralFrame : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k),
    ∃ Φ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i), ∀ u,
      castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.FrameEquiv.frame_equiv | exact GlobalTheory.Mem.R3.LiftBrg.FrameEquiv.frame_equiv | (intros; apply GlobalTheory.Mem.R3.LiftBrg.FrameEquiv.frame_equiv <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceSupport_level_standardCoordinates : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (v : HeightOneSpectrum (𝓞 X.toD7.host.F)) (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1) (hv : Formalism.L2.Col.IsOver v Pb) (g : Bridge.Gf (Vc X.toD7 i)) (u : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹),
    ((envL X I hX U Xg tr L cV i t).isLoc x g ↔
      ∀ w : HeightOneSpectrum (𝓞 X.toD7.host.F), w ≠ v →
        Formalism.UG.bc (Formalism.UG.prV (E := X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1) ∧
    ((envL X I hX U Xg tr L cV i t).isLoc x g →
      (g ∈ (envL X I hX U Xg tr L cV i t).lev.J ↔ u ∈ Formalism.L2.Col.mhlKv X.toD7.sp.cm X.B.R.nV v)) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.SplitLoc.loc_iff | exact GlobalTheory.Mem.R3.LiftBrg.SplitLoc.loc_iff | (intros; apply GlobalTheory.Mem.R3.LiftBrg.SplitLoc.loc_iff <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftFormLevel_splits_at_offLevel_splitPlace : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (j : Bridge.Gf (Vc X.toD7 i)) (hj : j ∈ (envL X I hX U Xg tr L cV i t).lev.J),
    ∃ j₁ ∈ (envL X I hX U Xg tr L cV i t).lev.J, ∃ j₂ ∈ (envL X I hX U Xg tr L cV i t).lev.J,
      (envL X I hX U Xg tr L cV i t).isLoc x j₁ ∧ j = j₁ * j₂ ∧
      ∀ l, (envL X I hX U Xg tr L cV i t).isLoc x l → Commute j₂ l := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.LevSplitAt.lev_split_at | exact GlobalTheory.Mem.R3.LiftBrg.LevSplitAt.lev_split_at | (intros; apply GlobalTheory.Mem.R3.LiftBrg.LevSplitAt.lev_split_at <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg

theorem eta_isHecke : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (hx1 : 1 ≤ x.2) (hx2 : x.2 ≤ (Vc X.toD7 i).rank) (v : HeightOneSpectrum (𝓞 X.toD7.host.F)) (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1) (hv : Formalism.L2.Col.IsOver v Pb) (Ut : Formalism.L2.Col.MhlUnif Pb) (g : Bridge.Gf (Vc X.toD7 i)) (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * ((Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2 : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹),
    (envL X I hX U Xg tr L cV i t).isT x g := by
  intro X px I hX U Xg tr L hI hV hL cV i t A k hF x hx1 hx2 v Pb hPb hv Ut g hg
  show x.2 ≤ (Vc X.toD7 i).rank → ∃ α, IsHeckeAt (Vc X.toD7 i) (x.1.1.1 : Pl X.toD7.host.E) x.2 α ∧ (g : GL _ _) = finHom (Vc X.toD7 i) α⁻¹
  intro _
  obtain ⟨α₀, hα₀, hfin⟩ := GlobalTheory.T.exists_adelicPoint_finitePart_eq_realOne (Vc X.toD7 i) g
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_splitIdempotent_at_conjugatePrime Pb Ut
  obtain ⟨h1, h2⟩ := GlobalTheory.T.conj_uniformizer_isUniformizer_conjPrime Pb Ut
  have hβ := hL.is.βV i
  rw [hL.beta.1 i] at hβ
  have hdict := GlobalTheory.T.mem_completedSelfDualLattice_iff_integral_stdFrame (Vc X.toD7 i) (L.ΛV i) hβ
  have heps := GlobalTheory.T.conjPrimeIdempotent_mul_eq_zero_of_vanishing_at_place v Pb e hv he
  have hC : A * k ∈ Formalism.L2.DIV.St 1 := mul_mem hF.2.1 hF.2.2.2.2.1
  have hg' : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) (finHom (Vc X.toD7 i) α₀)) = A * k * ((Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2 : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ := by
    rw [hfin]; exact hg
  have hs := GlobalTheory.T.frameTransport_eta_supported_at_placeIdempotent (Vc X.toD7 i) X.B.R.nV (rkEq X i) v Pb Ut x.2 e (A * k) α₀ hv he hα₀ hg'
  have hl := GlobalTheory.T.heckeElementInv_latticeClauses_of_frameConj (Vc X.toD7 i) X.B.R.nV (rkEq X i) v Pb Ut x.2 e (A * k) α₀ he heps hdict hC hα₀ hg'
  have hd := GlobalTheory.T.heckeElement_uniformizerRatio_determinant (Vc X.toD7 i) X.B.R.nV (rkEq X i) v Pb Ut x.2 e (A * k) α₀ (by rw [rkEq X i]; exact hx2) he heps hα₀ hg'
  rw [← hPb]
  refine ⟨α₀⁻¹, ⟨e, Formalism.L2.Col.cO X.toD7.host.E Ut.π, he, h1, h2, (GfC _).inv_mem hα₀, GlobalTheory.SplitPlace.suppAt_inv hs, hl.1, hl.2, hd⟩, ?_⟩
  rw [inv_inv, hfin]

end GlobalTheory.Mem.R3.LiftBrg
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameTransport_eta_isHeckeElement_lifts : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (hx1 : 1 ≤ x.2) (hx2 : x.2 ≤ (Vc X.toD7 i).rank) (v : HeightOneSpectrum (𝓞 X.toD7.host.F)) (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1) (hv : Formalism.L2.Col.IsOver v Pb) (Ut : Formalism.L2.Col.MhlUnif Pb) (g : Bridge.Gf (Vc X.toD7 i)) (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * ((Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2 : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹),
    (envL X I hX U Xg tr L cV i t).isT x g := by
  atlas_forward_decl GlobalTheory.Mem.R3.LiftBrg.eta_isHecke
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLevelType_trivial_splitPlaceSupport : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (j : (envL X I hX U Xg tr L cV i t).lev.J) (hj : (envL X I hX U Xg tr L cV i t).isLoc x j),
    (envL X I hX U Xg tr L cV i t).lev.χ j = 1 := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.SplitChi.chi_loc_lift | exact GlobalTheory.Mem.R3.LiftBrg.SplitChi.chi_loc_lift | (intros; apply GlobalTheory.Mem.R3.LiftBrg.SplitChi.chi_loc_lift <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.SplitTie

open GlobalTheory.Mem.R3.LiftBrg

theorem frame_equiv (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) :
    ∃ Φ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i), ∀ u,
      castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ :=
  GlobalTheory.T.finiteAdelicUnitary_conj_integralFrame X I hX U Xg tr L i t A k hF

theorem loc_iff (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i))
    (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k)
    (x : (famR X I hX U Xg tr).A.ok t × ℕ) (v : HeightOneSpectrum (𝓞 X.toD7.host.F))
    (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1)
    (hv : Formalism.L2.Col.IsOver v Pb)
    (g : Bridge.Gf (Vc X.toD7 i)) (u : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV)
    (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹) :
    ((envL X I hX U Xg tr L cV i t).isLoc x g ↔
      ∀ w : HeightOneSpectrum (𝓞 X.toD7.host.F), w ≠ v →
        Formalism.UG.bc (Formalism.UG.prV (E := X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1) ∧
    ((envL X I hX U Xg tr L cV i t).isLoc x g →
      (g ∈ (envL X I hX U Xg tr L cV i t).lev.J ↔ u ∈ Formalism.L2.Col.mhlKv X.toD7.sp.cm X.B.R.nV v)) :=
  GlobalTheory.T.splitPlaceSupport_level_standardCoordinates X I hX U Xg tr L hI hV hL cV i t A k hF x v Pb hPb hv g u hg

theorem lev_split (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i))
    (i : Fin X.toD7.R.m) (t : TupU I U) (x : (famR X I hX U Xg tr).A.ok t × ℕ)
    (j : Bridge.Gf (Vc X.toD7 i)) (hj : j ∈ (envL X I hX U Xg tr L cV i t).lev.J) :
    ∃ j₁ ∈ (envL X I hX U Xg tr L cV i t).lev.J, ∃ j₂ ∈ (envL X I hX U Xg tr L cV i t).lev.J,
      (envL X I hX U Xg tr L cV i t).isLoc x j₁ ∧ j = j₁ * j₂ ∧
      ∀ l, (envL X I hX U Xg tr L cV i t).isLoc x l → Commute j₂ l :=
  GlobalTheory.T.liftFormLevel_splits_at_offLevel_splitPlace X I hX U Xg tr L hI hV hL cV i t x j hj

theorem eta_isT (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i))
    (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k)
    (x : (famR X I hX U Xg tr).A.ok t × ℕ) (hx1 : 1 ≤ x.2) (hx2 : x.2 ≤ (Vc X.toD7 i).rank)
    (v : HeightOneSpectrum (𝓞 X.toD7.host.F))
    (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1)
    (hv : Formalism.L2.Col.IsOver v Pb)
    (Ut : Formalism.L2.Col.MhlUnif Pb)
    (g : Bridge.Gf (Vc X.toD7 i))
    (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * ((Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2 : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) :
      GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹) :
    (envL X I hX U Xg tr L cV i t).isT x g :=
  GlobalTheory.T.frameTransport_eta_isHeckeElement_lifts X I hX U Xg tr L hI hV hL cV i t A k hF x hx1 hx2 v Pb hPb hv Ut g hg

theorem chi_loc_lift (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i))
    (i : Fin X.toD7.R.m) (t : TupU I U) (x : (famR X I hX U Xg tr).A.ok t × ℕ)
    (j : (envL X I hX U Xg tr L cV i t).lev.J) (hj : (envL X I hX U Xg tr L cV i t).isLoc x j) :
    (envL X I hX U Xg tr L cV i t).lev.χ j = 1 :=
  GlobalTheory.T.liftLevelType_trivial_splitPlaceSupport X I hX U Xg tr L hI hV hL cV i t x j hj

theorem isDC_map {G H : Type} [Group G] [Group H] (Φ : G ≃* H) (K : Subgroup G) (K' : Subgroup H)
    (hK : ∀ u, Φ u ∈ K' ↔ u ∈ K) {x : G} {R : Finset G} (h : Bridge.IsDC K x R) :
    Bridge.IsDC K' (Φ x) (R.map Φ.toEquiv.toEmbedding) := by
  have hK' : ∀ y : H, y ∈ K' ↔ Φ.symm y ∈ K := fun y => by rw [← hK, MulEquiv.apply_symm_apply]
  have hmem : ∀ b, b ∈ R.map Φ.toEquiv.toEmbedding ↔ Φ.symm b ∈ R := by
    intro b
    rw [Finset.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro hb
      exact ⟨Φ.symm b, hb, by simp⟩
  refine ⟨fun a ha => ?_, fun g hg => ?_⟩
  · have hu := (hmem a).1 ha
    obtain ⟨k₁, k₂, e⟩ := h.1 _ hu
    refine ⟨⟨Φ k₁, (hK _).2 k₁.2⟩, ⟨Φ k₂, (hK _).2 k₂.2⟩, ?_⟩
    show a = Φ k₁ * Φ x * Φ k₂
    rw [← map_mul, ← map_mul, ← e, MulEquiv.apply_symm_apply]
  · obtain ⟨k₁, k₂, e⟩ := hg
    have hg' : Φ.symm g = Φ.symm k₁ * x * Φ.symm k₂ := by
      rw [e, map_mul, map_mul, MulEquiv.symm_apply_apply]
    obtain ⟨a, ⟨ha, haK⟩, hu⟩ := h.2 (Φ.symm g) ⟨⟨_, (hK' _).1 k₁.2⟩, ⟨_, (hK' _).1 k₂.2⟩, hg'⟩
    refine ⟨Φ a, ⟨(hmem _).2 (by simpa using ha), ?_⟩, ?_⟩
    · rw [hK', map_mul, map_inv, MulEquiv.symm_apply_apply]
      exact haK
    · rintro b ⟨hb, hbK⟩
      have hb' := (hmem b).1 hb
      rw [hK', map_mul, map_inv] at hbK
      have := hu (Φ.symm b) ⟨hb', hbK⟩
      rw [← this, MulEquiv.apply_symm_apply]

section Std

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} {Pb : Formalism.L2.DIV.Pl E}
  (U : Formalism.L2.Col.MhlUnif Pb) (k : ℕ)

theorem rep_mem_dc {a : Formalism.L2.Col.UAd hc n}
    (ha : (QuotientGroup.mk a : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) ∈ Formalism.L2.Col.mhlCosets hc v U k) :
    ∃ κ₁ ∈ Formalism.L2.Col.mhlKv hc n v, ∃ κ₂ ∈ Formalism.L2.Col.mhlKv hc n v, a = κ₁ * Formalism.L2.Col.mhlEta hc n v U.hπ0 k * κ₂ := by
  obtain ⟨κ₁, h₁, κ₂, h₂, e⟩ := Formalism.L2.Col.mhl_cosets_out hc U k ha
  obtain ⟨h, eh⟩ := QuotientGroup.mk_out_eq_mul (Formalism.L2.Col.mhlKv hc n v) a
  refine ⟨κ₁, h₁, κ₂ * (h : Formalism.L2.Col.UAd hc n)⁻¹, Subgroup.mul_mem _ h₂ (Subgroup.inv_mem _ h.2), ?_⟩
  rw [← mul_assoc, ← e, eh, mul_inv_cancel_right]

theorem isDC_of_reps (R : Finset (Formalism.L2.Col.UAd hc n))
    (hR : Set.BijOn (fun η : Formalism.L2.Col.UAd hc n => (QuotientGroup.mk η : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v)) R
      (Formalism.L2.Col.mhlCosets hc v U k)) :
    Bridge.IsDC (Formalism.L2.Col.mhlKv hc n v) (Formalism.L2.Col.mhlEta hc n v U.hπ0 k) R := by
  refine ⟨fun a ha => ?_, fun g hg => ?_⟩
  · obtain ⟨κ₁, h₁, κ₂, h₂, e⟩ := rep_mem_dc hc U k (hR.mapsTo ha)
    exact ⟨⟨κ₁, h₁⟩, ⟨κ₂, h₂⟩, e⟩
  · obtain ⟨k₁, k₂, e⟩ := hg
    have hc' : (QuotientGroup.mk g : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) ∈ Formalism.L2.Col.mhlCosets hc v U k :=
      ⟨k₁, k₁.2, k₂, k₂.2, by rw [e]⟩
    obtain ⟨a, ha, hag⟩ := hR.surjOn hc'
    refine ⟨a, ⟨ha, QuotientGroup.eq.1 hag⟩, fun b hb => ?_⟩
    apply hR.injOn hb.1 ha
    have hag' : (QuotientGroup.mk a : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) = QuotientGroup.mk g := hag
    show (QuotientGroup.mk b : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) = QuotientGroup.mk a
    rw [hag']
    exact QuotientGroup.eq.2 hb.2

theorem reps_off (R : Finset (Formalism.L2.Col.UAd hc n))
    (hR : Set.BijOn (fun η : Formalism.L2.Col.UAd hc n => (QuotientGroup.mk η : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v)) R
      (Formalism.L2.Col.mhlCosets hc v U k)) (u : Formalism.L2.Col.UAd hc n) (hu : u ∈ R)
    (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) :
    Formalism.UG.bc (Formalism.UG.prV (E := E) w) (u : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1 := by
  obtain ⟨κ₁, h₁, κ₂, h₂, e⟩ := rep_mem_dc hc U k (hR.mapsTo hu)
  rw [e]
  exact Formalism.L2.Col.mhl_off_mul hc (Formalism.L2.Col.mhl_off_mul hc h₁.1 (Formalism.L2.Col.mhlEta_off hc U k)) h₂.1 w hw

theorem reps_bij (ST SG : Finset (Formalism.L2.DIV.Pl E)) (hov : Formalism.L2.Col.IsOver v Pb)
    (hST : ∀ Q ∈ ST, ¬ Formalism.L2.Col.IsOver v Q) (hSG : ∀ Q ∈ SG, ¬ Formalism.L2.Col.IsOver v Q)
    (hsp : Formalism.L2.Col.conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) (R : Finset (Formalism.L2.Col.UAd hc n))
    (hR : Set.BijOn (fun η : Formalism.L2.Col.UAd hc n => (QuotientGroup.mk η : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v)) R
      (Formalism.L2.Col.mhlCosets hc v U k)) (Q : Formalism.L2.DIV.Pl E) (hQ : Formalism.L2.Col.conjPrime₂ Pb = Q) (y : Formalism.L2.Col.UAd hc n) (d : Formalism.L2.Col.DecoSet E n ST SG)
    (hd : Formalism.L2.Col.decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d) :
    Set.BijOn (fun u : Formalism.L2.Col.UAd hc n => Formalism.L2.Col.decoOf ST SG ((y * u : Formalism.L2.Col.UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
      (R : Set (Formalism.L2.Col.UAd hc n)) (d.heckeSet Q.asIdeal k) := by
  subst hQ hd
  have hB := Formalism.L2.Col.mhl_split_bij' hc U k ST SG hov hST hSG hsp hk y
  have hout := Formalism.L2.Col.mhs_decoOf_out hc (v := v) ST SG hST hSG y
  refine ⟨fun u hu => ?_, fun u hu u' hu' h => ?_, fun d hd => ?_⟩
  · have := hB.mapsTo (hR.mapsTo hu)
    simp only [hout] at this
    exact this
  · have h' : Formalism.L2.Col.decoOf ST SG ((y * (QuotientGroup.mk u : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v).out : Formalism.L2.Col.UAd hc n) :
        GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        Formalism.L2.Col.decoOf ST SG ((y * (QuotientGroup.mk u' : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v).out : Formalism.L2.Col.UAd hc n) :
        GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      rw [hout, hout]; exact h
    exact hR.injOn hu hu' (hB.injOn (hR.mapsTo hu) (hR.mapsTo hu') h')
  · obtain ⟨c, hc', rfl⟩ := hB.surjOn hd
    obtain ⟨u, hu, rfl⟩ := hR.surjOn hc'
    exact ⟨u, hu, (hout u).symm⟩

end Std

theorem bijOn_map_equiv {G H T : Type} [Group G] [Group H] (Φ : G ≃* H) (R : Finset G) (S : Set T) (f : G → T) (f' : H → T)
    (hf : Set.BijOn f (R : Set G) S) (he : ∀ u, f' (Φ u) = f u) :
    Set.BijOn f' ((R.map Φ.toEquiv.toEmbedding : Finset H) : Set H) S := by
  have hmem : ∀ b, b ∈ R.map Φ.toEquiv.toEmbedding ↔ Φ.symm b ∈ R := by
    intro b
    rw [Finset.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro hb
      exact ⟨Φ.symm b, hb, by simp⟩
  refine ⟨fun b hb => ?_, fun b hb b' hb' h => ?_, fun d hd => ?_⟩
  · have := hf.mapsTo ((hmem b).1 hb)
    rwa [← he, MulEquiv.apply_symm_apply] at this
  · have h' : f (Φ.symm b) = f (Φ.symm b') := by rw [← he, ← he, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact h
    have := hf.injOn ((hmem b).1 hb) ((hmem b').1 hb') h'
    simpa using congrArg Φ this
  · obtain ⟨u, hu, rfl⟩ := hf.surjOn hd
    exact ⟨Φ u, (hmem _).2 (by simpa using hu), he u⟩

theorem ptL_frame (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι) (i : Fin X.toD7.R.m) (t : TupU I U)
    (A k : GL (Fin X.B.R.nV) (EA X)) (Φ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i))
    (hΦ : ∀ u, castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹) (hk : k ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) (w u : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) :
    ptL X I U i t A k (Φ w * Φ u) = Formalism.L2.Col.decoOf ∅ (sgL X I U t) (((⟨k, hk⟩ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) * w * u : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (EA X)) := by
  have hmul : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ w * Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ w : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) * castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) := by
    rw [Subgroup.coe_mul, map_mul, map_mul]
  show Formalism.L2.Col.decoOf ∅ (sgL X I U t) (A⁻¹ * castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ w * Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) * A * k) = _
  rw [hmul, hΦ, hΦ]
  congr 1
  simp only [Subgroup.coe_mul]
  group

theorem ptL_frame0 (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι) (i : Fin X.toD7.R.m) (t : TupU I U)
    (A k : GL (Fin X.B.R.nV) (EA X)) (Φ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i))
    (hΦ : ∀ u, castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹) (hk : k ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) (w : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) :
    ptL X I U i t A k (Φ w) = Formalism.L2.Col.decoOf ∅ (sgL X I U t) (((⟨k, hk⟩ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) * w : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (EA X)) := by
  show Formalism.L2.Col.decoOf ∅ (sgL X I U t) (A⁻¹ * castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ w : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) * A * k) = _
  rw [hΦ]
  congr 1
  simp only [Subgroup.coe_mul]
  group

theorem heckeCSD_symm_apply {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} {ST SG' : Finset (HeightOneSpectrum (𝓞 E))} (S : Formalism.L2.Col.GSD K) (h : S.Ok) (c : Formalism.L2.Col.DecoPts S E n ST SG')
    (SG : Finset (HeightOneSpectrum (𝓞 E))) (S0 : Set (HeightOneSpectrum (𝓞 E))) (x : Formalism.L2.DIV.offSub ST SG SG' S0 × ℕ)
    (f : (S.toCSD h).Forms) :
    (S.res h).symm (Formalism.L2.DIV.heckeCSD S h c SG S0 x f) = Formalism.L2.Col.heckeFam c S0 (⟨x.1.1.1, x.1.2⟩, x.2) ((S.res h).symm f) :=
  (S.res h).symm_apply_apply _

theorem op_eq_of_bij (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (cV : ∀ i, CoefA (Vc X.toD7 i))
    (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X))
    (x : (famR X I hX U Xg tr).A.ok t × ℕ) (hA : Finset (Bridge.Gf (Vc X.toD7 i)))
    (hB : ∀ g, Set.BijOn (fun a => ptL X I U i t A k (g * a)) (hA : Set (Bridge.Gf (Vc X.toD7 i)))
      ((ptL X I U i t A k g).heckeSet (x.1.1.1 : Pl X.toD7.host.E).asIdeal x.2))
    (P : PresL X I hX U Xg tr L cV i t) (hR : ReadsStd X I hX U Xg tr L cV i t A k P)
    (f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms) :
    P.ext (((famR X I hX U Xg tr).A.heckeL i t x f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms) :
      ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V) =
      Bridge.dcOp hA (P.ext (f : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) := by
  classical
  funext g
  rw [hR, Bridge.dcOp]
  simp only [hR]
  erw [heckeCSD_symm_apply]
  rw [Formalism.L2.Col.heckeFam]
  erw [Formalism.L2.Col.heckeD_op_apply]
  erw [map_sum]
  unfold Formalism.L2.Col.DecoPts.nb
  rw [Finset.sum_map]
  have hP0 := (x.1.1.1).ne_bot
  have hP1 := Formalism.L2.Col.conjIdeal_ne_bot hP0
  symm
  refine Finset.sum_nbij (fun a => ptL X I U i t A k (g * a)) ?_ ?_ ?_ ?_
  · intro a ha
    exact (Formalism.L2.Col.DecoSet.mem_heckeNb hP0 hP1 _ _ _).2 ((hB g).mapsTo ha)
  · intro a ha b hb hab
    exact (hB g).injOn ha hb hab
  · intro d hd
    have hd' := (Formalism.L2.Col.DecoSet.mem_heckeNb hP0 hP1 _ _ _).1 hd
    obtain ⟨a, ha, rfl⟩ := (hB g).surjOn hd'
    exact ⟨a, ha, rfl⟩
  · intro a _
    rw [hR]
    rfl

theorem loc_data (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i))
    (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k)
    (x : (famR X I hX U Xg tr).A.ok t × ℕ) (hx1 : 1 ≤ x.2) (hx2 : x.2 ≤ (Vc X.toD7 i).rank) :
    ∃ (hx : Bridge.Gf (Vc X.toD7 i)) (hA : Finset (Bridge.Gf (Vc X.toD7 i))),
      (envL X I hX U Xg tr L cV i t).isT x hx ∧ (∀ a ∈ hA, (envL X I hX U Xg tr L cV i t).isLoc x a) ∧
      Bridge.IsDC (envL X I hX U Xg tr L cV i t).lev.J hx hA ∧
      ∀ g, Set.BijOn (fun a => ptL X I U i t A k (g * a)) (hA : Set (Bridge.Gf (Vc X.toD7 i)))
        ((ptL X I U i t A k g).heckeSet (x.1.1.1 : Pl X.toD7.host.E).asIdeal x.2) := by
  obtain ⟨Φ, hΦ⟩ := frame_equiv X I hX U Xg tr L i t A k hF
  have hmem : (x.1.1.1 : HeightOneSpectrum (𝓞 X.toD7.host.E)) ∈ Formalism.L2.DIV.offSet (E := X.toD7.host.E) ∅ (sgL X I U t) ∅ := x.1.2
  obtain ⟨hc1, hc2, hc3⟩ := hmem
  let P : HeightOneSpectrum (𝓞 X.toD7.host.E) := x.1.1.1
  let Pb : HeightOneSpectrum (𝓞 X.toD7.host.E) := Formalism.L2.Col.conjPrime₂ P
  have hcc : Formalism.L2.Col.conjPrime₂ Pb = P := Formalism.L2.Col.conjPrime_conjPrime P
  obtain ⟨v, hov⟩ : ∃ v : HeightOneSpectrum (𝓞 X.toD7.host.F), Formalism.L2.Col.IsOver v Pb :=
    ⟨HeightOneSpectrum.under (𝓞 X.toD7.host.F) Pb, rfl⟩
  have hsp : Formalism.L2.Col.conjPrime₂ Pb ≠ Pb := by
    intro h
    apply hc1
    exact (Formalism.L2.Col.conjIdeal_asIdeal P).trans (congrArg HeightOneSpectrum.asIdeal (hcc.symm.trans h).symm)
  have hST : ∀ Q ∈ (∅ : Finset (Pl X.toD7.host.E)), ¬ Formalism.L2.Col.IsOver v Q := by simp
  have hSG : ∀ Q ∈ sgL X I U t, ¬ Formalism.L2.Col.IsOver v Q := by
    intro Q hQ hQv
    rcases Formalism.L2.Col.mhl_over_eq X.toD7.sp.cm hov Q hQv with h | h
    · exact hc3 Q (by simp [hQ]) ((congrArg HeightOneSpectrum.asIdeal h).trans (Formalism.L2.Col.conjIdeal_asIdeal P).symm)
    · have h' : Q = P := h.trans hcc
      exact hc2 (Set.mem_union_right _ (Finset.mem_coe.2 (show P ∈ sgL X I U t from h' ▸ hQ)))
  obtain ⟨Ut⟩ := Formalism.L2.Col.MhlUnif.nonempty hsp
  have hxn : x.2 ≤ X.B.R.nV := by rw [rkEq X i]; exact hx2
  obtain ⟨R, hR⟩ := Formalism.L2.Col.mhs_exists_reps X.toD7.sp.cm Ut x.2 ∅ (sgL X I U t) hov hST hSG hsp hxn
  let Off : Subgroup (Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) :=
    { carrier := {u | ∀ w, w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E := X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1}
      one_mem' := fun w _ => by rw [OneMemClass.coe_one, map_one]
      mul_mem' := fun {a b} ha hb w hw => by rw [Subgroup.coe_mul, map_mul, ha w hw, hb w hw, mul_one]
      inv_mem' := fun {a} ha w hw => by rw [InvMemClass.coe_inv, map_inv, ha w hw, inv_one] }
  have hKvOff : ∀ u, u ∈ Formalism.L2.Col.mhlKv X.toD7.sp.cm X.B.R.nV v → u ∈ Off := fun u hu => hu.1
  have hEtaOff : (Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2) ∈ Off := fun w hw => Formalism.L2.Col.mhlEta_off X.toD7.sp.cm Ut x.2 w hw
  have hoffR : ∀ u ∈ R, u ∈ Off := fun u hu w hw => reps_off X.toD7.sp.cm Ut x.2 R hR u hu w hw
  let Lc : Subgroup (Bridge.Gf (Vc X.toD7 i)) := Off.map Φ.toMonoidHom
  have hLc : ∀ u, Φ u ∈ Lc ↔ u ∈ Off := by
    intro u
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hisLoc : ∀ u, (envL X I hX U Xg tr L cV i t).isLoc x (Φ u) ↔ u ∈ Off := fun u =>
    (loc_iff X I hX U Xg tr L hI hV hL cV i t A k hF x v Pb hcc hov (Φ u) u (hΦ u)).1
  have hJ : ∀ u, u ∈ Off → (Φ u ∈ (envL X I hX U Xg tr L cV i t).lev.J ↔ u ∈ Formalism.L2.Col.mhlKv X.toD7.sp.cm X.B.R.nV v) := fun u hu =>
    (loc_iff X I hX U Xg tr L hI hV hL cV i t A k hF x v Pb hcc hov (Φ u) u (hΦ u)).2 ((hisLoc u).2 hu)
  have hLoc' : ∀ l, (envL X I hX U Xg tr L cV i t).isLoc x l ↔ l ∈ Lc := by
    intro l
    have := hisLoc (Φ.symm l)
    rw [MulEquiv.apply_symm_apply] at this
    rw [this, ← hLc, MulEquiv.apply_symm_apply]
  have hKiff : ∀ u, Φ u ∈ (envL X I hX U Xg tr L cV i t).lev.J ⊓ Lc ↔ u ∈ Formalism.L2.Col.mhlKv X.toD7.sp.cm X.B.R.nV v := by
    intro u
    constructor
    · rintro ⟨h1, h2⟩
      exact (hJ u ((hLc u).1 h2)).1 h1
    · intro h
      exact ⟨(hJ u (hKvOff u h)).2 h, (hLc u).2 (hKvOff u h)⟩
  have hmemR : ∀ a, a ∈ R.map Φ.toEquiv.toEmbedding → ∃ u ∈ R, a = Φ u := by
    intro a ha
    obtain ⟨u, hu, e⟩ := Finset.mem_map.1 ha
    exact ⟨u, hu, e.symm⟩
  have hDCl : Bridge.IsDC ((envL X I hX U Xg tr L cV i t).lev.J ⊓ Lc) (Φ (Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2)) (R.map Φ.toEquiv.toEmbedding) :=
    isDC_map Φ _ _ hKiff (isDC_of_reps X.toD7.sp.cm Ut x.2 R hR)
  have hDC : Bridge.IsDC (envL X I hX U Xg tr L cV i t).lev.J (Φ (Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2)) (R.map Φ.toEquiv.toEmbedding) := by
    refine GlobalTheory.RowPartsOrth.isDC_of_local (envL X I hX U Xg tr L cV i t).lev.J Lc (Φ (Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2)) (R.map Φ.toEquiv.toEmbedding) ((hLc _).2 hEtaOff) ?_ ?_ hDCl
    · intro j hj
      obtain ⟨j₁, hj₁, j₂, hj₂, hl₁, e, hc⟩ := lev_split X I hX U Xg tr L hI hV hL cV i t x j hj
      exact ⟨j₁, hj₁, j₂, hj₂, (hLoc' j₁).1 hl₁, e, fun l hl => hc l ((hLoc' l).2 hl)⟩
    · intro a ha
      obtain ⟨u, hu, rfl⟩ := hmemR a ha
      exact (hLc u).2 (hoffR u hu)
  refine ⟨Φ (Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2), R.map Φ.toEquiv.toEmbedding, eta_isT X I hX U Xg tr L hI hV hL cV i t A k hF x hx1 hx2 v Pb hcc hov Ut (Φ (Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2)) (hΦ _), ?_, hDC, ?_⟩
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := hmemR a ha
    exact (hisLoc u).2 (hoffR u hu)
  · intro g
    have hk : k ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := hF.2.2.2.1
    obtain ⟨w, rfl⟩ := Φ.surjective g
    exact bijOn_map_equiv Φ R _ _ _
      (reps_bij X.toD7.sp.cm Ut x.2 ∅ (sgL X I U t) hov hST hSG hsp hxn R hR P hcc ((⟨k, hk⟩ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) * w) _
        (ptL_frame0 X I U i t A k Φ hΦ hk w).symm)
      (fun u => ptL_frame X I U i t A k Φ hΦ hk w u)

theorem split_tie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) P ((famR X I hX U Xg tr).A.heckeL i t)
      (fun x => 1 ≤ x.2 ∧ x.2 ≤ (Vc X.toD7 i).rank) (LiftBrg.envL X I hX U Xg tr L cV i t).isT
      (LiftBrg.envL X I hX U Xg tr L cV i t).isLoc) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t A k hF P hR
  have key : ∀ x : (famR X I hX U Xg tr).A.ok t × ℕ, 1 ≤ x.2 ∧ x.2 ≤ (Vc X.toD7 i).rank →
      ∃ (hx : Bridge.Gf (Vc X.toD7 i)) (hA : Finset (Bridge.Gf (Vc X.toD7 i))),
        (envL X I hX U Xg tr L cV i t).isT x hx ∧ (∀ a ∈ hA, (envL X I hX U Xg tr L cV i t).isLoc x a) ∧ Bridge.IsDC (envL X I hX U Xg tr L cV i t).lev.J hx hA ∧
        ∀ f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms,
          P.ext (((famR X I hX U Xg tr).A.heckeL i t x f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms) :
            ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V) =
          Bridge.dcOp hA (P.ext (f : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) := by
    intro x hx
    obtain ⟨hx', hA, h1, h2, h3, h4⟩ := loc_data X I hX U Xg tr L hI hV hL cV i t A k hF x hx.1 hx.2
    exact ⟨hx', hA, h1, h2, h3, fun f => op_eq_of_bij X I hX U Xg tr L cV i t A k x hA h4 P hR f⟩
  choose! hxf hAf hxok hAloc hDC hop using key
  exact ⟨⟨hxf, hAf, hxok, hAloc, fun x _ j hj => chi_loc_lift X I hX U Xg tr L hI hV hL cV i t x j hj, hDC, hop⟩⟩

end GlobalTheory.Mem.R3.LiftBrg.SplitTie
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitHecke_operators_lifts_doubleCoset : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) P ((famR X I hX U Xg tr).A.heckeL i t)
      (fun x => 1 ≤ x.2 ∧ x.2 ≤ (Vc X.toD7 i).rank) (LiftBrg.envL X I hX U Xg tr L cV i t).isT
      (LiftBrg.envL X I hX U Xg tr L cV i t).isLoc) := by
  atlas_forward_decl GlobalTheory.Mem.R3.LiftBrg.SplitTie.split_tie
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelChar_eq_one_inert_prime_off_level : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (j : (LiftBrg.envL X I hX U Xg tr L cV i t).lev.J),
    IsLocElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 (j : Bridge.Gf (Vc X.toD7 i)) → (LiftBrg.envL X I hX U Xg tr L cV i t).lev.χ j = 1 := by
  first | exact @GlobalTheory.Mem.R3.LiftInertChi.levChi_eq_one_of_isLocElt | exact GlobalTheory.Mem.R3.LiftInertChi.levChi_eq_one_of_isLocElt | (intros; apply GlobalTheory.Mem.R3.LiftInertChi.levChi_eq_one_of_isLocElt <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertNeighbours_lifts_doubleCoset_translates : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ q : ↑((famR X I hX U Xg tr).okI t) × List ℕ, Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2 →
    ∃ (x : Bridge.Gf (Vc X.toD7 i)) (R : Finset (Bridge.Gf (Vc X.toD7 i))),
      IsLabElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank q.2) x ∧
      (∀ a ∈ R, IsLocElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 a) ∧
      Bridge.IsDC (LiftBrg.envL X I hX U Xg tr L cV i t).lev.J x R ∧
      ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet X.toD7.host.E X.B.R.nV ∅ (LiftBrg.sgL X I U t) → M)
        (g : Bridge.Gf (Vc X.toD7 i)),
        ∑ a ∈ R, ψ (LiftBrg.ptL X I U i t A k (g * a)) =
          ∑ e ∈ (LiftBrg.ptL X I U i t A k g).inertNb ((q.1.1 : PlI X.B px).1).asIdeal q.2, ψ e := by
  first | exact @GlobalTheory.InertNbr.inert_neighbours | exact GlobalTheory.InertNbr.inert_neighbours | (intros; apply GlobalTheory.InertNbr.inert_neighbours <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.InertTie

theorem conj_symm_apply {K M N : Type} [CommSemiring K] [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (e : M ≃ₗ[K] N) (T : Module.End K M) (x : N) : e.symm (e.conj T x) = T (e.symm x) := by
  simp [LinearEquiv.conj_apply]

theorem opEq (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X))
    (P : LiftBrg.PresL X I hX U Xg tr L cV i t) (hP : LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P)
    (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (R : Finset (Bridge.Gf (Vc X.toD7 i)))
    (hN : ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet X.toD7.host.E X.B.R.nV ∅ (LiftBrg.sgL X I U t) → M)
        (g : Bridge.Gf (Vc X.toD7 i)),
        ∑ a ∈ R, ψ (LiftBrg.ptL X I U i t A k (g * a)) =
          ∑ e ∈ (LiftBrg.ptL X I U i t A k g).inertNb ((q.1.1 : PlI X.B px).1).asIdeal q.2, ψ e)
    (f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms) :
    P.ext ((((famR X I hX U Xg tr).heckeLI i t q f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms) :
        ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) =
      Bridge.dcOp R (P.ext (f : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) := by
  funext g
  rw [hP]
  unfold Bridge.dcOp
  rw [Finset.sum_congr rfl (fun a _ => hP f (g * a))]
  rw [hN _ (fun e => P.coef ((((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm f).1 e)) g]
  refine (congrArg P.coef ?_).trans (map_sum P.coef _ _)
  change (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm
        (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).conj
        (Formalism.L2.Col.heckeFamI (formPts _ _) ∅ (offSubI.lev q.1, q.2)) f)).1 _ = _
  erw [conj_symm_apply]
  erw [Formalism.L2.Col.heckeI_op_apply]
  unfold Formalism.L2.Col.DecoPts.nbI
  simp [formPts]
  rfl

theorem exists_inertTie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) P ((famR X I hX U Xg tr).heckeLI i t)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank k.2)
      (fun k => IsLabElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank k.2))
      fun k => IsLocElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t A k hF P hR
  classical
  have hN := fun (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ)
      (hq : Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2) =>
    GlobalTheory.T.inertNeighbours_lifts_doubleCoset_translates X px I hX U Xg tr L eG hI hV hL hG cV i t A k hF q hq
  exact ⟨{
    hx := fun q => if hq : Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2 then (hN q hq).choose else 1
    hA := fun q => if hq : Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2 then (hN q hq).choose_spec.choose else ∅
    hx_ok := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.1
    hA_loc := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.1
    chi_loc := fun q _ j hj => GlobalTheory.T.levelChar_eq_one_inert_prime_off_level X px I hX U Xg tr L eG hI hV hL hG cV i t q j hj
    hDC := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.2.1
    op_eq := fun q hq f => by
      simp only [dif_pos hq]
      exact opEq X I hX U Xg tr L cV i t A k P hR q _ (hN q hq).choose_spec.choose_spec.2.2.2 f }⟩

end GlobalTheory.Mem.R3.LiftBrg.InertTie
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertHecke_doubleCosetOperators_lifts : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) P ((famR X I hX U Xg tr).heckeLI i t)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank k.2)
      (fun k => IsLabElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank k.2))
      fun k => IsLocElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1) := by
  atlas_forward_decl GlobalTheory.Mem.R3.LiftBrg.InertTie.exists_inertTie
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg

set_option maxHeartbeats 4000000 in

theorem exists_liftSide : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 → Seed.FrmC.StdLat (Vc X.toD7 i) → ∃ s : ∀ t, Seed.LiftSideT (famR X I hX U Xg tr) L cV (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) i t, (∀ t,       (∀ q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
        eG ((s t).act_tie.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL _ _))) ∧
      Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef (s t).pres (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) (s t).pres ((famR X I hX U Xg tr).heckeLI i t)
        (fun k => Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank k.2)
        (fun k => IsLabElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank k.2))
        fun k => IsLocElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1)) ∧ BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (s t).pres.extL φ) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i c0L hcV hmap hin hβ hg _
  obtain ⟨c, hc, hP⟩ := GlobalTheory.T.exists_common_coefficientMap_liftPresentation X px I hX U Xg tr L eG hI hV hL hG cV i c0L hcV hmap hin hβ hg
  choose P hR hco hC using hP
  have hF : ∀ t, FrameOK X I U i t 1 1 := fun t => GlobalTheory.T.identity_integralUnitaryFrameCoordinates_of_unitGram X px I U i t hg
  choose a ha using fun t => GlobalTheory.T.exists_finiteGroupAction_liftForms_rightTranslation X px I hX U Xg tr L eG hI hV hL hG cV i t 1 1 (hF t) (P t) (hR t)
  have hk := fun t => GlobalTheory.T.splitHecke_operators_lifts_doubleCoset X px I hX U Xg tr L eG hI hV hL hG cV i t 1 1 (hF t) (P t) (hR t)
  have hki := fun t => GlobalTheory.T.exists_inertHecke_doubleCosetOperators_lifts X px I hX U Xg tr L eG hI hV hL hG cV i t 1 1 (hF t) (P t) (hR t)
  exact ⟨fun t => Bridge.SideRealG.mk (P t) (a t) (Classical.choice (hk t)), fun t => ⟨ha t, hC t, hki t⟩,
    GlobalTheory.T.standardLiftReading_of_decoratedLatticePresentations X px I hX U Xg tr L eG hI hV hL hG cV i hβ hg c hc P hR hco⟩

end GlobalTheory.Mem.R3.LiftBrg
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_liftForms_adelic_decoratedLattices : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 → Seed.FrmC.StdLat (Vc X.toD7 i) → ∃ s : ∀ t, Seed.LiftSideT (famR X I hX U Xg tr) L cV (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) i t, (∀ t,       (∀ q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
        eG ((s t).act_tie.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL _ _))) ∧
      Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef (s t).pres (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) (s t).pres ((famR X I hX U Xg tr).heckeLI i t)
        (fun k => Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank k.2)
        (fun k => IsLabElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank k.2))
        fun k => IsLocElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1)) ∧ BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (s t).pres.extL φ) := by
  atlas_forward_decl GlobalTheory.Mem.R3.LiftBrg.exists_liftSide
end
