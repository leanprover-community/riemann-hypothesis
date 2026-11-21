import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEstimateImpliesFrameAutomorphyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEstimateImpliesFrameAutomorphy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphyFromSmallExponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphyFromSmallExponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceBlockDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceBlockDecomposition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceFiniteSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceFiniteSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceBlockBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceBlockBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlacePrimeLocal

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameAut
open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame
section Op
variable (K : Type) [CommRing K] (n : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)
end Op
end GlobalTheory.FrameAut
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL
namespace GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
def AutStAlt : Prop := _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P W w => AutAt p j P W w
end GlobalTheory.FrameAut
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameLab
variable {D : D7}
theorem labels_ok_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W _ _ w _ _ _ Q
  obtain ⟨-, h2, h3⟩ := (GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
    p.charW.base.lev).2.2.2 p.charW.base.fam (p.R.mu w) Q.1 Q.2
  refine ⟨⟨plOf p j (p.R.mu w) Q, fun e => h2 e.symm, (under_conjPl _).symm⟩, under_conjPl _,
    (absNorm_conjPl _).trans h3.symm, mem_conjPl_of_fixed _ (map_natCast _ _)⟩
end GlobalTheory.FrameLab
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_place_block_decomposition_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal) := by
  atlas_forward_decl _root_.GlobalTheory.FrameLab.labels_ok_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameAutCof
theorem cofinite_labels_at_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite :=
  fun p _ _ j _ _ _ _ w _ _ hs => cofinite_labels p j (p.R.mu w) hs.1.ne_zero
end GlobalTheory.FrameAutCof
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_place_finite_set_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite := by
  atlas_forward_decl _root_.GlobalTheory.FrameAutCof.cofinite_labels_at_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameAut
theorem norm_sq_blockValue_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W _ _ w _ _ _ ν hν Q
  have h := norm_sq_firstValA p.R.toRealDat p.F.lv2 p.charW.base.lev p.charW.base.fam j (p.R.mu w) Q.1 Q.2
  obtain rfl : ν = fun Q => Formalism.L2.Col.firstValA (p.P.A3.A.muVal j (p.R.mu w)) p.P.A3.A.etaVal p.P.A3.A.q p.P.A3.A.r Q.1 :=
    List.mem_singleton.1 hν
  have e : (blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t = p.P.A3.A.r := Nat.add_sub_cancel ..
  rw [e]
  exact h
end GlobalTheory.FrameAut
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sq_emb_block_eq_q_pow_of_small_at : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t) := by
  atlas_forward_decl _root_.GlobalTheory.FrameAut.norm_sq_blockValue_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
private theorem emb_cj_pz {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (io : PadicAlgCl l ≃+* ℂ)
    (τ : E →+* PadicAlgCl l) :
    io.toRingHom.comp (GlobalTheory.ExpFrame.cj τ) = ComplexEmbedding.conjugate (io.toRingHom.comp τ) := by
  ext x
  exact IsCMField.complexEmbedding_complexConj E (io.toRingHom.comp τ) x
private theorem places_inj_pz {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (io : PadicAlgCl l ≃+* ℂ)
    {ι : Type} {inc : ι → (E →+* PadicAlgCl l)} (h : IsHalf inc) :
    Function.Injective fun τ => InfinitePlace.mk (io.toRingHom.comp (inc τ)) := by
  intro τ τ' e
  have hi : ∀ a b : E →+* PadicAlgCl l, io.toRingHom.comp a = io.toRingHom.comp b → a = b := fun a b hab =>
    RingHom.ext fun x => io.injective (RingHom.congr_fun hab x)
  rcases InfinitePlace.mk_eq_iff.1 e with e | e
  · exact h.1 (hi _ _ e)
  · exact absurd (hi _ _ ((emb_cj_pz io _).trans e)) (h.2.1 τ τ')
set_option maxHeartbeats 1600000 in
private theorem frame_embedding_exists {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
    (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : N = (Vc D j).rank)
    (F : Frame l D.what₂.Tau N) (e0 : D.what₂.LL →+* PadicAlgCl l) (ix : F.I → (blk p j t).Pl × ℕ)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)) (T : Tied p j t F e0 ix inc)
    (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (hmu : ∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res N (mu τ))) (hθ : F.IsEig mu θ) :
    ∃ π : Submodule ℂ (UA D.host.E N → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight N, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧
        (∀ v, GlobalTheory.Hk3.Good p.R.toRealDat t v → ∀ x ∈ locU N v, cLoc v x ∈ GlobalTheory.LFun.KGL v N → RU D.host.E N x φ = φ) ∧
        ∀ Q : (blk p j t).Pl, (∀ x ∈ locU N (labOf p j t Q), cLoc (labOf p j t Q) x ∈ GlobalTheory.LFun.KGL (labOf p j t Q) N →
          RU D.host.E N x φ = φ) ∧
        ∀ i, (ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E N).comp (locU N (labOf p j t Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j t Q) N).comap ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j t Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab N (ix i).2))
              ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype x)) φ = T.io (θ i) • φ := by
  subst hN
  classical
  have hs : (Vc D j).SigOK := D.sp.V_sig _
  have hp : (Vc D j).IsPosDef := p.vpos j
  have hinf : Formalism.L2.Theta.IsInfFam p.R.θ := p.charW.base.models.inf
  obtain ⟨jj, h₀, hTr⟩ := GlobalTheory.DefTransfer.exists_isTransfer D (Vc D j) p.R.θ hinf hs hp
  obtain ⟨B, hB1, hB2⟩ := UpperTheory.exists_invariant_posDef_hermitian_form_autForm_unitary D (Vc D j) hs hp jj hTr.2.1
  obtain ⟨Fm, hF0, hFl, hFr, hFh⟩ := UpperTheory.exists_nonzero_vectorValued_eigenform_unitary p j t F e0 ix inc T mu θ hθ
  have hb : ∀ τ, T.io.toRingHom.comp (e0.comp (Links.labLL D τ)) = Formalism.BasicNotions.TH.tauE D τ := fun τ => by
    rw [← Formalism.IndefR.Conj.labE_base τ]
    exact RingHom.ext fun x => T.liftFrame_embedding_base _
  have hemb : ∀ τ, T.io.toRingHom.comp (inc τ) = Formalism.BasicNotions.TH.tauE D τ ∨
      T.io.toRingHom.comp (inc τ) = ComplexEmbedding.conjugate (Formalism.BasicNotions.TH.tauE D τ) := fun τ => by
    rcases T.lab τ with h | h
    · exact Or.inl (by rw [h, hb])
    · exact Or.inr (by rw [h, emb_cj_pz, hb])
  have hfix : ∀ (k : Formalism.L2.Theta.GA D (Vc D j)), (∃ h : (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k ∈ levJ p j t,
      levChi p j t ⟨_, h⟩ = 1) → ∀ g, Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k) = Fm g := by
    rintro k ⟨h, h1⟩ g
    have := hFr ⟨_, h⟩ g
    rw [h1, Units.val_one, one_smul] at this
    exact this
  have hev : ∀ᶠ κ in nhds (1 : Formalism.L2.Theta.GA D (Vc D j)), ∀ g,
      Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict κ) = Fm g :=
    (GlobalTheory.ThetaIntegrand.eventually_level (Vc D j) (p.R.βV j) (p.R.datVt j t)).mono fun κ h => hfix κ h
  obtain ⟨F1, h10, h1l, h1i, h1e, A, hA⟩ := UpperTheory.vectorValued_autForm_equivariant_infinite_component D (Vc D j) p.R.θ jj h₀ hinf hTr
    (fun τ => T.io.toRingHom.comp (inc τ)) hemb mu T.sh Fm hF0 hFl hev
  let lam : D.what₂.Tau → DomWeight (Vc D j).rank := fun τ =>
    ⟨fun a => (mu τ a : ℤ) + T.sh τ, fun a b hab => add_le_add_left (Int.ofNat_le.2 (hmu τ hab)) _⟩
  obtain ⟨π, hπ, hw, φ, hφ, hφ0, hsum⟩ := UpperTheory.exists_unitaryAutomorphicForm_of_weightVectorValued D.host.E (Vc D j).rank D.what₂.Tau (fun τ => T.io.toRingHom.comp (inc τ))
    (places_inj_pz T.io T.half) mu T.sh lam (fun _ _ => rfl) B hB1 hB2 F1 h10 h1l h1i h1e
  have htr : ∀ g y, F1 (g * y) = A (Fm ((Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict (jj g * h₀) *
      (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict (GlobalTheory.DefTransfer.cj jj h₀ y))) := fun g y => by
    rw [hA, ← map_mul, GlobalTheory.DefTransfer.cj_apply, map_mul jj]
    congr 3
    group
  have hK : ∀ v v', GlobalTheory.Hk3.Good p.R.toRealDat t v' → GlobalTheory.Hk3.hyp (Vc D j) v = GlobalTheory.Hk3.hyp (Vc D j) v' →
      ∀ x ∈ GlobalTheory.DefTransfer.KP (Vc D j).rank v, RU D.host.E (Vc D j).rank x φ = φ := by
    intro v v' hg he x hx
    have h1 := (hTr.2.2.2.2.2.2.1 v x).2 hx
    rw [he] at h1
    have h2 := hfix _ (UpperTheory.levChi_eq_one_of_good_place p j t v' hg _ h1)
    have := hsum Unit Finset.univ (fun _ => x) 1 (fun _ _ => hx.1.1) fun g => by
      rw [Finset.univ_unique, Finset.sum_singleton, one_smul, htr, h2, hA]
    simpa using this
  refine ⟨π, hπ, fun τ => ⟨lam τ, fun _ => rfl, hw τ, ?_⟩, φ, hφ, hφ0, fun v hv x h1 h2 => hK v v hv rfl x ⟨h1, h2⟩, fun Q => ?_⟩
  · rw [emb_cj_pz]
    exact GlobalTheory.DefU.AU.HasWt.conjugate (π := GlobalTheory.DefU.AU.mk ⟨π, hπ⟩) (hw τ)
  have hg : GlobalTheory.Hk3.Good p.R.toRealDat t (plOf p j t Q) :=
    ((GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
      p.charW.base.lev).2.2.2 p.charW.base.fam t Q.1 Q.2).1
  have hKQ := hK (labOf p j t Q) _ hg (GlobalTheory.SphConj.hyp_conj _ _)
  refine ⟨fun x h1 h2 => hKQ x ⟨h1, h2⟩, fun i hi => ?_⟩
  subst hi
  obtain ⟨r1, r2, -⟩ := (T.ix_range (ix i)).1 ⟨i, rfl⟩
  obtain ⟨hloc, R, hR, hRs⟩ := UpperTheory.exists_sphericalHeckeRep_splitLabel_of_offLevelPlace p j t (ix i).1 (ix i).2 r1 r2
  rw [GlobalTheory.SplitTransfer.heckeVec_divInd hTr hKQ hR]
  refine hsum _ R (fun γ => (GlobalTheory.DefTransfer.cj jj h₀).symm γ) _ (fun γ hγ => ((hTr.2.2.2.2.2.2.2 _ _ R hR).1 γ hγ).1.1) fun g => ?_
  simp only [htr, MulEquiv.apply_symm_apply]
  rw [← map_sum, hRs _ Fm hFr, hA, ← map_smul]
  exact congrArg A (hFh i hloc _)
theorem _root_.GlobalTheory.T.small_place_prime_local_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
      (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
      (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π : Submodule ℂ (UA D.host.E P.Nr → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight P.Nr, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧ ∀ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal →
        (∀ x ∈ locU P.Nr (labOf p j (p.R.mu w) Q), cLoc (labOf p j (p.R.mu w) Q) x ∈ GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) P.Nr →
          RU D.host.E P.Nr x φ = φ) ∧
        ∀ i, (R.ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E P.Nr).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) P.Nr).comap ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j (p.R.mu w) Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab P.Nr (R.ix i).2))
              ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype x)) φ = T.io (θ i) • φ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W hD _ w hw hW _ _ F R inc T mu θ hmu hθ
  obtain ⟨π, h1, h2, φ, h3, h4, h5, h6⟩ := frame_embedding_exists p j (p.R.mu w) hD.Nr F R.e0 R.ix inc T mu θ hmu hθ
  exact ⟨π, h1, h2, fun v hv => ⟨φ, h3, h4, h5 v (UpperTheory.good_place_of_twist_place_dividing p j P W hD w hw hW v hv)⟩, φ, h3, h4, fun Q _ => h6 Q⟩
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameAut
theorem autAt_of_alt (hLab : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal)) (hCof : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite) (hBl : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t)) (hSat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ φ ∈ π, φ ≠ 0 →
    (∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w n → RU E n x φ = φ) →
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ S ∧
      ∀ k ≤ n, GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n w).subtype) ((GlobalTheory.LFun.KGL w n).comap ((cLoc w).comp (locU n w).subtype))
        (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E w) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k)) ((cLoc w).comp (locU n w).subtype x)) φ =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n S k • φ) (hAut : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
      (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
      (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π : Submodule ℂ (UA D.host.E P.Nr → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight P.Nr, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧ ∀ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal →
        (∀ x ∈ locU P.Nr (labOf p j (p.R.mu w) Q), cLoc (labOf p j (p.R.mu w) Q) x ∈ GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) P.Nr →
          RU D.host.E P.Nr x φ = φ) ∧
        ∀ i, (R.ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E P.Nr).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) P.Nr).comap ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j (p.R.mu w) Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab P.Nr (R.ix i).2))
              ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype x)) φ = T.io (θ i) • φ) :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w → AutAt p j P W w := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hr hm j P W hd hn w hw hwr hs
  refine ⟨⟨hLab p hr hm j P W hd hn w hw hwr hs, hCof p hr hm j P W hd hn w hw hwr hs, hBl p hr hm j P W hd hn w hw hwr hs⟩, ?_⟩
  intro _ F R inc T mu θ hmu hE
  obtain ⟨π, hπ, hwt, hl, φ, hφ, hφ0, hQ⟩ := hAut p hr hm j P W hd hn w hw hwr hs F R inc T mu θ hmu hE
  refine ⟨π, hπ, hwt, hl, fun Q => ?_⟩
  have hlab := hLab p hr hm j P W hd hn w hw hwr hs Q
  by_cases hQl : ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal
  · have hun := hl _ (hlab.2.2.2.2 hQl)
    obtain ⟨ψ, hψ, hψ0, hψfix⟩ := hun
    obtain ⟨σ, S, hc, hsat, -⟩ := hSat _ _ π hπ _ hlab.1 ψ hψ hψ0 hψfix
    refine ⟨⟨ψ, hψ, hψ0, hψfix⟩, σ, S, hc, hsat, fun i hi => ?_⟩
    exact absurd (hi ▸ hQl) ((T.ix_range (R.ix i)).1 ⟨i, rfl⟩).2.2
  · obtain ⟨hfix, heig⟩ := hQ Q hQl
    obtain ⟨σ, S, hc, hsat, hk⟩ := hSat _ _ π hπ _ hlab.1 φ hφ hφ0 hfix
    refine ⟨⟨φ, hφ, hφ0, hfix⟩, σ, S, hc, hsat, fun i hi => ?_⟩
    have hle := ((T.ix_range (R.ix i)).1 ⟨i, rfl⟩).2.1
    exact smul_left_injective ℂ hφ0 ((heig i hi).symm.trans (hk _ hle))
theorem autSt_of_alt (hLab : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal)) (hCof : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite) (hBl : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t)) (hSat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ φ ∈ π, φ ≠ 0 →
    (∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w n → RU E n x φ = φ) →
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ S ∧
      ∀ k ≤ n, GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n w).subtype) ((GlobalTheory.LFun.KGL w n).comap ((cLoc w).comp (locU n w).subtype))
        (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E w) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k)) ((cLoc w).comp (locU n w).subtype x)) φ =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n S k • φ) (hAut : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
      (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
      (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π : Submodule ℂ (UA D.host.E P.Nr → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight P.Nr, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧ ∀ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal →
        (∀ x ∈ locU P.Nr (labOf p j (p.R.mu w) Q), cLoc (labOf p j (p.R.mu w) Q) x ∈ GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) P.Nr →
          RU D.host.E P.Nr x φ = φ) ∧
        ∀ i, (R.ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E P.Nr).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) P.Nr).comap ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j (p.R.mu w) Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab P.Nr (R.ix i).2))
              ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype x)) φ = T.io (θ i) • φ) :
    _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt := by
  intro hS
  obtain ⟨ε1, he, H⟩ := hS
  refine ⟨ε1, he, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := H eps h1 h2
  refine ⟨K, fun Fm CH hc hl => ?_⟩
  obtain ⟨x0, hx0⟩ := hK Fm CH hc hl
  exact ⟨x0, fun x hx hxx i p hr hm j P W hd hn w hw hwr =>
    _root_.GlobalTheory.FrameAut.autAt_of_alt hLab hCof hBl hSat hAut p hr hm j P W hd hn w hw hwr (hx0 x hx hxx i p hr hm j P W hd hn w hw hwr)⟩
theorem autSt_of_smallSt' : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt :=
  _root_.GlobalTheory.FrameAut.autSt_of_alt _root_.GlobalTheory.T.small_place_block_decomposition_alt _root_.GlobalTheory.T.small_place_finite_set_alt _root_.GlobalTheory.T.norm_sq_emb_block_eq_q_pow_of_small_at GlobalTheory.T.exists_satake_sphericalVector_definiteUnitary _root_.GlobalTheory.T.small_place_prime_local_alt
end GlobalTheory.FrameAut
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aut_statement_of_small_exponent_statement : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt := by
  atlas_forward_decl _root_.GlobalTheory.FrameAut.autSt_of_smallSt'
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
theorem GlobalTheory.FrameAut.frame_autSt_of_smallSt : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt :=
  _root_.GlobalTheory.T.aut_statement_of_small_exponent_statement
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_aut_of_small_estimate : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt := by
  atlas_forward_decl _root_.GlobalTheory.FrameAut.frame_autSt_of_smallSt
end
end
