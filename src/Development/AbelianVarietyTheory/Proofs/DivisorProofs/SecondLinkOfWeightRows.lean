import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalOf
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaLiftAdjointScalarOnPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterUpdateOfWeakRealisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsUniformLinksRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibilityStatement

section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.BigOn

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem isLev_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.toLevCh.Is A.μ0) :
    (reScal R lam kap).toLevCh.Is A.μ0 := h

theorem isGrp_reScal (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsGrp F) :
    (reScal R lam kap).IsGrp F := { h with }

theorem isFam_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsFam) :
    (reScal R lam kap).IsFam := { h with }

theorem isModels_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsModels) :
    (reScal R lam kap).IsModels := { h with }

theorem isChain_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsChain) :
    (reScal R lam kap).IsChain := { h with }

theorem isThP_rescale (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsThP) :
    (reScal R lam kap).IsThP := { h with }

def reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) : CxData B :=
  { X with lam := lam, κ := κ }

theorem liftMatC_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) {fc : DefSub B → DefFace Bs} (cr : Crd B fc)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) :
    (reScalCx X lam κ).liftMatC cr b j t = X.liftMatC cr b j t := rfl

theorem liftMat_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) {fc : DefSub B → DefFace Bs} (cr : Crd B fc)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) :
    (reScalCx X lam κ).liftMat cr b j t = X.liftMat cr b j t :=
  congrArg (kMat Bs.v0.embedding) (liftMatC_reScalCx X lam κ cr b j t)

theorem iw_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) {fc : DefSub B → DefFace Bs} (cr : Crd B fc)
    (b : Bool) : ((reScalCx X lam κ).data cr b).Iw = (X.data cr b).Iw := by
  funext j t w
  exact congrArg (fun θ => idx w (X.M b j) (matLat θ ((lv (fc X.zs) b).Tl j t))) (liftMat_reScalCx X lam κ cr b j t)

theorem zs_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) : (reScalCx X lam κ).zs = X.zs := rfl

set_option maxHeartbeats 1000000 in
theorem toCx_reScal (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ) :
    (reScal R lam kap).toCx F = reScalCx (R.toCx F) lam (fun _ => kap) := rfl

theorem reScal_nonzeroIndexPlace_iff (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : (reScal R lam kap).NonzeroIndexPlace F w ↔ R.NonzeroIndexPlace F w := by
  unfold RealDat.NonzeroIndexPlace
  rw [toCx_reScal, iw_reScalCx, zs_reScalCx]

theorem isTup_reScal (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsTup F) :
    (reScal R lam kap).IsTup F :=
  ⟨fun w hw => h.tw w ((reScal_nonzeroIndexPlace_iff R F lam kap w).1 hw), h.mu_off, h.mu_used, h.mu_ne, h.mu_conj, h.mu_on⟩

end

theorem char_charOf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → R.IsThP → R.IsTup F → (charOf R F).Char F := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h1 h2 h3 h4 h5 h6 h7
  obtain ⟨lam, kap, hs⟩ := GlobalTheory.ScalChoice.exists_isScal D G Pl0 T0 A Ks R F
  have hex : ∃ q : (type_of% R.lam) × ℝ, (reScal R q.1 q.2).Char F :=
    ⟨(lam, kap), isLev_reScal R lam kap h1, isGrp_reScal R F lam kap h2, isFam_reScal R lam kap h3,
      isModels_reScal R lam kap h4, isChain_reScal R lam kap h5, isThP_rescale R lam kap h6, hs,
      isTup_reScal R F lam kap h7⟩
  exact Classical.epsilon_spec hex

end GlobalTheory.BigOn
end

section
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
open GlobalTheory.CharRealise
open Formalism.DivisionValues

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

set_option maxHeartbeats 4000000 in

theorem splitPartFace_baseLevel_indices_eq (i : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (p.S false).Iw i p.P.A3.A.μ0 w = ((p.R.toRealDat.toCx (F2 p)).data (F2 p).cr false).Iw i p.P.A3.A.μ0 w := by
  show ((p.R.toCx3 p.F).data p.F.cr false).Iw i _ w = _
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl

set_option maxHeartbeats 4000000 in

theorem splitPartFace_baseLevel_jw_eq (i : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    jw ((lv (p.F.fc (p.R.toCx3 p.F).zs) false).HT i p.P.A3.A.μ0) w ((lv (p.F.fc (p.R.toCx3 p.F).zs) false).Tl i p.P.A3.A.μ0) =
      jw ((lv ((F2 p).fc (p.R.toRealDat.toCx (F2 p)).zs) false).HT i p.P.A3.A.μ0) w
        ((lv ((F2 p).fc (p.R.toRealDat.toCx (F2 p)).zs) false).Tl i p.P.A3.A.μ0) := by
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl

set_option maxHeartbeats 4000000 in

theorem w1_of_inW1_split_part (C CH : ℝ) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (h : p.R.toRealDat.NonzeroIndexPlace (F2 p) w) :
    (p.R.toCx3 p.F).W1 p.F.cr (p.N C CH) w := by
  obtain ⟨w', hw', i, h⟩ := h
  refine ⟨i, ?_⟩
  rcases hw' with rfl | rfl
  · rcases h with h | h | h | h | h
    · exact Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h)
    · exact Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h))
    · exact Or.inr (Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_jw_eq p i _) h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rcases h with h | h | h | h | h
    · exact Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h))
    · rw [ValuationRepresentative.conjPl_conjPl] at h
      exact Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_jw_eq p i _) h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · rw [ValuationRepresentative.conjPl_conjPl] at h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem tupTw_of_w1Row : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz),
    SingleIndexPlacesAreTwisted p → p.R.toRealDat.tup_tw (F2 p) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p h w hw
  exact h w (w1_of_inW1_split_part p 0 0 w hw)

end GlobalTheory.BigOn

end
end

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPart_nonzeroIndexPlaces_twisted : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), SingleIndexPlacesAreTwisted p → p.R.toRealDat.tup_tw (F2 p) := by
  atlas_forward_decl GlobalTheory.BigOn.tupTw_of_w1Row
end

section
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem splitPartRealisationWithScalars_char_of_weak : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.R.toRealDat.ExAt → SingleIndexPlacesAreTwisted p → (R2 p).Char (F2 p) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hE hW
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak p.charW hE
  exact GlobalTheory.BigOn.char_charOf D _ _ _ p.P.A3.A _ p.R.toRealDat (F2 p) hc.lev ⟨hc.grp.red_R, hc.grp.red_L, hc.grp.levels, hc.grp.record, hc.grp.chiW⟩ hc.fam hc.models hc.chain hc.thP
    ⟨GlobalTheory.T.splitPart_nonzeroIndexPlaces_twisted D L hT Gi Gl Kc Y cX ex Csz p hW, hc.tup.mu_off, hc.tup.mu_used, hc.tup.mu_ne, hc.tup.mu_conj, hc.tup.mu_on⟩

end GlobalTheory.BigOn
end

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.char_R2_of_exAt_of_singleIndexPlacesTwisted : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.R.toRealDat.ExAt → SingleIndexPlacesAreTwisted p → (R2 p).Char (F2 p) := by
  atlas_forward_decl GlobalTheory.BigOn.splitPartRealisationWithScalars_char_of_weak
end

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

namespace GlobalTheory.BigOn

theorem links2_of_rows : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz),
    p.Rows → SingleIndexPlacesAreTwisted p → Links2 p := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hr hw
  obtain ⟨hU, hB, hR⟩ := GlobalTheory.T.split_rows_uniform_links_rank D L hT Gi Gl Kc Y cX ex Csz p hr
  obtain ⟨hBar, hPin, hPh⟩ := GlobalTheory.T.split_rows_bar_phase_compatibility D L hT Gi Gl Kc Y cX ex Csz p hr
  exact ⟨GlobalTheory.T.char_R2_of_exAt_of_singleIndexPlacesTwisted D L hT Gi Gl Kc Y cX ex Csz p hr.exAt hw, hr.ok.ok2, hU, hB, hR, hBar, hPin, hPh⟩

end GlobalTheory.BigOn
end
