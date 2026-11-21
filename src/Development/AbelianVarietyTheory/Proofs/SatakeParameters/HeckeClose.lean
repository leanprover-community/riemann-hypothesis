import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryRowOperatorIsLabelOperatorWithPartner
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperatorsStatement
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanImageMaxGenEigenspace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSpaceJointEigenspacesPairCommISup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UpwardThetaLiftInjectiveOnCarriedPart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeThetaLevel3Exists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRowsLiftsRationalAdjointClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypesSeparatedByInertPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodGenericCharacterOfSeriesTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay

section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory.EigTransfer

theorem linearMap_ext_of_iSup_eq_top {E F C : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (Ec : C → Submodule ℂ E) (htop : (⨆ c, Ec c) = ⊤) (f g : E →ₗ[ℂ] F)
    (h : ∀ c, ∀ w ∈ Ec c, f w = g w) : f = g := by
  have hle : (⊤ : Submodule ℂ E) ≤ LinearMap.eqLocus f g := by
    rw [← htop]
    exact iSup_le fun c w hw => LinearMap.mem_eqLocus.2 (h c w hw)
  ext e
  exact LinearMap.mem_eqLocus.1 (hle Submodule.mem_top)

end GlobalTheory.EigTransfer
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem parts_of_adjoint_lift : ∀ {X E I : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) (op : I → Module.End ℂ X) (h : I → Module.End ℂ E), ∀ {C : Type} (Ec : C → Submodule ℂ E) (lab : C → I → ℂ), (∀ i u, Θ (op i u) = h i (Θ u)) → (∀ i, Commute (op i) (LinearMap.adjoint (op i))) → (∀ i, Commute (h i) (LinearMap.adjoint (h i))) → Formalism.L2.Col.PairComm op → (⨆ c, Ec c) = ⊤ → (∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) → (∀ c, Ec c ≠ ⊥ → ∃ w ∈ Ec c, LinearMap.adjoint Θ w ≠ 0) → Formalism.L2.Col.PairComm h ∧ ∀ Q : (I → ℂ) → Prop, (∀ c, Ec c ≠ ⊥ → ((Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q ↔ Q (lab c))) ∧ (⨆ (c : C) (_ : Ec c ≠ ⊥ ∧ (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q), Ec c) = Formalism.L2.Col.eigSum h Q := by
  intro X E I _ _ _ _ _ _ Θ op h C Ec lab hint hn hn' hc htop hh hne
  have hcomm : Formalism.L2.Col.PairComm h := by
    intro i j
    refine GlobalTheory.EigTransfer.linearMap_ext_of_iSup_eq_top Ec htop (h i * h j) (h j * h i) fun c w hw => ?_
    simp only [Module.End.mul_apply, hh c w hw, map_smul, smul_smul, mul_comm]
  have hup : ∀ c, (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigAt op (lab c) := by
    rintro c _ ⟨w, hw, rfl⟩
    exact Formalism.L2.Col.mem_eigAt_of_forall_apply fun i =>
      GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators Θ op h hint hn hn' i (lab c i) w (hh c w hw i)
  have hiff : ∀ (Q : (I → ℂ) → Prop) c, Ec c ≠ ⊥ →
      ((Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q ↔ Q (lab c)) := by
    intro Q c hcne
    constructor
    · intro hle
      by_contra hq
      obtain ⟨w, hw, hw0⟩ := hne c hcne
      have hm : LinearMap.adjoint Θ w ∈ (Ec c).map (LinearMap.adjoint Θ) := ⟨w, hw, rfl⟩
      have hd := Formalism.L2.Col.disjoint_eigSum hc (C := fun x => ¬ Q x) (C' := Q) fun x hx => hx
      exact hw0 ((Submodule.disjoint_def.1 hd) _
        (Formalism.L2.Col.eigAt_le_eigSum (C := fun x => ¬ Q x) hq (hup c hm)) (hle hm))
    · intro hq
      exact (hup c).trans (Formalism.L2.Col.eigAt_le_eigSum hq)
  refine ⟨hcomm, fun Q => ⟨fun c hcne => hiff Q c hcne, ?_⟩⟩
  have hle : ∀ P : (I → ℂ) → Prop, (⨆ (c : C) (_ : P (lab c)), Ec c) ≤ Formalism.L2.Col.eigSum h P := fun P =>
    iSup₂_le fun c hq w hw => Formalism.L2.Col.eigAt_le_eigSum hq
      (Formalism.L2.Col.mem_eigAt_of_forall_apply fun i => hh c w hw i)
  have hsup : (⨆ (c : C) (_ : Q (lab c)), Ec c) ⊔ (⨆ (c : C) (_ : ¬ Q (lab c)), Ec c) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun c => ?_
    by_cases hq : Q (lab c)
    · exact le_sup_of_le_left (le_iSup₂_of_le (f := fun c (_ : Q (lab c)) => Ec c) c hq le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun c (_ : ¬ Q (lab c)) => Ec c) c hq le_rfl)
  have hd : Disjoint (⨆ (c : C) (_ : ¬ Q (lab c)), Ec c) (Formalism.L2.Col.eigSum h Q) :=
    (Formalism.L2.Col.disjoint_eigSum hcomm (C := fun x => ¬ Q x) (C' := Q) fun x hx => hx).mono_left
      (hle fun x => ¬ Q x)
  have hQ : (⨆ (c : C) (_ : Q (lab c)), Ec c) = Formalism.L2.Col.eigSum h Q := by
    have := sup_inf_assoc_of_le (⨆ (c : C) (_ : ¬ Q (lab c)), Ec c) (hle Q)
    rw [hsup, top_inf_eq, hd.eq_bot, sup_bot_eq] at this
    exact this.symm
  rw [← hQ]
  apply le_antisymm
  · refine iSup₂_le fun c hcq => ?_
    exact le_iSup₂_of_le (f := fun c (_ : Q (lab c)) => Ec c) c ((hiff Q c hcq.1).1 hcq.2) le_rfl
  · refine iSup₂_le fun c hq => ?_
    by_cases hb : Ec c = ⊥
    · rw [hb]; exact bot_le
    · exact le_iSup₂_of_le (f := fun c (_ : Ec c ≠ ⊥ ∧ (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q) => Ec c)
        c ⟨hb, (hiff Q c hb).2 hq⟩ le_rfl

end GlobalTheory.Hk3
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parts_adjoint_intertwiner_eq_joint_eigenspaces : ∀ {X E I : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) (op : I → Module.End ℂ X) (h : I → Module.End ℂ E), ∀ {C : Type} (Ec : C → Submodule ℂ E) (lab : C → I → ℂ), (∀ i u, Θ (op i u) = h i (Θ u)) → (∀ i, Commute (op i) (LinearMap.adjoint (op i))) → (∀ i, Commute (h i) (LinearMap.adjoint (h i))) → Formalism.L2.Col.PairComm op → (⨆ c, Ec c) = ⊤ → (∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) → (∀ c, Ec c ≠ ⊥ → ∃ w ∈ Ec c, LinearMap.adjoint Θ w ≠ 0) → Formalism.L2.Col.PairComm h ∧ ∀ Q : (I → ℂ) → Prop, (∀ c, Ec c ≠ ⊥ → ((Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q ↔ Q (lab c))) ∧ (⨆ (c : C) (_ : Ec c ≠ ⊥ ∧ (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q), Ec c) = Formalism.L2.Col.eigSum h Q := by
  atlas_forward_decl GlobalTheory.Hk3.parts_of_adjoint_lift
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Hk3.HeckeRowsClose

section TwLemmas
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tw_sub_injective (s : Bool) {V W : Submodule ℂ E} (h : Tw.sub s V = Tw.sub s W) : V = W := by
  ext x
  exact SetLike.ext_iff.mp h (Tw.mk s x)

theorem tw_span_image (s : Bool) (S : Set E) :
    Submodule.span ℂ ((Tw.mk s : E → Tw s E) '' S) = Tw.sub s (Submodule.span ℂ S) := by
  have h1 : Tw.sub s (Submodule.span ℂ S) = (Submodule.span ℂ S).map (Tw.mkL s E) := by
    ext x
    constructor
    · intro hx; exact ⟨Tw.out x, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  rw [h1, Submodule.map_span]; rfl

theorem tw_commute (s : Bool) {a b : Module.End ℂ E} (h : Commute a b) : Commute (Tw.map s a) (Tw.map s b) := by
  show Tw.map s a * Tw.map s b = Tw.map s b * Tw.map s a
  ext x
  exact congrArg (Tw.mk s) (LinearMap.congr_fun h.eq (Tw.out x))

end TwLemmas

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem opC_eq (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hK : (R.toCx3 F).KFormR) (t : T) (i : (A3.rowI t).OpIx)
    (g : Module.End ℂ (R.HX t).H) (hg : ∀ x, R.jX t ((A3.rowI t).opAll i x) = g (R.jX t x)) :
    (R.toCx3 F).opC t (Sum.inl i) = Tw.map (twAt D.what₂.embLL A3.A.v0) g := by
  apply (Module.Basis.mk (hK t).1 (hK t).2.ge).ext
  intro k
  rw [Module.Basis.mk_apply, ← CxData.jR_opR _ hK]
  exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) (hg _)

set_option maxHeartbeats 1000000 in
theorem span_parts_eq (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hK : (R.toCx3 F).KFormR)
    (op : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H)
    (hOpC : ∀ i, (R.toCx3 F).opC A3.A.μ0 (Sum.inl i) = Tw.map (twAt D.what₂.embLL A3.A.v0) (op i))
    (p : A3.fam3.base3.Ix) :
    Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) =
      Formalism.L2.Col.eigSum op (fun x => cxSys A3.fam3.base3.v0.embedding ((A3.rowI A3.A.μ0).HasRes3 p.1)
        (fun i => cj (twAt D.what₂.embLL A3.A.v0) (x i))) := by
  have hFD : FiniteDimensional D.what₂.LL (A3.fam3.amb3.FR A3.A.μ0) :=
    Module.Finite.of_basis (A3.A.fam.R A3.A.μ0).S.basis
  have hFin : Finite (Module.Basis.ofVectorSpaceIndex D.what₂.LL (A3.fam3.amb3.FR A3.A.μ0)) :=
    Module.Finite.finite_basis (CxData.bR (A := A3.fam3.amb3) A3.A.μ0)
  have hjR : ∀ i x, (R.toCx3 F).jR A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i x) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (op i) ((R.toCx3 F).jR A3.A.μ0 x) :=
    fun i x => (CxData.jR_opR _ hK _ (Sum.inl i) x).trans (LinearMap.congr_fun (hOpC i) _)
  have hspan := (GlobalTheory.span_image_eigAt_of_basis A3.fam3.base3.v0.embedding ((R.toCx3 F).jR A3.A.μ0)
    (CxData.bR (A := A3.fam3.amb3) A3.A.μ0) (A3.rowI A3.A.μ0).opAll
    (fun i => Tw.map (E := (R.HX A3.A.μ0).H) (F := (R.HX A3.A.μ0).H) (twAt D.what₂.embLL A3.A.v0) (op i))
    (hK _).1 (hK _).2 hjR).2.1 ((A3.rowI A3.A.μ0).HasRes3 p.1)
  have hTw := (GlobalTheory.TwEig.pairComm_eigSum_sub_iSup (twAt D.what₂.embLL A3.A.v0) op).2.1
    (cxSys A3.fam3.base3.v0.embedding ((A3.rowI A3.A.μ0).HasRes3 p.1))
  apply tw_sub_injective (twAt D.what₂.embLL A3.A.v0)
  rw [← tw_span_image, Set.image_image]
  exact hspan.trans hTw

set_option maxHeartbeats 1000000 in
theorem adj_ne_zero (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hB : R.PThmB)
    (hPos : 0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0)
    (hEEc : ∀ c, R.EEc c = EEc R.toRealDat R.SF c) (p : A3.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ)
    (hc : EEc R.toRealDat R.SF c ≠ ⊥) :
    ∃ w ∈ EEc R.toRealDat R.SF c, LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hc
  have hc' : R.EEc c ≠ ⊥ := fun h0 => hc ((hEEc c).symm.trans h0)
  have hcar : R.Carries p c := by
    refine ⟨hc', ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [hall v ((SetLike.ext_iff.mp (hEEc c) v).mp hv)]
    exact Submodule.zero_mem _
  exact GlobalTheory.thetaUp_injective_on_carried R F hB hPos p c hcar w ((SetLike.ext_iff.mp (hEEc c) w).mpr hw) hw0 (hall w hw)

set_option maxHeartbeats 1000000 in
theorem eep_eq (R : RealDat3 D A3 Ks) (hEEc : ∀ c, R.EEc c = EEc R.toRealDat R.SF c) (p : A3.fam3.base3.Ix)
    (op : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H)
    (h' : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ R.HE.H) (Q : ((A3.rowI A3.A.μ0).OpIx → ℂ) → Prop)
    (hspanE : Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) =
      Formalism.L2.Col.eigSum op Q)
    (hLA : (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : EEc R.toRealDat R.SF c ≠ ⊥ ∧
      (EEc R.toRealDat R.SF c).map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤ Formalism.L2.Col.eigSum op Q),
        EEc R.toRealDat R.SF c) = Formalism.L2.Col.eigSum h' Q) :
    R.EEp3 p = Formalism.L2.Col.eigSum h' Q := by
  rw [← hLA]
  unfold RealDat3.EEp3 RealDat3.Carries
  simp only [hEEc, hspanE]

set_option maxHeartbeats 1000000 in
theorem exists_core (hH : HoweUnram) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hLI : GlobalTheory.Chain.LiftInteg D)
    (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hS : SchurAll R.toRealDat) (hJ : InertJunk A3) (hB : R.PThmB)
    (hPos : 0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) : ∃ hE, HeckeIntertwiningDefinite A3 (R.toCx3 F) hE := by
  obtain ⟨hCore', hSF, -, -, hEEc, -, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC
  have hCore := hCore' hEx
  obtain ⟨h, hOpsE, hNE, hTop, hEig, -⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 hCore hS R.SF hSF
  choose hX hXops hXnorm using (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models).1
  choose pl cX c0 hDict using GlobalTheory.T.every_rowOperator_is_labelOperator_with_partner hH R F hLI hC hEx hS hJ
  have hK : (R.toCx3 F).KFormR := RealDat3.kFormR_of hCore.models
  have hOpC : ∀ t i, (R.toCx3 F).opC t (Sum.inl i) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (hX t (pl t i) (cX t i)) :=
    fun t i => opC_eq R F hK t i _ ((hDict t).op _ (hXops t) i)
  have hSys := fun t i => GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 hCore hS R.SF hSF t (pl t i) ((hDict t).good i) (cX t i)
    (c0 t i) ((hDict t).mat i) (hX t) (hXops t)
  refine ⟨fun t i => Tw.map (E := R.HE.H) (F := R.HE.H) (twAt D.what₂.embLL A3.A.v0) (h (pl t i) (c0 t i)), ⟨?_, ?_, ?_⟩⟩
  · intro t i u
    rw [hOpC]
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) ((hSys t i).1 h hOpsE (Tw.out (s := twAt D.what₂.embLL A3.A.v0) u))
  · intro i j
    exact tw_commute _ (hNE.1 _ _ ((hDict _).good i) ((hDict _).good j) _ _)
  · intro p
    have hNX := hXnorm A3.A.μ0
    have hspanE := span_parts_eq R F hK (fun i => hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i)) (hOpC A3.A.μ0) p
    have hNop : ∀ i, Commute (hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i))
        (LinearMap.adjoint (hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i))) := fun i => by
      have hg := (hDict A3.A.μ0).good i
      have hc := hNX.1 _ _ hg hg (cX A3.A.μ0 i) (dualC (Finsupp.mapRange star (star_zero ℂ) (cX A3.A.μ0 i)))
      rw [← hNX.2 _ hg] at hc
      exact hc
    have hNh : ∀ i, Commute (h (pl A3.A.μ0 i) (c0 A3.A.μ0 i)) (LinearMap.adjoint (h (pl A3.A.μ0 i) (c0 A3.A.μ0 i))) :=
      fun i => by
        have hg := (hDict A3.A.μ0).good i
        have hc := hNE.1 _ _ hg hg (c0 A3.A.μ0 i) (dualC (Finsupp.mapRange star (star_zero ℂ) (c0 A3.A.μ0 i)))
        rw [← hNE.2 _ hg] at hc
        exact hc
    have hPC : Formalism.L2.Col.PairComm (fun i => hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i)) :=
      fun i j => hNX.1 _ _ ((hDict _).good i) ((hDict _).good j) _ _
    obtain ⟨-, hLA⟩ := GlobalTheory.T.parts_adjoint_intertwiner_eq_joint_eigenspaces (R.Th A3.A.μ0) (fun i => hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i))
      (fun i => h (pl A3.A.μ0 i) (c0 A3.A.μ0 i)) (fun c => EEc R.toRealDat R.SF c)
      (fun c i => evC (Yc D 0) (pl A3.A.μ0 i) (fun d => c (pl A3.A.μ0 i) (dualLab d)) (c0 A3.A.μ0 i))
      (fun i u => (hSys A3.A.μ0 i).1 h hOpsE u) hNop hNh hPC hTop
      (fun c w hw i => hEig c _ ((hDict _).good i) _ w hw) (adj_ne_zero R F hB hPos hEEc p)
    have hEEp := eep_eq R hEEc p _ (fun i => h (pl A3.A.μ0 i) (c0 A3.A.μ0 i)) _ hspanE (hLA _).2
    exact (congrArg (Tw.sub (twAt D.what₂.embLL A3.A.v0)) hEEp).trans
      ((GlobalTheory.TwEig.pairComm_eigSum_sub_iSup (twAt D.what₂.embLL A3.A.v0)
        (fun i => h (pl A3.A.μ0 i) (c0 A3.A.μ0 i))).2.1 _).symm

theorem exists_heckeIntertwiningDefinite_of_liftInteg : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type}
    [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F →
    R.toRealDat.ExAt → InertJunk A3 → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) →
    ∃ hE, HeckeIntertwiningDefinite A3 (R.toCx3 F) hE :=
  fun hH _ hCD _ _ _ _ _ _ _ _ _ _ _ _ R F hLI hC hEx hJ hB hPos =>
    exists_core hH R F hLI hC hEx (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCD R.toRealDat) hJ hB hPos

end GlobalTheory.Hk3.HeckeRowsClose
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hecke_operators_rows_intertwine_theta_lifts : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → InertJunk A3 → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → ∃ hE, HeckeIntertwiningDefinite A3 (R.toCx3 F) hE := by
  atlas_forward_decl GlobalTheory.Hk3.HeckeRowsClose.exists_heckeIntertwiningDefinite_of_liftInteg
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.okH_inertRationalAdjoint_of_weakCharacterisation_inertJunk : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → InertJunk A3 → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) := by
  first | exact @GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed | exact GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed | (intros; apply GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.HeckeClose

theorem heckeClose : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ s, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → InertJunk A3 → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → ((∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).PartsW false → ((∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint)) ∧ R.PHecke F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr := by
  intro hH hHC hCD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hJ hSer hPass hU hGU hGE hLW hA hB hPos hParts
  have hLI : GlobalTheory.Chain.LiftInteg D := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hCD D
  have hS : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCD R.toRealDat
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨tr, htr⟩ := GlobalTheory.T.exists_separating_inert_eigenvalue_passage hH R F hLI hC hEx hS hJ hX hB hPos
  have hTS : A3.fam3.TypesSep3 :=
    GlobalTheory.T.finite_types_separated_by_inert_places hCD hH R F hLI hOk hC hEx ⟨fun t k => hJ.R t k.1 k.2, fun j t k => hJ.L j t k.1 k.2⟩ hPass hPos hB
  have hG : GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ := (GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes R F hC s hOk hSer).2
  have hR := GlobalTheory.T.exists_hecke_operators_rows_intertwine_theta_lifts hH hHC hCD R F hLI hC hEx hJ hB hPos
  have hL := GlobalTheory.T.heckeTheta_level3_exists hH hHC hCD R F hLI hC hEx hJ s hOk hG hU hGU hGE hLW hA hPos hB hParts hTS hPass
  exact ⟨GlobalTheory.T.okH_inertRationalAdjoint_of_weakCharacterisation_inertJunk R F hC hJ, ⟨hR, hL⟩, hTS, tr, htr⟩

end GlobalTheory.Hk3.HeckeClose

end
end
