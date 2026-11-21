import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThetaFireRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLeviFlagOfMemParabolic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMemLevelOfDatumFlagCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLiftsSmoothVectors

section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.LevelCharacterConjugate

theorem levPOf_inv {D : D7} {G K : Type} [Group G] [Field K] {Pg : Finset (Pl D.host.E)} {r : ℕ}
    (eG : G ≃* G0 Pg r) (σ : K →+* ℂ) (P : Subgroup G) (ψ : P →* Kˣ) :
    levPOf eG σ P ψ⁻¹ = (levPOf eG σ P ψ).conj := by
  have hc : (Units.map (σ : K →* ℂ)).comp (ψ⁻¹.comp (eG.symm.toMonoidHom.subgroupComap P)) =
      ((Units.map (σ : K →* ℂ)).comp (ψ.comp (eG.symm.toMonoidHom.subgroupComap P)))⁻¹ :=
    MonoidHom.ext fun x => by simp only [MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv]
  exact congrArg (LevelP.mk (Subgroup.comap eG.symm.toMonoidHom P)) hc

theorem liftLevel_fixedEmbedding_eq_conj_rowLevel {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool)
    (h : A.v0 = InfinitePlace.mk D.what₂.embLL) : R.levL F b (sg0 D A) = (R.levR F b).conj := by
  rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ h]
  exact levPOf_inv _ _ _ _

end GlobalTheory.Proof.LevelCharacterConjugate
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRankR

theorem exists_lift_of_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) (κ' : GA D (Wc D i)), κ' ∈ levG (Wc D i) (R.βW i) (R.datWp i P) → ∃ g0 : P.H, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0.1 κ' ∧ levChi (Wc D i) (R.βW i) (R.datWp i P) κ' = ((P.chi g0 : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i P κ' hκ
  have hp : rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ') ∈ P.H := hκ.2.2
  refine ⟨⟨_, hp⟩, ⟨hκ.1, hκ.2.1, rfl⟩, ?_⟩
  have h2 : ext1 (R.datWp i P).P.H (R.datWp i P).P.chi
      (rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ')) = P.chi ⟨_, hp⟩ := extendOne_of_mem _ hp
  unfold levChi levFn
  rw [h2]
  have hs : (R.datWp i P).s = 0 := rfl
  have hQ : (R.datWp i P).Q = ∅ := rfl
  rw [hs, hQ]
  simp

end GlobalTheory.LevelRankR

end
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_mem_levelOfDatum_flagCharacter : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (g0 : P.H) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0.1 κ → κ ∈ levG (Vc D i) (R.βV i) (RecTie.datVP R i t P) ∧ levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) κ = ((P.chi g0 : ℂˣ) : ℂ)⁻¹ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ := by
  first | exact @GlobalTheory.lift_mem_levVP | exact GlobalTheory.lift_mem_levVP | (intros; apply GlobalTheory.lift_mem_levVP <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_intertwines_lifts_smoothVectors : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : (R.MW i (sg0 D A)).Vec) (x : GA D (Wc D i)), R.thF i t y' v x = R.thF i t y v (x * κ') := by
  first | exact @GlobalTheory.ThetaShiftSmooth.thF_shift_all | exact GlobalTheory.ThetaShiftSmooth.thF_shift_all | (intros; apply GlobalTheory.ThetaShiftSmooth.thF_shift_all <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaLevelP

set_option maxHeartbeats 1000000 in

theorem thF_mem_conj {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hIs : R.toLevCh.Is A.μ0)
    (hMod : R.IsModels) (hTh : R.IsThP) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (y : (R.HV i t).H)
    (hy : R.extV i t y ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t P))
      (levChi _ (R.βV i) (RecTie.datVP R i t P))) :
    R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P.conj))
      (levChi _ (R.βW i) (R.datWp i P.conj)) := by
  have hW := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 (hTh.thF_mem i t y)
  refine (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).2 ⟨hW.aut, hW.cusp, fun v k' hk' g => ?_, hW.equiv, hW.cont⟩
  obtain ⟨g0, hl', hc'⟩ := GlobalTheory.LevelRankR.exists_lift_of_mem_level R i P.conj k' hk'
  have hL := (GlobalTheory.StepLifts.lifts_exist R hIs i).1 t
  have hx := hL g0
  clear hL
  rcases hx with ⟨κ, hl⟩
  have h1 := GlobalTheory.T.lift_mem_levelOfDatum_flagCharacter R i t P
  let g1 : P.H := ⟨g0.1, g0.2⟩
  have h3 := h1 g1 κ hl
  clear h1
  have hf0 : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ ≠ 0 := Units.ne_zero _
  have hy' : ∀ k ∈ levS (Vc D i) (R.βV i) (RecTie.datVP R i t P), ∀ h,
      R.extV i t y (h * k) = levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) k • R.extV i t y h := hy
  have e1 := hy' κ h3.1
  have e2 := h3.2
  clear hy' hy h3
  have hnum : (((P.chi g1 : ℂˣ) : ℂ))⁻¹ = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ *
      levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) κ := by
    rw [e2]
    field_simp
  have hsh : ∀ h, R.extV i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) h =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ) := by
    intro h
    have e3 : R.extV i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) h = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ • R.extV i t y h :=
      congrFun ((R.extV i t).map_smul _ y) h
    refine e3.trans ?_
    refine Eq.trans ?_ (congrArg (fun w => (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • w) (e1 h).symm)
    refine (congrArg (fun a : ℂ => a • R.extV i t y h) hnum).trans ?_
    exact mul_smul _ _ _
  have key := GlobalTheory.T.thetaLift_intertwines_lifts_smoothVectors R hIs hMod hTh i t g0.1 κ k' hl hl' y _ hsh v g
  have hcc : levChi (Wc D i) (R.βW i) (R.datWp i P.conj) k' = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ := by
    rw [hc']
    change (((P.chi⁻¹) g1 : ℂˣ) : ℂ) = _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have e4 : R.thF i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) v g = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ * R.thF i t y v g := by
    have e5 := congrFun (congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) ((R.thF i t).map_smul (((P.chi g1 : ℂˣ) : ℂ))⁻¹ y)) g
    exact e5
  exact key.symm.trans (e4.trans (congrArg (· * R.thF i t y v g) hcc.symm))

set_option maxHeartbeats 1000000 in

theorem thF_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (b : Bool) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), R.extV i t y ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) (levChi _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) → R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hIs hMod hTh hv b i t y hy
  rw [GlobalTheory.Proof.LevelCharacterConjugate.liftLevel_fixedEmbedding_eq_conj_rowLevel R F b hv]
  exact thF_mem_conj R hIs hMod hTh i t (R.levR F b) y hy

end GlobalTheory.ThetaLevelP
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_mem_multiplicitySpace_baseLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (b : Bool) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), R.extV i t y ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) (levChi _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) → R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) := by
  first | exact @GlobalTheory.ThetaLevelP.thF_mem_level | exact GlobalTheory.ThetaLevelP.thF_mem_level | (intros; apply GlobalTheory.ThetaLevelP.thF_mem_level <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaFireLift

theorem lift_postOn {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (X : MMap M) :
    PiTensorProduct.lift (postOn M L X) = L ∘ₗ PiTensorProduct.lift X := by
  ext v
  simp [postOn]

theorem thetaFireL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → R.IsThP → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ IL : RecTie.LiftIds (RecTie.toLiftReal R F tupT hm hTop hinj), RecTie.ThetaFireL (RecTie.toLiftReal R F tupT hm hTop hinj) IL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hLev hGrp hMod hThP hv0 IL μ hμ i x
  have hfm : ((IL.jMt μ hμ i x).1 : GA D (Vc D i) → (R.cV i).W) ∈ LinearMap.range (R.extV i (tupT μ)) ⊓
      RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i (tupT μ) (R.levR F false)))
        (levChi _ (R.βV i) (RecTie.datVP R i (tupT μ) (R.levR F false))) := (IL.jMt μ hμ i x).2
  obtain ⟨y, hy⟩ : ∃ y, (LinearEquiv.ofInjective _ (hinj i (tupT μ))).symm
      ⟨((IL.jMt μ hμ i x).1 : GA D (Vc D i) → (R.cV i).W), hfm.1⟩ = y := ⟨_, rfl⟩
  have hyf : R.extV i (tupT μ) y = ((IL.jMt μ hμ i x).1 : GA D (Vc D i) → (R.cV i).W) := by
    rw [← hy]
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (hinj i (tupT μ))).apply_symm_apply _)
  have hM := GlobalTheory.T.thetaLift_mem_multiplicitySpace_baseLevel R F hLev hMod hThP hv0 false i (tupT μ) y (by rw [hyf]; exact hfm.2)
  refine ⟨PiTensorProduct.lift (R.thF i (tupT μ) y), ?_, ?_, ?_⟩
  · exact Submodule.mem_map_of_mem hM
  · rw [← hy]; rfl
  · have hG : R.eWf i (sg0 D A) ∘ₗ PiTensorProduct.lift (R.thF i (tupT μ) y) ∈
        (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).map
          (PiTensorProduct.lift : MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap := by
      rw [← lift_postOn]
      exact Submodule.mem_map_of_mem (GlobalTheory.GoodProjLevel.proj_mem_good R hLev hGrp.record hv0 i _ _ hM)
    exact hG

end GlobalTheory.ThetaFireLift
end
end
