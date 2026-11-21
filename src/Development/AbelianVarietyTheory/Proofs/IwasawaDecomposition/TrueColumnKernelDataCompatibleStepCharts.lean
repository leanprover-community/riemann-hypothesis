import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelChoicesStandardTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullHermitianColumnsTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalFramesNearAdelicAtBadPrimesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElementSameCharacterNearBadStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNearStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceMoveRationalFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPointMatrixAndInverseIntegralAtEveryPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalGroupElementEqLevelComponentBadPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepNearLiftsComponentMemLocalChartGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismsNearSameAdelicCongruent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismCongruentNearFrameReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMiddleStepLevelInverseLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepGroupCharacterInverseTypeAtLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQOfCongE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesPreimageUnderLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesShapeAtBadPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTopStepLevelCongruentBlockSumOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepCharacterInverseTypeAtLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartReadsAtClassGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeFunctionalsEqMovedLevelFunctionals
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeLatticeEqCompanionOfAdelicRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBadPrimeOverBadPlaceOfChain
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEq

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelChoices_standard_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKerTie l Z t → ex.errX.piT = X.piT → t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  first | exact @GlobalTheory.Mem.Col2.TC.k_pins_tie | exact GlobalTheory.Mem.Col2.TC.k_pins_tie | (intros; apply GlobalTheory.Mem.Col2.TC.k_pins_tie <;> assumption)
end

section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_fields_definite_laws : ∀ B : Base, B.fields.AbelianUnramifiedExtensionConditions ∧ B.fields.f = B.R.f := by
  first | exact @GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws | exact GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws | (intros; apply GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

set_option maxHeartbeats 4000000 in

theorem exists_stepElt_of_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ChiFin I l Z (K (chOf c)).lev → ∀ κ : (K (chOf c)).lev.U, ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ (((K (chOf c)).lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ' : B.LLˣ) : B.LL) ∧ ∀ (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), LiftsInv I κ' P g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ.1 g := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c fb hfb hchi κ
  obtain ⟨x, hxchi, ⟨q, hq⟩, hxκ⟩ := GlobalTheory.T.exists_levelElement_same_character_near_bad I hOk hPins l Z u a i hi bad Ch chOf K k hR c hchi κ
  have hl := hR.lev c x.1 q hq
  have hx : x.1 ∈ (fun β => (K β).lev.U) (chOf c) := x.2
  obtain ⟨κ', h3⟩ := hl.mp hx
  have hg := h3.1
  have hact := h3.2.1
  have hcos := h3.2.2
  refine ⟨κ', ⟨hg, hcos⟩, ?_, ?_⟩
  · rw [← hxchi]
    exact hR.chr c x κ' hg (hact ▸ hq)
  · intro P g hL
    obtain ⟨hm1, hm2, hn⟩ := GlobalTheory.T.levelElement_at_bad_primes_integral_and_near I hOk l Z u a i hi bad Ch chOf K k hR c x.1 κ' hg (hact ▸ hq) P
    obtain ⟨p, hp, hpN⟩ := hR.k_std (chOf c)
    exact GlobalTheory.T.adelicMatrixCongruence_move_rational_frame _ _ κ.1 x.1 (k (chOf c)) (fb P) _ (fun r s => (GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime _ _ p hp hpN _ r s).1)
      (fun r s => (GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime _ _ p hp hpN _ r s).2) hm1 hm2 (hxκ P) (hn g hL) (hfb P).1 (hfb P).2

end GlobalTheory.Mem.Col2.AdT

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stepGroupElement_of_chartLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ChiFin I l Z (K (chOf c)).lev → ∀ κ : (K (chOf c)).lev.U, ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ (((K (chOf c)).lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ' : B.LLˣ) : B.LL) ∧ ∀ (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), LiftsInv I κ' P g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ.1 g := by
  atlas_forward_decl GlobalTheory.Mem.Col2.AdT.exists_stepElt_of_level
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_group_element_eq_level_component_bad_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ S.Uloc v → ∃ x ∈ S.U, ∀ (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep : SBof I a → ℕ) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P x g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LocSplice.main | exact GlobalTheory.Mem.Col2.AdT.LocSplice.main | (intros; apply GlobalTheory.Mem.Col2.AdT.LocSplice.main <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_automorphisms_near_same_adelic_congruent : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → 1 ≤ dep' P → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' → CongE P.1 (dep' P) g' g := by
  first | exact @GlobalTheory.Mem.Col2.AdT.AdTieNear.main | exact GlobalTheory.Mem.Col2.AdT.AdTieNear.main | (intros; apply GlobalTheory.Mem.Col2.AdT.AdTieNear.main <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_automorphism_congruent_near_frame_reading : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → CongE P.1 (dep' P) g' g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' := by
  first | exact @GlobalTheory.Mem.Col2.AdT.NearCong.main | exact GlobalTheory.Mem.Col2.AdT.NearCong.main | (intros; apply GlobalTheory.Mem.Col2.AdT.NearCong.main <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_group_character_inverse_type_at_lifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, MidAt I hi b P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 ((I.cst a).D P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.chr_mul_prod_midAt | exact GlobalTheory.Mem.Col2.AdT.chr_mul_prod_midAt | (intros; apply GlobalTheory.Mem.Col2.AdT.chr_mul_prod_midAt <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

set_option maxHeartbeats 1600000 in
private theorem mem_GLint_and_exists_liftsInv_of_congE : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K),
    MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧
      ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' →
        ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := by
  classical
  intro B X I hI u a i hi b P g z hmid
  have hO := hI.idx_ok a
  have hpr := (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P
    ((I.idx a).h i (Idx.get b hi) P) g).mp ⟨z, hmid⟩
  have hgi : g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 := hO.int i (Idx.get b hi) P hpr
  refine ⟨hgi, fun g' hg' hc => ?_⟩
  have hb : b.1 = some (Idx.get b hi) := (Option.some_get _).symm
  have hstd : ∀ (k : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) {x : Sp B.fields.E (B.R.N i)},
      x ∈ stdAt B.fields.E (B.R.N i) P.1 → k.1 x ∈ stdAt B.fields.E (B.R.N i) P.1 :=
    fun k _ hx => GlobalTheory.TopStep.glint_mem k hx
  refine ⟨⟨1, ⟨fun w => if h : w.1 = P.1 then
      (GlobalTheory.TopStep.redGL (B.R.N i) w.1 ⟨g, by rw [h]; exact hgi⟩)⁻¹ else 1, ?_⟩,
    ⟨fun w => if h : w.1 = P.1 then
      (⟨g', by rw [h]; exact hg'⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) w.1))⁻¹ else 1, ?_⟩⟩, ?_, ?_, ?_⟩
  · rw [LevFam.grp, Subgroup.mem_pi]
    intro w _
    simp only [levGAt, hb, Option.elim]
    by_cases hw : w.1 = P.1
    · rw [dif_pos hw]
      apply inv_mem
      rw [hO.grpG]
      obtain ⟨w, hwG⟩ := w
      simp only at hw
      subst hw
      exact ⟨g, hpr, fun x hx => GlobalTheory.TopStep.redV_redGL ⟨g, hgi⟩ hx⟩
    · rw [dif_neg hw]
      exact one_mem _
  · rw [LevQFam.grp, Subgroup.mem_pi]
    intro w _
    simp only [levQAt, hb, Option.elim]
    by_cases hw : w.1 = P.1
    · rw [dif_pos hw]
      apply inv_mem
      obtain ⟨w, hwQ⟩ := w
      simp only at hw
      subst hw
      have hgQ : (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) ∈
          ((I.idx a).levQ i (Idx.get b hi) ⟨P.1, hwQ⟩).H := by
        rw [hO.grpQ, Subgroup.mem_subgroupOf]
        exact hpr
      set k := (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1))⁻¹ with hk
      have hkg : ∀ v, k.1 (g v) = v := by
        intro v
        have h1 : k * (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) = 1 := inv_mul_cancel _
        exact congrArg (fun m : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1) => m.1 v) h1
      have hdeep := levQ_deep I hI a i hi (Idx.get b hi) P hwQ (k * ⟨g', hg'⟩)
      obtain ⟨hd, -⟩ := hdeep (by
        intro x hx
        have hneg := Submodule.neg_mem _ (hstd k (hc x hx))
        rw [map_smul, map_sub, hkg, ← smul_neg, neg_sub] at hneg
        exact hneg)
      have e2 : (⟨g', hg'⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) = ⟨g, hgi⟩ * (k * ⟨g', hg'⟩) := by
        rw [hk, mul_inv_cancel_left]
      rw [e2]
      exact mul_mem hgQ hd
    · rw [dif_neg hw]
      exact one_mem _
  · exact map_one (ufGL B.fields.E (B.R.N i))
  · refine ⟨hg', ?_, ?_⟩
    · intro h x hx
      dsimp only
      rw [dif_pos rfl, inv_inv, ← GlobalTheory.TopStep.redV_redGL ⟨g, hgi⟩ hx]
      have hD : (I.cst a).D P = 1 := hO.depthG P h
      have hq := hc x hx
      rw [hD, pow_one] at hq
      funext l
      have h1 : IntAt P.1 (g x l) := GlobalTheory.TopStep.mem_stdAt.mp (hstd ⟨g, hgi⟩ hx) l
      have h2 : IntAt P.1 (g' x l) := GlobalTheory.TopStep.mem_stdAt.mp (hstd ⟨g', hg'⟩ hx) l
      have h3 : IntAt P.1 (((qOf P.1 : ℕ) : B.fields.E)⁻¹ * (g x l - g' x l)) := GlobalTheory.TopStep.mem_stdAt.mp hq l
      have h0 := GlobalTheory.TopStep.redP_eq_zero_of_div (P := P.1) (a := g x l - g' x l) (by rw [div_eq_inv_mul]; exact h3)
      rw [GlobalTheory.TopStep.reduction_sub h1 h2, sub_eq_zero] at h0
      exact h0.symm
    · intro h
      dsimp only
      rw [dif_pos rfl, inv_inv]
  · intro P' hP'
    have hne : P'.1 ≠ P.1 := fun e => hP' (Subtype.ext e)
    refine ⟨one_mem _, ?_, ?_⟩
    · intro h x hx
      dsimp only
      rw [dif_neg hne, inv_one]
      simp
    · intro h
      dsimp only
      rw [dif_neg hne, inv_one]
      all_goals rfl

open Classical in

theorem midAt_lifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K),
    MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧
      ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' →
        ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := mem_GLint_and_exists_liftsInv_of_congE

end GlobalTheory.Mem.Col2.AdT

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruent_automorphisms_lift_step_group_elements : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K), MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧ ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' → ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := by
  atlas_forward_decl GlobalTheory.Mem.Col2.AdT.midAt_lifts
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCosetInFrames_preimage_under_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (p : (I.stp u a i).D b) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), (I.stp u a i).gam b κ = 1 → LiftsInv I κ P g → ∀ z, z ∈ cosetIn ((I.stp u a i).act b κ p) P ↔ g z ∈ cosetIn p P := by
  first | exact @GlobalTheory.Mem.Col2.AdT.cosetIn_act_of_liftsInv | exact GlobalTheory.Mem.Col2.AdT.cosetIn_act_of_liftsInv | (intros; apply GlobalTheory.Mem.Col2.AdT.cosetIn_act_of_liftsInv <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_reads_at_class_GL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ∀ P : SBof I a, GlobalTheory.TwU.NearAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (((K (chOf c)).y ⟨c, rfl⟩).1 * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P)) (GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P)) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.FrameMove.frame_near | exact GlobalTheory.Mem.Col2.AdT.FrameMove.frame_near | (intros; apply GlobalTheory.Mem.Col2.AdT.FrameMove.frame_near <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representativeLattice_eq_companion_of_adelicRep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ c : (I.stp u a i).Cl, ((I.stp u a i).rep c).1.1.deco.1.N = GlobalTheory.TwU.latCo (I.rec7 l Z).sp (gramN (I.rec7 l Z) i hi) 1 (B.fields.conjO (X.piT u)) ((K (chOf c)).y ⟨c, rfl⟩).1 (K (chOf c)).lev.Lb := by
  first | exact @GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo | exact GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo | (intros; apply GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_badPrime_over_bad_place_of_chain : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P ∈ SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.exists_SBof_over | exact GlobalTheory.Mem.Col2.AdT.exists_SBof_over | (intros; apply GlobalTheory.Mem.Col2.AdT.exists_SBof_over <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

open Formalism.HermitianLatticesTheory GlobalTheory.ThetaMove in

theorem inverseHalfDifferent_local_trivial_at_prime_norm {R : Ranks} (H : Host R) (P : HeightOneSpectrum (𝓞 H.E)) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∉ P.asIdeal ^ 2) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (H.AA0 : Submodule (𝓞 H.E) H.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 H.E) H.E) := by
  have := P.isPrime
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hnd := GlobalTheory.PeriodIdealUnit.not_dvd_different (K := H.K) hp P.asIdeal hmem h2
  have hnot : ¬ H.𝔟 ≤ P.asIdeal := fun hle => hnd (by
    rw [H.𝔟_spec.1]
    exact (Ideal.dvd_iff_le.2 hle).mul_right _)
  obtain ⟨z, hz, hzP⟩ := SetLike.not_le_iff_exists.1 hnot
  have hB : ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
      have h3 := H.𝔟_spec.2
      simp [h] at h3
  refine GlobalTheory.PeriodIdealUnit.locP_eq_one P _ ?_ ?_
  · intro t ht
    have ht' : t ∈ H.AA0 := ht
    unfold Host.AA0 at ht'
    obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff hB).1 ht' _ (FractionalIdeal.mem_coeIdeal_of_mem _ hz))
    refine (mem_locP P 1 t).2 ⟨z, hzP, Submodule.mem_one.2 ⟨w, ?_⟩⟩
    rw [Algebra.smul_def, hw, mul_comm]
  · refine ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    rw [one_smul]
    show (1 : H.E) ∈ H.AA0
    unfold Host.AA0
    refine (FractionalIdeal.mem_inv_iff hB).2 fun y hy => ?_
    rw [one_mul]
    exact FractionalIdeal.coeIdeal_le_one hy

theorem aaUnit_sall : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ), (I.J.amb B χ).AAUnit (Sall (Pr := B.primes X) I.sel (I.tup a) u) := by
  intro B X I hOk u a χ P hP
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr hOk.sel_ok
    (hOk.T_mem u) hOk.g_mem P hP
  show Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Th.perAA B.host ⊤) = _
  rw [Th.perAA_top]
  exact inverseHalfDifferent_local_trivial_at_prime_norm B.host P bad.2.1 bad.2.2.1

end GlobalTheory.Mem.Col2.AdT
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLatticeIdeal_trivial_at_chain_bad_primes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ), (I.J.amb B χ).AAUnit (Sall (Pr := B.primes X) I.sel (I.tup a) u) := by
  atlas_forward_decl GlobalTheory.Mem.Col2.AdT.aaUnit_sall
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

open Classical in

theorem addChar_isIntegral {A : Type} [AddCommGroup A] [Finite A] {K : Type} [Field K] (ψ : AddChar A K) (y : A) :
    IsIntegral ℤ (ψ y) := by
  refine IsIntegral.of_pow (Nat.card_pos (α := A)) ?_
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  exact isIntegral_one

theorem qOf_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : 0 < qOf w := by
  refine Nat.pos_of_ne_zero ?_
  unfold qOf
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact w.ne_bot

theorem ciPsi_isIntegral {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
    (P : SB) (x : X.E) : IsIntegral ℤ (ciPsi Ch P x) := by
  classical
  unfold ciPsi
  split
  · have := ciFinite (X := X) (qOf_pos P.1).ne'
    exact addChar_isIntegral _ _
  · exact isIntegral_one

theorem twZeta_pow_eq_one {X : Fields} (σ₀ : X.K →+* ℂ) {N : ℕ} (hN : 0 < N)
    (hex : ∃ z : X.K, σ₀ z = Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))) : twZeta σ₀ N ^ N = 1 := by
  have hs : σ₀ (twZeta σ₀ N) = Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) := Classical.epsilon_spec hex
  apply σ₀.injective
  rw [map_pow, hs, map_one, ← Complex.exp_nat_mul]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show (N : ℂ) * (2 * Real.pi * Complex.I / (N : ℂ)) = 2 * Real.pi * Complex.I by field_simp]
  exact Complex.exp_two_pi_mul_I

theorem twPsiQ_isIntegral {X : Fields} (σ₀ : X.K →+* ℂ) (xi0 : X.E) (P : HeightOneSpectrum (𝓞 X.E)) (D : ℕ)
    (hz : twZeta σ₀ (qOf P ^ D) ^ (qOf P ^ D) = 1) (a : X.E) : IsIntegral ℤ (twPsiQ σ₀ xi0 P D a) := by
  classical
  unfold twPsiQ
  split
  · refine IsIntegral.of_pow (pow_pos (qOf_pos P) D) ?_
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hz, _root_.one_zpow]
    exact isIntegral_one
  · exact isIntegral_one

theorem psi_isIntegral : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (a : I.ι) (P : SBof I a) (x : B.fields.E),
    IsIntegral ℤ ((I.cst a).psi P x) := by
  intro B X I h ht a P x
  rw [ht.cst_eq a]
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · rw [twCst_psi_g hP]
    exact ciPsi_isIntegral _ _ _
  · rw [twCst_psi_Q hP]
    exact twPsiQ_isIntegral _ _ _ _
      (twZeta_pow_eq_one _ (pow_pos (qOf_pos P.1) _) (TC.root_of_ok h ht.deep a P hP)) x

end GlobalTheory.Mem.Col2.AdT
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConstantWeilCharacter_values_isIntegral : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (a : I.ι) (P : SBof I a) (x : B.fields.E), IsIntegral ℤ ((I.cst a).psi P x) := by
  atlas_forward_decl GlobalTheory.Mem.Col2.AdT.psi_isIntegral
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdeleFieldIdentification_eq_baseChangeRingEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E), GlobalTheory.TwU.IsAdIso ι → ∀ x, ι x = afIso F E x := by
  first | exact @GlobalTheory.isAdIso_eq_afIso | exact GlobalTheory.isAdIso_eq_afIso | (intros; apply GlobalTheory.isAdIso_eq_afIso <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT

section Lev
variable {B : Base} {X : PreX B.toPre} {I : TC B X} (hOk : I.Ok) (hP : TC.Pins B X) {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {i : ℕ} {hi : i ≤ B.R.m}
  {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch} {K : Charts I l Z u a i hi bad chOf} {k : Ch → GA B (B.R.N i)}
  (hR : ReadsAt I l Z K k) (c : (I.stp u a i).Cl) {fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E} (hfb : FrNear I l Z a (k (chOf c)) fb)
  (hfin : ChiFin I l Z (K (chOf c)).lev)
  {dep : SBof I a → ℕ} {Rel : SBof I a → (Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) → B.fields.K → Prop}

include hOk hP hR hfb hfin in

theorem locLe_of (hd : ∀ P, dep P ≤ (I.cst a).D P)
    (h : ∀ κ : (I.stp u a i).G c.1, Keeps I κ ((I.stp u a i).rep c) → ∀ P, ∃ g g' z, Rel P g z ∧ LiftsInv I κ P g' ∧ CongE P.1 (dep P) g g') :
    GlobalTheory.TwU.LocLe (sm I l Z) (K (chOf c)).lev fb dep Rel := by
  intro P v hv κ hκ hU
  obtain ⟨x, hx, hxκ⟩ := GlobalTheory.T.local_group_element_eq_level_component_bad_prime I hOk l Z a (B.T u) i hi bad (K (chOf c)).lev P v hv κ hκ hU
  obtain ⟨κ', hk, -, hin⟩ := GlobalTheory.T.exists_stepGroupElement_of_chartLevel I hOk hP l Z u a i hi bad Ch chOf K k hR c fb hfb hfin ⟨x, hx⟩
  obtain ⟨g, g', z, hg, hl, hc⟩ := h κ' hk P
  exact ⟨g, z, hg, hxκ fb dep g (GlobalTheory.T.rational_automorphism_congruent_near_frame_reading I hOk l Z a i fb _ dep P x g' g hl.1 (hd P) (hin P g' hl) hc)⟩

include hOk hP hR hfb hfin in

theorem chiIs_of (hd : ∀ P, 1 ≤ dep P ∧ dep P ≤ (I.cst a).D P)
    (hex : ∀ (κ : (I.stp u a i).G c.1) P, ∃ g', LiftsInv I κ P g')
    (h : ∀ (κ : (I.stp u a i).G c.1) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, Rel P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 (dep P) (g P) (g' P)) →
      (((I.stp u a i).chr c.1 κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1) :
    GlobalTheory.TwU.ChiIs (sm I l Z) (K (chOf c)).lev fb dep Rel := by
  intro κ g z hg
  obtain ⟨κ', -, hχ, hin⟩ := GlobalTheory.T.exists_stepGroupElement_of_chartLevel I hOk hP l Z u a i hi bad Ch chOf K k hR c fb hfb hfin κ
  choose g' hg' using hex κ'
  have e := h κ' g g' z fun P => ⟨(hg P).1, hg' P,
    GlobalTheory.T.rational_automorphisms_near_same_adelic_congruent I hOk l Z a i fb _ dep P κ.1 (g' P) (g P) (hg' P).1 (hd P).1 (hd P).2 (hin P _ (hg' P)) (hg P).2⟩
  rw [hχ]
  exact (map_mul B.embLL _ _).symm.trans ((congrArg B.embLL e).trans (map_one _))

include hOk hP hR hfb hfin in

theorem lev_mid (hm : i < B.R.m) (y0 : SBof I a → Sp B.fields.E (B.R.N i))
    (hy0 : i + 1 = B.R.m → ∀ P, y0 P ∈ cosetIn ((I.stp u a i).rep c) P)
    (hRel : ∀ P g z, Rel P g z ↔ MidAt I hm c.1 P g z ∧ (i + 1 = B.R.m → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g (y0 P)) (y0 P))) :
    GlobalTheory.TwU.LocLe (sm I l Z) (K (chOf c)).lev fb (I.cst a).D Rel ∧ GlobalTheory.TwU.LocGe (sm I l Z) (K (chOf c)).lev fb (I.cst a).D Rel ∧
      GlobalTheory.TwU.ChiIs (sm I l Z) (K (chOf c)).lev fb (I.cst a).D Rel := by
  refine ⟨locLe_of hOk hP hR c hfb hfin (fun _ => le_rfl) fun κ hκ P => ?_, ?_,
    chiIs_of hOk hP hR c hfb hfin (fun P => ⟨(hOk.idx_ok a).cst_ok.D_pos P, le_rfl⟩) (fun κ P => ?_) fun κ g g' z h => ?_⟩
  · obtain ⟨g, z, hg, hl⟩ := GlobalTheory.T.exists_middleStep_level_inverse_lifts I hOk u a i hm c.1 κ P
    refine ⟨g, g, z, (hRel P g z).2 ⟨hg, fun h1 => ?_⟩, hl, congE_refl _ _ _⟩
    have h2 := (GlobalTheory.T.couplingCosetInFrames_preimage_under_lift I hOk u a i c.1 κ _ P g hκ.1 hl (y0 P)).1 (by rw [hκ.2]; exact hy0 h1 P)
    exact ((((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a i _ P).2 h1).2.2 _ (hy0 h1 P)).1 _).1 h2
  · rintro P v hv κ hκ ⟨g, z, hg, hin⟩
    obtain ⟨hg1, hg2⟩ := (hRel P g z).1 hg
    obtain ⟨hint, hc⟩ := GlobalTheory.T.congruent_automorphisms_lift_step_group_elements I hOk u a i hm c.1 P g z hg1
    refine GlobalTheory.T.stepNearLifts_component_mem_localChartGroup I hOk hP l Z u a i hi bad Ch chOf K k hR c fb hfb P v hv κ hκ g hint hin fun g' hg' hgg => ?_
    obtain ⟨κ', e1, e2, e3⟩ := hc g' hg' hgg
    refine ⟨κ', ⟨e1, funext fun P' => Set.ext fun z' => ?_⟩, e2, e3⟩
    by_cases hPP : P' = P
    · subst hPP
      rw [GlobalTheory.T.couplingCosetInFrames_preimage_under_lift I hOk u a i c.1 κ' _ P' g' e1 e2 z']
      by_cases h1 : i + 1 = B.R.m
      · exact (((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a i _ P').2 h1).2.2 _ (hy0 h1 P')).2 g g' hg' hgg (hg2 h1) z'
      · rw [(GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a i _ P').1 h1]
        exact Iff.rfl
    · exact GlobalTheory.T.couplingCosetInFrames_preimage_under_lift I hOk u a i c.1 κ' _ P' 1 e1 (e3 P' hPP) z'
  · obtain ⟨g, z, -, hl⟩ := GlobalTheory.T.exists_middleStep_level_inverse_lifts I hOk u a i hm c.1 κ P
    exact ⟨g, hl⟩
  · exact GlobalTheory.T.step_group_character_inverse_type_at_lifts I hOk u a i hm c.1 κ g g' z fun P => ⟨((hRel P _ _).1 (h P).1).1, (h P).2⟩

include hOk hP hR hfb hfin in

theorem lev_top (hm : i = B.R.m) :
    GlobalTheory.TwU.LocLe (sm I l Z) (K (chOf c)).lev fb (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a)) (GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i) ∧
      GlobalTheory.TwU.ChiIs (sm I l Z) (K (chOf c)).lev fb (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a)) (GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i) := by
  have hd : ∀ P, 1 ≤ GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P ∧ GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P ≤ (I.cst a).D P := fun P => by
    unfold GlobalTheory.TwU.topDep
    have h1 := (hOk.idx_ok a).cst_ok.M_pos
    split_ifs with h
    · exact ⟨le_rfl, (hOk.idx_ok a).cst_ok.D_pos P⟩
    · exact ⟨by omega, (hOk.idx_ok a).depthQ P h⟩
  refine ⟨locLe_of hOk hP hR c hfb hfin (fun P => (hd P).2) fun κ _ P => GlobalTheory.T.exists_topStep_level_congruent_blockSum_one I hOk u a i hm c.1 κ P,
    chiIs_of hOk hP hR c hfb hfin hd (fun κ P => ?_) fun κ g g' z h => GlobalTheory.T.last_step_character_inverse_type_at_lifts I hOk u a i hm c.1 κ g g' z h⟩
  obtain ⟨g, g', z, -, hl, -⟩ := GlobalTheory.T.exists_topStep_level_congruent_blockSum_one I hOk u a i hm c.1 κ P
  exact ⟨g', hl⟩

end Lev

set_option maxHeartbeats 4000000 in

theorem adTie_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi (β : Ch i hi), LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf i hi c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt), I.IsTw → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → ex.errX.piT = X.piT → I.StdDt l Z dt → (∀ v ∈ bad, v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v) → (∀ i hi, I.ReadsK l Z u a i hi (chOf i hi) (Kc i hi) ∧ I.IdY l Z u a i hi (eY i hi)) → (∀ i hi β, FunKilled (Kc i hi β).lev (X.piT u)) → (∀ i hi β, ∃ n : ℕ, 0 < n ∧ ∀ κ : (Kc i hi β).lev.U, (∀ v ∈ badG (I.rec7 l Z), bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (Kc i hi β).lev.chi κ ^ n = 1) → (a ≠ I.mu0 → ∀ i hi c (y : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm), Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det ((Kc i hi (chOf i hi c)).y ⟨c, rfl⟩).1 → detPt B.host I.SQ ((I.stp u a i).rep c).1.1 = dt y) → ∃ A : GlobalTheory.TwU.AdData t u a (fun i hi => ⟨B.T u, bad, eY i hi, Ch i hi, chOf i hi, fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c), Kc i hi⟩), GlobalTheory.TwU.AdPins A dt ∧ GlobalTheory.TwU.AdTie A dt (B.fields.conjO (X.piT u)) := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t u a bad Ch chOf eY Kc dt hTw hSK hRd hPin hX hDt hbad hRK hFun hFin hDet
  have hch : t.ChTie := (GlobalTheory.T.kernelChoices_standard_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t ⟨hSK.X_eq, hSK.seam, hSK.Pr, hSK.Ch, hSK.sel, hSK.S, hSK.word, hSK.tup,
    hSK.cst, hSK.idx, hSK.m2, hSK.glob, hSK.amb, hSK.δ, hSK.O⟩ hX).1
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch', sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hXf, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hSK
  dsimp only at hXf hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hXf
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  obtain ⟨r, hr, hN, hXi⟩ := hRd u a
  obtain rfl : rd u a = r := eq_of_heq hr
  have hm : B.R.m = B.R.m - 2 + 2 := hOk.hm
  choose k hk using fun i hi => (hRK i hi).1
  choose sc hsc using fun i hi => (hk i hi).onto
  choose fb hfb using fun i hi (β : Ch i hi) => GlobalTheory.T.exists_rational_frames_near_adelic_at_bad_primes I hOk l Z a (B.R.N i) (k i hi β)
  have hm1 : B.R.m - 2 + 1 ≤ B.R.m := by omega
  choose y0 hy0 using fun (β : Ch _ hm1) (P : SBof I a) => ((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a _ ((I.stp u a _).rep (sc _ hm1 β)) P).2 (by omega)).1
  have hkey : ∀ i hi c, (sc i hi (chOf i hi c)).1 = c.1 ∧ cosetIn ((I.stp u a i).rep (sc i hi (chOf i hi c))) = cosetIn ((I.stp u a i).rep c) :=
    fun i hi c => ((hk i hi).key _ _).1 (hsc i hi _)
  have hm3 : B.R.m - 2 + 1 + 1 = B.R.m := by omega
  have hib : ∀ i (hi : i < B.R.m) c, Idx.get c.1 hi = Idx.get (sc i hi.le (chOf i hi.le c)).1 hi := fun i hi c => by rw [(hkey i hi.le c).1]
  have hcrd := (spaces_in_coordinates I hOk hP l Z).2.2.2
  have hdt : ∀ x, dt x = FullDt.u1Dt B.host I.SQ x := fun x => by
    obtain ⟨b, hb⟩ := FullDt.exists_lift B.host x
    exact (hDt x b hb).trans (FullDt.normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ x b hb).symm
  refine ⟨{ crd := fun _ _ => 1
            iA := RingEquiv.refl _
            q := (QuotientGroup.mk' (KDq B.host I.SQ)).comp (finIdele (afIso B.host.F B.host.E))
            pt := fun i _ c => ((I.stp u a i).rep c).1.1
            yb := fun c => ((I.stp u a _).rep c).1.2
            ib := fun i hi β => Idx.get (sc i hi.le β).1 hi
            fb := fb
            y0 := y0 }, ?_, ?_⟩
  · refine ⟨(GlobalTheory.T.base_fields_definite_laws B).1, hOk.sel_ok, ⟨hOk.g_mem, hOk.T_mem u⟩, hch, hOk.ch_tied.mu0, GlobalTheory.T.localConstantWeilCharacter_values_isIntegral I hOk hTw a, fun _ => rfl, fun _ => Iff.rfl,
      ⟨fun y => ?_, fun k z hz => ?_⟩, fun x y hxy => ?_, fun ι hι j b x hb hx => ?_, fun h => ?_,
      fun μ _ _ => ⟨tildeQ B.host I.SQ (I.xi μ), fun x => ?_, fun u => ?_⟩, fun i hi => ?_, fun i hi y τ => ?_⟩
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (show DtQ B.host I.SQ from y)
      exact ⟨finAf B.host.F B.host.E a, mk_eq_of_snd_eq B.host I.SQ (afIso_finAf B.host.F B.host.E a)⟩
    · have hz' : (show B.host.E from z.1) * B.host.conj (k : B.host.E) = k := hz
      show (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) (ratId B.host.F B.host.E k)) : DtQ B.host I.SQ) = e1Q B.host I.SQ z
      rw [← isUnitaryPointsMap_unitaryRationalPointsFiner B.host I.SQ k z hz']
      refine mk_eq_of_snd_eq B.host I.SQ ?_
      show afIso B.host.F B.host.E ((k : B.host.E) ⊗ₜ[B.host.F] 1) = _
      rw [afIso_tmul_one]
      rfl
    · refine (hDt y (finIdele (afIso B.host.F B.host.E) x) ?_).symm
      have e : finAf B.host.F B.host.E (finIdele (afIso B.host.F B.host.E) x) = x :=
        Units.ext ((afIso B.host.F B.host.E).injective (afIso_finAf B.host.F B.host.E _))
      unfold IsDetLift
      rw [e]
      exact hxy.symm
    · show muTilQ B.host I.SQ I.C.mu0 (j.1 + 1) (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x)) = _
      have e : (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x) : DtQ B.host I.SQ) = QuotientGroup.mk b :=
        mk_eq_of_snd_eq B.host I.SQ ((GlobalTheory.T.finiteAdeleFieldIdentification_eq_baseChangeRingEquiv _ _ ι hι x).symm.trans hx)
      rw [e, muTilQ_succ B.host I.SQ I.C.mu0 j, tildeQ_mk B.host I.SQ (reference_characters_factor_tame I.SQ I.C j), finPartI_eq_self hb]
      rfl
    · obtain rfl : a = I.mu0 := h
      refine ⟨I.trueColumn_tuple_trivial_eq_one, ?_⟩
      show (O u I.mu0).mt = _
      rw [hO.mt u I.mu0, l.xi0, tildeQ_one]
      funext j
      split_ifs
      · exact mul_one _
      · rfl
    · have hk : KDq B.host I.SQ ≤ ((I.xi μ).1.comp (finPartI B.host.E)).ker :=
        (KDq_anti B.host (I.Q_subset_SQ μ)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).2.2 μ).1
      show tildeQ B.host I.SQ (I.xi μ) (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x)) = _
      rw [tildeQ_mk B.host I.SQ hk, finPartI_eq_self fun _ => rfl]
      exact Units.ext ((hOk.xi_reads μ).apply _ x rfl)
    · exact hO.mt u μ
    · rw [(hcrd i hi).1]
      simp [cT]
    · show (O u a).frm i y τ = _
      have e1 : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (1 : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) τ = 1 :=
        Matrix.map_one _ (map_zero _) (map_one _)
      refine (congrFun ((hO.frm u a i y).trans ((hRK i hi).2 y).symm) τ).trans ?_
      exact ((congrArg (· * (eY i hi y).1 τ) e1).trans (one_mul _)).symm
  · have hmov : ∀ {n : ℕ} (y : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), GlobalTheory.TwU.ratA (I.rec7 l Z).host.F 1 * y = y := fun y => by
      rw [map_one, one_mul]
    refine ⟨⟨fun i _ c => hN i c, fun c => PtAt.mem_ybSet _ hm3, fun i hi c c' x => ?_, fun c c' x => ?_, ⟨fun c => hN _ c, fun c c' x => ?_⟩,
      fun i hi c => (hPin u a i c).2 (Or.inl (by have : i ≤ B.R.m - 2 + 1 := hi; omega)), fun c' => (hPin u a _ c').trans (or_iff_right (by show ¬ B.R.m - 2 + 1 + 1 + 1 ≤ B.R.m; omega))⟩,
      fun _ _ => rfl, fun _ _ v hv => GlobalTheory.T.exists_badPrime_over_bad_place_of_chain I hOk l Z a v (hbad v hv), fun i hi c => ?_, fun i hi c P => ?_, fun i hi β P v h hv => ?_,
      fun c y hy P => ?_, fun i hi hi2 β => ?_, fun β => ?_, fun β => ?_, fun i hi c y hy => ?_, ?_⟩
    · have hi' : i < B.R.m - 2 := hi
      refine (hXi i (by omega) c c' x).trans ?_
      rw [xiAt_entry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm (Idx.some_get _ (by omega)).symm]
      exact congrArg₂ (fun al be => B.embLL (XiEntry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) i al be _ _ x)) (hib i _ c) (hib (i + 1) _ c')
    · refine (hXi (B.R.m - 2) (by omega) c c' x).trans ?_
      rw [xiAt_penultimate_eq_xiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm]
      exact congrArg (fun al => B.embLL (XiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (B.R.m - 2) al _ _ _ x)) (hib (B.R.m - 2) _ c)
    · refine (hXi (B.R.m - 2 + 1) (by omega) c c' x).trans ?_
      rw [xiAt_last I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega : B.R.m - 2 + 1 + 1 = B.R.m), xiOver_eq_topG]
      rfl
    · exact (seamOf_lat _ _ _ _ _ _ _ _).trans ((hN i c).trans (GlobalTheory.T.representativeLattice_eq_companion_of_adelicRep I hOk hP l Z u a i hi bad _ _ _ _ (hk i hi) c))
    · have h := GlobalTheory.T.chart_reads_at_class_GL I hOk hP l Z u a i hi bad _ _ _ _ (hk i hi) c _ (hfb i hi _) P
      rw [← hmov ((Kc i hi (chOf i hi c)).y ⟨c, rfl⟩).1] at h
      exact h
    · obtain ⟨ι, hι⟩ := GlobalTheory.T.levelPrimeFunctionals_eq_moved_level_functionals I hOk hP l Z u a i hi bad _ _ _ _ (hk i hi) β (hFun i hi β) P v h hv
      refine ⟨ι, fun c hc => ?_⟩
      have h := hι c hc
      rw [← hmov ((Kc i hi (chOf i hi c)).y ⟨c, rfl⟩).1] at h
      exact h
    · have h1 := (GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a _ ((I.stp u a _).rep c) P).2 (show B.R.m - 2 + 1 + 1 = B.R.m by omega)
      have h2 := hy0 (chOf _ hm1 c) P
      rw [(hkey _ hm1 c).2] at h2
      exact ((h1.2.2 _ h2).1 _).1 (h1.2.1 y hy)
    · have hi2' : i ≤ B.R.m - 2 := hi2
      obtain ⟨c, rfl⟩ := (hk i hi.le).onto β
      refine lev_mid hOk hP (hk i hi.le) c (hfb i hi.le _) (hFin i hi.le _) hi (fun _ => 0) (fun h => by omega) fun P g z => ?_
      rw [and_iff_left fun h => by omega, ← (hkey i hi.le c).1]
      exact Iff.rfl
    · obtain ⟨c, rfl⟩ := (hk _ hm1).onto β
      refine lev_mid hOk hP (hk _ hm1) c (hfb _ hm1 _) (hFin _ hm1 _) (by omega) (y0 (chOf _ hm1 c)) (fun _ P => (hkey _ hm1 c).2 ▸ hy0 _ P) fun P g z => ?_
      rw [← (hkey _ hm1 c).1]
      exact and_congr Iff.rfl ⟨fun h _ => h, fun h => h (by omega)⟩
    · have hm2 : B.R.m - 2 + 1 + 1 ≤ B.R.m := by omega
      obtain ⟨c, rfl⟩ := (hk _ hm2).onto β
      exact lev_top hOk hP (hk _ hm2) c (hfb _ hm2 _) (hFin _ hm2 _) (by omega)
    · refine (hO.dt u a i c).trans ?_
      by_cases ha : a = I.mu0
      · subst ha
        exact (FullDt.detPt_of_reads I hOk u i (hk i hi) c y hy).trans (hdt y).symm
      · exact hDet ha i hi c y hy
    · have e := eq_of_heq hamb
      have h := GlobalTheory.T.periodLatticeIdeal_trivial_at_chain_bad_primes I hOk u a χ
      rw [← e] at h
      exact h

end GlobalTheory.Mem.Col2.AdT

end
end
