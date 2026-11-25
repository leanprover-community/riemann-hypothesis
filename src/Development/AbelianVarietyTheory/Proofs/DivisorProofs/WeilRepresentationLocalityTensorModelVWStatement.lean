module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewiseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrModelOfIsLin

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)
open GlobalTheory.WeilM GlobalTheory.LFun ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.WeilLocalityVW

theorem locality : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ k ∈ UAt σ Γ.W (evFin F v), ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, k)) φ φ₁ :=
  fun Bs Γ X om om' hTr v k hk φ hφ => GlobalTheory.WeilLocalityW.locality _ _ _ Bs _ _ Γ X om om' hTr v k hk φ hφ

end GlobalTheory.WeilLocalityVW

theorem _root_.GlobalTheory.T.weilRepresentationLocality_tensorModelVW : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ k ∈ UAt σ Γ.W (evFin F v), ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, k)) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityVW.locality
