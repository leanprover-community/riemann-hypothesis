module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForLeviMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierDoubleReflection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicIntegralFormula

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChangeBij

open GlobalTheory.SympChange GlobalTheory.LeviOp GlobalTheory.SympUnip GlobalTheory.AdelicSvNQuad GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic

section Levi

variable {F : Type} [Field F] [NumberField F] {κ : Type}

open scoped Classical in
theorem levi_mapsTo [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F) (hA : IsUnit A.det) :
    ∀ Φ ∈ schA F κ, LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) Φ ∈ schA F κ := by
  let gI : F →+* mixedEmbedding.mixedSpace F := (evIr (F := F)).comp (algebraMap F (AF F))
  let gF : F →+* FiniteAdeleRing (𝓞 F) F := (RingHom.snd _ _).comp (algebraMap F (AF F))
  let L := linEquiv (κ := κ) gI A hA
  have key : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) (pureA F f g) =
        pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f) (g ∘ homeo gF A hA) := by
    intro f g
    funext x
    simp only [LinearMap.funLeft_apply, pureA, Function.comp_apply, homeo_apply,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    congr 1
    · congr 1
      funext i
      exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
    · congr 1
      funext i
      exact hom_mulVec (RingHom.snd _ _) (algebraMap F (AF F)) gF rfl A⁻¹ x i
  have hle : schA F κ ≤ (schA F κ).comap
      (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    show _ ∈ schA F κ
    rw [key]
    exact Submodule.subset_span ⟨_, _, sb_comp (homeo gF A hA) hg, rfl⟩
  exact fun Φ hΦ => hle hΦ

end Levi

end GlobalTheory.SympChangeBij

