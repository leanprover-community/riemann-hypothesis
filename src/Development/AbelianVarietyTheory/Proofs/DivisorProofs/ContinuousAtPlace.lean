module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacAny

variable {F : Type} [Field F] [NumberField F]

scoped instance invTwoV (v : HeightOneSpectrum (𝓞 F)) : Invertible (2 : Fv F v) :=
  invertibleOfNonzero (by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2]
    exact (map_ne_zero _).2 two_ne_zero)

def psiV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom (GlobalTheory.EmbChart.atPlace v).toAddMonoidHom

theorem psiV_apply (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    psiV ψ v t = ψ (GlobalTheory.EmbChart.atPlace v t) := rfl

theorem continuous_atPlace (v : HeightOneSpectrum (𝓞 F)) : Continuous (GlobalTheory.EmbChart.atPlace v) := by
  have h : (GlobalTheory.EmbChart.atPlace v : Fv F v → AF F) = fun t => (0, GlobalTheory.AdelicU.singleFin v t) := rfl
  rw [h]
  exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)

theorem continuous_psiV {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (psiV ψ v) :=
  hψ.comp (continuous_atPlace v)

section At

variable {v : HeightOneSpectrum (𝓞 F)}

end At

end GlobalTheory.VacAny
