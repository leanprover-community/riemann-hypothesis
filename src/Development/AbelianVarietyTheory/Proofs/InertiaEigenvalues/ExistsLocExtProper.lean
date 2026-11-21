import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq

noncomputable section
open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DelEps
variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
variable {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}

theorem trW_mk {h : IsPlaceOver A v} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (σ : Weil h) :
    trW (WD.mk a) σ = LinearMap.trace ℂ V (a.ρ σ) := by
  obtain ⟨e, he, -⟩ := WD.mk_eq_mk.1 (Classical.choose_spec (Classical.choose_spec (WD.mk a).exists_rep))
  unfold trW
  rw [← LinearMap.trace_conj' _ e]
  congr 1
  ext x
  simp [LinearEquiv.conj_apply, he]

def LocExt.self (h : IsPlaceOver A v) : LocExt h := ⟨K, v, h, isLocalExt_self h⟩



end GlobalTheory.DelEps
end
