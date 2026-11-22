module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompositumCompletion

theorem exists_completion_map {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L']
    (jL : L →+* L') (v : HeightOneSpectrum (𝓞 L)) (v' : HeightOneSpectrum (𝓞 L'))
    (h : ∀ x : 𝓞 L, RingOfIntegers.mapRingHom jL x ∈ v'.asIdeal ↔ x ∈ v.asIdeal) :
    ∃ μ : v.adicCompletion L →+* v'.adicCompletion L', Continuous μ ∧
      ∀ x, μ (algebraMap L _ x) = algebraMap L' _ (jL x) := by
  letI : Algebra L L' := jL.toAlgebra
  haveI : v'.asIdeal.LiesOver v.asIdeal := ⟨by ext x; exact (h x).symm⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver L L' v v').continuous
  let φ : v.adicCompletion L →+* v'.adicCompletion L' :=
    ((HeightOneSpectrum.adicCompletion.equiv L' v').symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation L)) (WithVal (v'.valuation L'))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv L v).toRingHom
  refine ⟨φ, ?_, fun x => ?_⟩
  · exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L' v').comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (v.valuation L)) (WithVal (v'.valuation L')))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v))
  · apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)

end GlobalTheory.CompositumCompletion
