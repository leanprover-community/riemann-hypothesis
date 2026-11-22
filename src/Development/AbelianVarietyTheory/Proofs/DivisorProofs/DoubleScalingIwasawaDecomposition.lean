module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.DblSurj

open Matrix GlobalTheory.EmbChart

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
  {ι : Type} [Fintype ι] [DecidableEq ι]

end Lift

end GlobalTheory.DblSurj

namespace GlobalTheory.DblSurj

open Matrix GlobalTheory.EmbChart

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {ι : Type} [Fintype ι] [DecidableEq ι]

end Local

end GlobalTheory.DblSurj

namespace GlobalTheory.DblSurj

open scoped Matrix

end GlobalTheory.DblSurj

open scoped Matrix

