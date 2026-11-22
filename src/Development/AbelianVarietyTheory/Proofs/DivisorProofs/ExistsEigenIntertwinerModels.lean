module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIntertwinerUniqueScalar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqZeroOfWrongSignGaussianRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantUnderIntegralLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProduStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.ModelPol

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def finPr {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : (κ → Af F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)

def pt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain MeasureTheory Filter Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.ThK.ModelPol.pureA_pt {κ : Type}
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :
    _root_.GlobalTheory.WeilM.pureA F f g (_root_.GlobalTheory.ThK.ModelPol.pt x y) = f x * g y := by
  change f (fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i))) * g y = f x * g y
  simp only [RingEquiv.apply_symm_apply]

section

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

end

end GlobalTheory.ThK.ModelPol

end
