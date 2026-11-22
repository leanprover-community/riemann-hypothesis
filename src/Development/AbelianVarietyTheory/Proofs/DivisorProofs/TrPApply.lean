module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

noncomputable section

namespace GlobalTheory.ArchSch

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable (F : Type) [Field F] [NumberField F]

def trP (κ : Type) [Fintype κ] : LinearMap.BilinForm ℝ (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun _ _ _ => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, LinearMap.map_smul, smul_eq_mul])
    (fun _ _ _ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun _ _ _ => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, LinearMap.map_smul, smul_eq_mul])

theorem mixedTracePairing_apply {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) :
    trP F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

variable {F} {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d d₁ : ℕ} {X : Spc F E n}
  {W : Spc F E d} {W₁ : Spc F E d₁}

end GlobalTheory.ArchSch
