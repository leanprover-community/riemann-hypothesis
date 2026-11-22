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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.RealLift Formalism.BasicNotions.TH
open scoped Classical

noncomputable section
namespace GlobalTheory.FockKStab
open GlobalTheory.ExpAct
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

end GlobalTheory.FockKStab
end

noncomputable section
namespace GlobalTheory.FockKStab
open Matrix

theorem commute_jm {R S : ℕ} {X : Mat R S} (hX : IsKC X) : Commute X (Formalism.BasicNotions.TH.Jm R S) := by
  show X * _ = _ * X
  have h1 : ∀ i j, X (Sum.inl i) (Sum.inr j) = 0 := fun i j => hX _ _ (by simp [sameBlock])
  have h2 : ∀ i j, X (Sum.inr i) (Sum.inl j) = 0 := fun i j => hX _ _ (by simp [sameBlock])
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply, h1, h2]

theorem mem_upq {R S : ℕ} {X : Mat R S} (hX : IsKC X) (hs : Xᴴ = -X) : X ∈ upq R S := by
  show Xᴴ * _ + _ * X = 0
  rw [hs, ← (commute_jm hX).eq]; simp

end GlobalTheory.FockKStab
end

noncomputable section
namespace GlobalTheory.FockKStab
open Matrix

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

end Tensor

end GlobalTheory.FockKStab
end
