import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerToL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LTLTInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLpTwoOfCpt

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp.Rep

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Calculus

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]








end Calculus

def co (p : Bool × Fin n × Fin n) : Mat n →L[ℝ] ℝ :=
  (if p.1 then Complex.reCLM else Complex.imCLM).comp
    (LinearMap.toContinuousLinearMap
      ((Matrix.entryLinearMap ℝ ℂ p.2.1 p.2.2 : Mat n →ₗ[ℝ] ℂ)))


section Conv

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

def cvl (φ : Mat n → ℂ) (y : Lp V 2 μ) : Mat n → V :=
  fun x => ∫ z : G n, φ (x * (z⁻¹ : G n).val) • (y : G n → V) z ∂μ

def CB (φ : Mat n → ℂ) (y : Lp V 2 μ) : Lp V 2 μ := ∫ z : G n, φ z.val • LT μ z y ∂μ

end Conv

section Classes

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] {μ : Measure (G n)}





end Classes


end GlobalTheory.CompanionTheory.WaveCp.Rep
