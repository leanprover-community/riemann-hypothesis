import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerToL

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp

section LeftTranslation

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]





end LeftTranslation

end GlobalTheory.CompanionTheory.WaveCp
