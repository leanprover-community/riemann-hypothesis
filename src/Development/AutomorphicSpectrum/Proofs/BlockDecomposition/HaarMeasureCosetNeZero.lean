import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecomp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecomp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet

section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem volume_cosetSet_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) ≠ 0 := by
  intro k _ _ _ _ t _ _ μ _ c hc
  have h0 : (0 : Fin t → k) ∈ cosetSet t c 0 := by
    show Multiplicative.ofAdd ((0 : Fin t → k) - 0) ∈ Lc t c
    rw [sub_zero, ofAdd_zero]
    exact one_mem _
  have hpos : 0 < μ (cosetSet t c 0) := (isClopen_cosetSet t c 0).isOpen.measure_pos μ ⟨0, h0⟩
  have hfin : μ (cosetSet t c 0) < ⊤ := (isCompact_cosetSet t hc 0).measure_lt_top
  rw [Complex.ofReal_ne_zero]
  exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_coset_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) ≠ 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZPsiPG.FibKer.volume_cosetSet_ne_zero
