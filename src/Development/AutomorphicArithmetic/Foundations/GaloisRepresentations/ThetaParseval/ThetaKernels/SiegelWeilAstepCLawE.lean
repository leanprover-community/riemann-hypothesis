module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCLawD
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem a_dil_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) (h : d.G) : d.a (R.ι w y * h) = Real.exp (2 * τ) * d.a h ∧ 0 ≤ d.a h := by
  haveI := d.cm.1
  have hf := _root_.PositivityTheory.SiegelWeilFormula.AStep.inFrame_dil'_k R w i₀ τ y hy
  have h21 : (inFrame d.b (R.ι w y)).toBlocks₂₁ = 0 := by rw [hf, Matrix.toBlocks_fromBlocks₂₁]
  obtain ⟨t, ht, hdet⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame_k d (R.ι w y) h21
  have hdetU : Matrix.GeneralLinearGroup.det t = Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ) := by
    rw [← det_dilT d.cm w i₀ τ]
    apply Units.ext
    rw [hdet, hf, Matrix.toBlocks_fromBlocks₁₁]
    rfl
  refine ⟨?_, ?_⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.a_mul_par_k d ht h, hdetU, absE_adrU d.cm w τ]
  · obtain ⟨p, tp, hp, k, hk, rfl⟩ := d.ok.hgt.iwa h
    rw [d.ok.hgt.val p tp hp k hk]
    exact NNReal.coe_nonneg _
end PositivityTheory.SiegelWeilFormula.AStep
end
end
