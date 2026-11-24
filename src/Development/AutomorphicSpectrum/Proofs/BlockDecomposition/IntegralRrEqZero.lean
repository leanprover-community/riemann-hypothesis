module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem Rd_ofReal_eq {n : ℕ} {Ψ : Mat n → ℝ} (hΨ : ContDiffOn ℝ ∞ Ψ (GLs n)) (X : Mat n)
    {y : Mat n} (hy : y ∈ GLs n) :
    Rd X (fun z => (Ψ z : ℂ)) y = ((Rr X Ψ y : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ Ψ y :=
    ((hΨ y hy).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
  have h : HasFDerivAt (fun z => (Ψ z : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ Ψ y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hd.hasFDerivAt
  simp only [Rd, Rr, h.fderiv]
  rfl

theorem integral_Rr_eq_zero : RCalc → ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (Ψ : Mat n → ℝ), ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0 := by
  intro hR n _ _ μ _ Ψ hΨ hc X
  have hf : ContDiffOn ℝ ∞ (fun z => (Ψ z : ℂ)) (GLs n) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hΨ
  have hcf : Cpt (fun z => (Ψ z : ℂ)) := by
    obtain ⟨R, hR'⟩ := hc
    exact ⟨R, fun y hy h => by simp [hR' y hy h]⟩
  have h0 := (hR n).2.2 μ ℂ (fun z => (Ψ z : ℂ)) hf hcf X
  have h1 : (fun y : G n => Rd X (fun z => (Ψ z : ℂ)) y.val) =
      fun y : G n => ((Rr X Ψ y.val : ℝ) : ℂ) :=
    funext fun y => Rd_ofReal_eq hΨ X (val_mem_GLs y)
  rw [h1, integral_complex_ofReal] at h0
  exact Complex.ofReal_eq_zero.1 h0

end GlobalTheory.CompanionTheory.WaveSpd
