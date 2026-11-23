module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSInf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.JSPair

def dotL (E : Type) [Field E] [NumberField E] (k : ℕ) :
    (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] Cinf E :=
  ∑ i : Fin k, (ContinuousLinearMap.mul ℝ (Cinf E)).bilinearComp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)

theorem dotL_apply {E : Type} [Field E] [NumberField E] {k : ℕ} (x z : Fin k → Cinf E) :
    dotL E k x z = ∑ i, x i * z i := by
  simp [dotL, ContinuousLinearMap.sum_apply]

theorem exists_pairing : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, S8 → StdPsi ψ → ∃ β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) ∧ ∀ x z : Fin k → Cinf E, ψ (sInf E (∑ i, x i * z i)) = Complex.exp (-((β x z : ℝ) : ℂ) * Complex.I) := by
  intro E _ _ _ k ψ h8 hψ
  obtain ⟨l, hl⟩ := h8 (InfinitePlace E) (GlobalTheory.CompanionTheory.JSInfStep.chiInf ψ)
    (hψ.cont.comp GlobalTheory.CompanionTheory.JSInfStep.continuous_sInf) (fun z => hψ.norm _)
  let β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (Fin k → Cinf E) (Cinf E) ℝ (-l)) ∘L dotL E k
  have hβ : ∀ x z, β x z = -l (∑ i, x i * z i) := fun x z => by
    simp [β, dotL_apply]
  refine ⟨β, fun y hy => ?_, fun x z => ?_⟩
  · funext i
    refine GlobalTheory.CompanionTheory.JSInfStep.chiInf_nondeg hψ (y i) fun w => ?_
    have h0 := hy (Pi.single i w)
    rw [hβ] at h0
    have e : ∑ j, (Pi.single i w : Fin k → Cinf E) j * y j = y i * w := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, mul_comm]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_mul]
      · simp
    rw [e] at h0
    have h1 : l (y i * w) = 0 := neg_eq_zero.1 h0
    rw [hl, h1]
    simp
  · have := hl (∑ i, x i * z i)
    rw [GlobalTheory.CompanionTheory.JSInfStep.chiInf_apply] at this
    rw [this, hβ]
    simp

end GlobalTheory.CompanionTheory.JSPair

end
