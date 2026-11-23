module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace FubiniStudySmooth

theorem contDiffAt_blockNorm {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (k : K)
    (z : (Σ k, ι k) → ℂ) (hz : ∃ i, z ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (Σ k, ι k) → ℂ => ‖WithLp.toLp 2 (fun i => w ⟨k, i⟩)‖) z := by
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (Σ k, ι k) → ℂ => WithLp.toLp 2 (fun i => w ⟨k, i⟩)) :=
    PiLp.contDiff_toLp.comp (contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))
  have hne : WithLp.toLp 2 (fun i => z ⟨k, i⟩) ≠ 0 := by
    obtain ⟨i, hi⟩ := hz
    intro h0
    exact hi (by simpa using congrArg (fun v : WithLp 2 (ι k → ℂ) => v.ofLp i) h0)
  exact (contDiffAt_norm ℂ hne).comp z hL.contDiffAt

end FubiniStudySmooth

theorem FsLineSmooth.proof : FsLineSmooth.Statement := by
  intro K _ ι _
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : (Σ k, ι k) → ℂ => ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ ^ ((1 : K → ℤ) k)) _
  refine contDiffOn_prod fun k _ => ?_
  intro z hz
  simp only [Pi.one_apply, zpow_one]
  exact (FubiniStudySmooth.contDiffAt_blockNorm ι k z (hz k)).contDiffWithinAt

end GroundTheory.Heights₂.Heights
