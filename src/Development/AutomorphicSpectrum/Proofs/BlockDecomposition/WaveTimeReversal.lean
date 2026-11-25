module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

open scoped Matrix.Norms.Elementwise

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem isWave_time_refl : ∀ {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → IsWave E fun s => u (-s) := by
  intro n E u hu
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨?_, fun t => h2 (-t), ?_, ?_⟩
  · have hm : Set.MapsTo (fun p : ℝ × Mat n => (-p.1, p.2)) (Set.univ ×ˢ GLs n) (Set.univ ×ˢ GLs n) :=
      fun p hp => ⟨Set.mem_univ _, hp.2⟩
    have hc : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => (-p.1, p.2)) (Set.univ ×ˢ GLs n) :=
      (contDiff_fst.neg.prodMk contDiff_snd).contDiffOn
    exact h1.comp hc hm
  · intro t g hg
    have := iteratedDeriv_comp_neg (𝕜 := ℝ) 2 (fun s => u s g) t
    rw [this, h3 (-t) g hg]
    simp
  · intro g hg
    have := deriv_comp_neg (𝕜 := ℝ) (fun s => u s g) 0
    rw [this]
    simpa using h4 g hg

end GlobalTheory.CompanionTheory.WaveSpd
