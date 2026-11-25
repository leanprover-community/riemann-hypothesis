module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
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

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

open scoped Matrix.Norms.Elementwise

namespace GlobalTheory.CompanionTheory.WaveMult

theorem lg_le_lg_mul_add (hL : LgFacts) {n : ℕ} {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) :
    lg x ≤ lg (x * y) + lg y := by
  have hdx : x.det ≠ 0 := hx
  have hdy : y.det ≠ 0 := hy
  have hxy : x * y ∈ GLs n := by
    change (x * y).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hdx hdy
  have hu : IsUnit y.det := isUnit_iff_ne_zero.mpr hdy
  have h1 := (hL n).1 (x * y) hxy y⁻¹ (inv_mem_GLs hy)
  have h2 := (hL n).2.1 y hy
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ hu, h2] at h1
  exact h1

theorem wave_cpt_bounded_time : LgFacts → WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V),
    IsWave E u → Cpt (u 0) → ∀ T : ℝ, ∃ R : ℝ, ∀ t, |t| ≤ T → ∀ y ∈ GLs n, R < lg y → u t y = 0 := by
  intro hL hS n E u hu hc T
  obtain ⟨c, hc'⟩ := hS n
  obtain ⟨R₀, hR₀⟩ := hc
  refine ⟨R₀ + |c| * (1 + |T|), fun t ht x hx hlg => hc' E u hu t x hx fun y hy hly => ?_⟩
  have hxy : x * y ∈ GLs n := by
    change (x * y).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  refine hR₀ (x * y) hxy ?_
  have h1 := lg_le_lg_mul_add hL hx hy
  have h2 : |t| ≤ |T| := ht.trans (le_abs_self T)
  have h3 : c * (1 + |t|) ≤ |c| * (1 + |T|) :=
    calc c * (1 + |t|) ≤ |c| * (1 + |t|) :=
          mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
      _ ≤ |c| * (1 + |T|) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
  linarith

end GlobalTheory.CompanionTheory.WaveMult
