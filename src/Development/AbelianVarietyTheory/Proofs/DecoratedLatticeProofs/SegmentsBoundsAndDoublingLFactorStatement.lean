module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SegmentsBoundsAndDoublingLFactor
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.segments_bounds_and_doubling_lFactor : ∀ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k t N : ℕ) (z : ℕ → ℂˣ), (∀ i, ‖(z i : ℂ)‖ = 1) → ∀ α : Fin N → ℂˣ, Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg w (z i) t → (∀ j, ‖(α j : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2) ∧ ‖(α j : ℂ)‖⁻¹ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α ((t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α⁻¹ ((t : ℂ) / 2 + 1 / 2) = ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t, ((1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹) * (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹))⁻¹ := by
  first | exact @GlobalTheory.LFun.seg_bounds_and_doubling_lFactor | exact GlobalTheory.LFun.seg_bounds_and_doubling_lFactor | (intros; apply GlobalTheory.LFun.seg_bounds_and_doubling_lFactor <;> assumption)
