module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckePartialLSeriesEntireBoundedStrips
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open NumberField

theorem _root_.GlobalTheory.T.completed_heckePartialLSeries_entire_bounded_strips : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (M : Ideal (𝓞 K)) (F : 𝓞 K → ℂ), M ≠ ⊥ → (∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) → (∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), F ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s := by
  first | exact @GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded | exact GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded | (intros; apply GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded <;> assumption)
