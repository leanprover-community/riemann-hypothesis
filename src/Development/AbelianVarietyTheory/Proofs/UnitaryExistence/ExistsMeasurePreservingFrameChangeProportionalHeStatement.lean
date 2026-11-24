module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMeasurePreservingFrameChangeProportionalHe
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

@[expose] public section

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_measurePreserving_frameChange_proportional_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (y : Frame X.Ψ r) (y' : Frame X'.Ψ r), X.Ψ = X'.Ψ → X.p0 = X'.p0 → y ∈ OrthFr X → y' ∈ OrthFr X' → (∀ (τ : X.Ψ), ∃ t : ℝ, t ≠ 0 ∧ X'.Gm.map τ.1 = (t : ℂ) • X.Gm.map τ.1) → ∃ (e : RealGrp X ≃ᵐ RealGrp X') (α : RealGrp X → RealGrp X) (u : RealGrp X), MeasurePreserving e (haarR X) (haarR X') ∧ Measurable α ∧ (∀ t, α (α t) = u⁻¹ * t * u) ∧ ∀ t (τ : X.Ψ) (τ' : X'.Ψ), τ.1 = τ'.1 → mat y' τ' * ((e (α t) τ' : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat y' τ')⁻¹ = mat y τ * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat y τ)⁻¹ := by
  first | exact @GlobalTheory.PeterssonFrameChange.frame_change | exact GlobalTheory.PeterssonFrameChange.frame_change | (intros; apply GlobalTheory.PeterssonFrameChange.frame_change <;> assumption)
