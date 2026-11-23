module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFramesSamePeriodCoordinates
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.exists_holomorphicFrames_same_periodCoordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (B : Set ℂ) (x₁ : ℂ → Frame X.Ψ r), (∀ w ∈ B, x₁ w ∈ X.dom) → (∀ v ∈ X.Λ, ∀ τ a, DifferentiableOn ℂ (fun w => GlobalTheory.GenericFrames.pc X (x₁ w) v τ a) B) → ∃ x : ℂ → Frame X.Ψ r, DifferentiableOn ℂ x B ∧ ∀ w ∈ B, x w ∈ X.dom ∧ ∀ v τ a, GlobalTheory.GenericFrames.pc X (x w) v τ a = GlobalTheory.GenericFrames.pc X (x₁ w) v τ a := by
  first | exact @GlobalTheory.HolFrameLift.exists_holomorphic_frames | exact GlobalTheory.HolFrameLift.exists_holomorphic_frames | (intros; apply GlobalTheory.HolFrameLift.exists_holomorphic_frames <;> assumption)
