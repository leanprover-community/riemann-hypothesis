module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSignatureBlocksOfVectorAndFrame
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.exists_signature_blocks_of_vector_and_frame : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n), Sorts ε f → Sorts ε' f' → ∃ e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q), SignCompat e ∧ sg (e none) = GlobalTheory.GaussMean.sgn ℝ s := by
  first | exact @GlobalTheory.SignCount.exists_signCompat | exact GlobalTheory.SignCount.exists_signCompat | (intros; apply GlobalTheory.SignCount.exists_signCompat <;> assumption)
