module

public import Formalism.PeriodIntegrals.QuotInv
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityLieAlgebraOfOmegaDensity
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

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.hasDensityAtIdentityLieAlgebra_of_omegaDensity : ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n), (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) → ∀ (μ : Measure (Formalism.BasicNotions.UpqT P Q)) (c : ℝ≥0∞), μ.IsHaarMeasure → Formalism.BasicNotions.OmegaDensity μ c → PI.IsHaarOnM (UH (Formalism.REAL.Jm ε)) (μ.map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))) ∧ HasDens (UH (Formalism.REAL.Jm ε)) (μ.map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))) c := by
  first | exact @GlobalTheory.OmegaFrobenius.hasDens_of_omegaDensity | exact GlobalTheory.OmegaFrobenius.hasDens_of_omegaDensity | (intros; apply GlobalTheory.OmegaFrobenius.hasDens_of_omegaDensity <;> assumption)
