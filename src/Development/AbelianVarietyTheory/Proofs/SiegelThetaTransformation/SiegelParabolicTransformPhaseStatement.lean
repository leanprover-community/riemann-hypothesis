module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelParabolicTransformPhase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.siegelParabolic_transform_values_rootOfUnity : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, σ.toBlocks₂₁ = 0 → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ → TransS σ φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ), Ph u ∧ ψ y = u * φ y' := by
  first | exact @GlobalTheory.Phase.ParabValues.values_parabolic | exact GlobalTheory.Phase.ParabValues.values_parabolic | (intros; apply GlobalTheory.Phase.ParabValues.values_parabolic <;> assumption)
