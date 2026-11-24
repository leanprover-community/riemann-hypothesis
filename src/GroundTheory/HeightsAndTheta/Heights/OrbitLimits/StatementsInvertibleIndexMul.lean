module

public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights

def InvertibleIndexMul.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (M N P : AddSubgroup Ω) (η : Type) [Fintype η] (g h : η → Ω),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) → (∀ b ∈ B, ∀ z ∈ N, b * z ∈ N) → (∀ b ∈ B, ∀ z ∈ P, b * z ∈ P) →
    (∀ i, g i ≠ 0) → (∀ i, h i ≠ 0) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * g i ∈ B) → (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * h i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i,
      ((∃ b : B, b ∉ m ∧ (b : Ω) * g i ∈ M) ∧ ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * g i) ∧
      ((∃ b : B, b ∉ m ∧ (b : Ω) * h i ∈ N) ∧ ∀ z ∈ N, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * h i) ∧
      ((∃ b : B, b ∉ m ∧ (b : Ω) * (g i * h i) ∈ P) ∧
        ∀ z ∈ P, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * (g i * h i))) →
      0 < genIndex M B.toAddSubgroup ∧ 0 < genIndex N B.toAddSubgroup ∧
        genIndex P B.toAddSubgroup = genIndex M B.toAddSubgroup * genIndex N B.toAddSubgroup

end GroundTheory.Heights₂.Heights.Targets
