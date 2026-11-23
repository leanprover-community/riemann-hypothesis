module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactModNormOneKernelInvolution
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.exists_compact_mod_normOneKernel_involution : ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [LocallyCompactSpace Z] [SigmaCompactSpace Z] [T2Space Z], (∀ a b : Z, a * b = b * a) → ∀ τ : Z →* Z, Continuous τ → (∀ z, τ (τ z) = z) → (∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s) → ∀ D : Set Z, IsCompact D → ∃ B : Set Z, IsCompact B ∧ ∀ z : Z, τ z * z ∈ D → ∃ t : Z, τ t * t = 1 ∧ ∃ b ∈ B, z = t * b := by
  first | exact @GlobalTheory.InvolutionNorm.exists_compact_mod_kernel | exact GlobalTheory.InvolutionNorm.exists_compact_mod_kernel | (intros; apply GlobalTheory.InvolutionNorm.exists_compact_mod_kernel <;> assumption)
