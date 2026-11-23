module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsSmallerLevelRelIndexMul
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


theorem _root_.GlobalTheory.T.hasSum_cosets_smaller_level_relIndex_mul_alt : ∀ {G : Type} [Group G] (K J H Γ : Subgroup G), K ≤ J → J ≤ H → H ≤ Γ → K.relIndex J ≠ 0 → ∀ (Ψ : G → ℂ) (z : ℂ), (∀ g ∈ Γ, g ∉ H → Ψ g = 0) → (∀ g ∈ Γ, ∀ k ∈ J, Ψ (g * k) = Ψ g) → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) z → HasSum (fun y : Γ ⧸ K.subgroupOf Γ => Ψ (y.out : Γ)) ((K.relIndex J : ℂ) * z) := by
  first | exact @GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul | exact GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul | (intros; apply GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul <;> assumption)
