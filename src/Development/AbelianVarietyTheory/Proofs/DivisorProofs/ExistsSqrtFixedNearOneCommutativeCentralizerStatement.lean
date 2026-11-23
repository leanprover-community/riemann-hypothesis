module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtFixedNearOneCommutativeCentralizer
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_sqrt_fixed_near_one_commutative_centralizer : ∀ (p : ℕ) [Fact p.Prime] (v : AwayP p) (B : Type) [Ring B] [Algebra (Qv v) B] [Module.Finite (Qv v) B], letI : TopologicalSpace B := moduleTopology (Qv v) B; ∀ (e : B) (σ : B →ₗ[Qv v] B), (∀ a b : B, a * e = e * a → b * e = e * b → a * b = b * a) → (∀ a : B, a * e = e * a → σ a * e = e * σ a) → (∀ a b : B, a * e = e * a → b * e = e * b → σ (a * b) = σ a * σ b) → σ 1 = 1 → ∃ W ∈ nhds (1 : B), ∀ s ∈ W, s * e = e * s → σ s = s → ∃ r : B, r * e = e * r ∧ σ r = r ∧ r * r = s := by
  first | (exact @GlobalTheory.sqrt_fix_near_one_centralizer) | (exact GlobalTheory.sqrt_fix_near_one_centralizer) | (intros; apply GlobalTheory.sqrt_fix_near_one_centralizer <;> assumption)
