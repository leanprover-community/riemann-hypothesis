module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CosetRepresentativeTraceFixedProperties
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

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.cosetRepresentativeTrace_fixed_properties : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)], ∀ z ∈ Fix L N, (∀ g : G, g • cosetTrace N z = cosetTrace N z) ∧ (v z ≤ 1 → v (cosetTrace N z) ≤ 1) ∧ ∀ e : L, (∀ g : G, g • e = e) → cosetTrace N (e * z) = e * cosetTrace N z := by
  first | exact @GlobalTheory.AlmostEt.cosetTrace_fixed_props | exact GlobalTheory.AlmostEt.cosetTrace_fixed_props | (intros; apply GlobalTheory.AlmostEt.cosetTrace_fixed_props <;> assumption)
