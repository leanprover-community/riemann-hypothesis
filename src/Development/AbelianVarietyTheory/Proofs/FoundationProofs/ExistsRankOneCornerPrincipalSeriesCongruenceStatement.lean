module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRankOneCornerPrincipalSeriesCongruence
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.exists_rankOne_corner_principalSeriesCongruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ x ∈ KO k (Fin n), ∀ a b : Fin n, a < b → ¬ Triv (ψ a / ψ b) (x.val a b) → (∀ j, b < j → Triv (ψ a / ψ j) (x.val a j)) → ∃ j ∈ grp ψ, ∃ (u : kˣ) (s : k), valuation k (u : k) = 1 ∧ valuation k s ≤ 1 ∧ s * x.val a b = (u : k) - 1 ∧ ψ a u ≠ ψ b u ∧ theta ψ j = (ψ b u : ℂ) ∧ x * j * x⁻¹ ∈ KO k (Fin n) ∧ (x * j * x⁻¹).val = 1 + Matrix.vecMulVec (fun i => s * x.val i b) (Pi.single a 1) := by
  first | exact @GlobalTheory.PsType.corner_rankOne | exact GlobalTheory.PsType.corner_rankOne | (intros; apply GlobalTheory.PsType.corner_rankOne <;> assumption)
