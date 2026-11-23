module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePrStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingPrincipalMinorMulModConductorStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupMulClosedStatement
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem theta_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, theta ψ (a * b) = theta ψ a * theta ψ b := by
  intro k _ _ _ _ n ψ hψ a ha b hb
  have P := GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k
  obtain ⟨-, -, -, -, -, -, hevmul, hevcong, hevtriv⟩ := P
  unfold theta
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  by_cases ht : Triv (ψ m / nxt ψ m) 1
  · rw [hevtriv _ _ ht, hevtriv _ _ ht, hevtriv _ _ ht, one_mul]
  · obtain ⟨hv, hc⟩ := GlobalTheory.T.leadingPrincipalMinor_mul_mod_conductor k n ψ hψ m ht
    have hab := GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed k n ψ hψ a ha b hb
    have va := hv a ha
    have vb := hv b hb
    have vab := hv (a * b) hab
    have vprod : valuation k (minor a m * minor b m) = 1 := by rw [map_mul, va, vb, one_mul]
    rw [hevcong _ _ _ vab vprod (hc a ha b hb), hevmul _ _ _ va vb]

end GlobalTheory.PsType
