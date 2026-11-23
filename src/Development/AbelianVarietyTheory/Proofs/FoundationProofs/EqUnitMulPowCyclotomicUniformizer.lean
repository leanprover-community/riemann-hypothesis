module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOfMemAdjoinStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevelStatement
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
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.UnitPow

theorem eq_unit_mul_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), b ≠ 0 → ∃ (n k : ℕ), 1 ≤ n ∧ ∃ u ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ u' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), u * u' = 1 ∧ b = u * (T.ζ n - 1) ^ k := by
  intro p _ Ω _ _ hclo T b hb hb0
  obtain ⟨n, ι, w, hn, hemb, hw, hmem⟩ := GlobalTheory.T.exists_level_emb_of_mem_adjoin_zeta_qq p Ω hclo T b hb
  obtain ⟨hdom, hdvr, hirr⟩ := GlobalTheory.T.isDiscreteValuationRing_cyclotomicTowerLevel p n hn
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [← hw, map_zero])
  obtain ⟨k, ε, hε⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hirr
  refine ⟨n, k, hn, ι (ε : On p n), hmem _, ι ((ε⁻¹ : (On p n)ˣ) : On p n), hmem _, ?_, ?_⟩
  · rw [← map_mul, Units.mul_inv, map_one]
  · rw [← hw, hε, map_mul, map_pow, map_sub, map_one, hemb.1]

end GlobalTheory.K5.UnitPow
