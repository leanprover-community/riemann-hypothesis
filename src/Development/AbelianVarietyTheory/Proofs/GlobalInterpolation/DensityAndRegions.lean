module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
public import Mathlib.Analysis.Analytic.Order
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InRegionMono
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NeOneOfIsPrimitive
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReLtOneOfZero
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

open Complex DirichletCharacter Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

namespace GlobalTheory.ZerosNearOne

theorem density_and_regions : ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧
    (∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((∑ p ∈ T, analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤ C1 * Q ^ ((1 : ℝ) / 4)) ∧
    (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ, LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re → IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (LFunction χ) ρ = 1 ∧ ∀ ρ' : ℂ, LFunction χ ρ' = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3)) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.ZeroDensityMult.zero_density_mult
  obtain ⟨c, hc, H2, H3⟩ := GlobalTheory.ZeroFreeHalf.main GlobalTheory.LandauPageRegion.main
  exact ⟨C, c, hC, hc, H, H2, H3⟩

end GlobalTheory.ZerosNearOne
