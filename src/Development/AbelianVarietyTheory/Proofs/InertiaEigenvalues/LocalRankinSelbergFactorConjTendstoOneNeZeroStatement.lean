module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergFactorConjTendstoOneNeZero
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

theorem _root_.GlobalTheory.T.localRankinSelbergFactor_conj_tendsto_one_ne_zero : ∀ (q : ℕ) (A B : Multiset ℂˣ), 1 < q → (∀ α ∈ A, ‖(α : ℂ)‖ ^ 2 < (q : ℝ)) → (∀ β ∈ B, ‖(β : ℂ)‖ ^ 2 < (q : ℝ)) → Tendsto (fun x : ℝ => locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1) (𝓝 (locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1)) ∧ locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1 ≠ 0 := by
  first | (exact @GlobalTheory.JSW.locL_conj_tendsto_one_and_ne_zero) | (exact GlobalTheory.JSW.locL_conj_tendsto_one_and_ne_zero) | (intros; apply GlobalTheory.JSW.locL_conj_tendsto_one_and_ne_zero  <;> assumption)
