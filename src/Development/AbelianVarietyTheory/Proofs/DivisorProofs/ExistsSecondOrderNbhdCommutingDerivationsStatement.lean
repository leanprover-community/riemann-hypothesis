module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondOrderNbhdCommutingDerivations
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr

@[expose] public section

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

theorem _root_.GlobalTheory.T.exists_secondOrderNbhd_commuting_derivations : ∀ (O : Type) [CommRing O] [Algebra ℂ O] (D₁ D₂ : Derivation ℂ O O), (∀ x, D₁ (D₂ x) = D₂ (D₁ x)) → ∃ (C : Type) (_ : CommRing C) (J : Ideal C) (φ₀ φ₁ φ₂ φ₃ : O →+* C) (e₁ e₂ : C), IsNilpotent J ∧ e₁ ∈ J ∧ e₂ ∈ J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x, φ₁ x = φ₀ x + φ₀ (D₁ x) * e₁) ∧ (∀ x, φ₂ x = φ₀ x + φ₀ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₁ x + φ₁ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₂ x + φ₂ (D₁ x) * e₁) ∧ ∀ x, φ₀ x * e₁ * e₂ = 0 → x = 0 := by
  first | exact @GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd | exact GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd | (intros; apply GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd <;> assumption)
