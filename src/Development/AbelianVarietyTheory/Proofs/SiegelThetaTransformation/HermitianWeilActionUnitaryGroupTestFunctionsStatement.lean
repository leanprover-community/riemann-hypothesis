module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctions
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

@[expose] public section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

theorem _root_.GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ γ ∈ UU E N, ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB (weil Ψ γ φ) ∧ TransH Ψ γ φ (weil Ψ γ φ) ∧ (∀ ψ, IsSB ψ → TransH Ψ γ φ ψ → ψ = weil Ψ γ φ) ∧ (∀ ψ, IsSB ψ → ip (weil Ψ γ φ) (weil Ψ γ ψ) = ip φ ψ ∧ weil Ψ γ (φ + ψ) = weil Ψ γ φ + weil Ψ γ ψ) ∧ (∀ c : ℂ, weil Ψ γ (c • φ) = c • weil Ψ γ φ) ∧ (∀ γ' ∈ UU E N, weil Ψ (γ' * γ) φ = weil Ψ γ' (weil Ψ γ φ)) ∧ weil Ψ 1 φ = φ := by
  first | exact @GlobalTheory.SW.weil_action | exact GlobalTheory.SW.weil_action | (intros; apply GlobalTheory.SW.weil_action <;> assumption)
