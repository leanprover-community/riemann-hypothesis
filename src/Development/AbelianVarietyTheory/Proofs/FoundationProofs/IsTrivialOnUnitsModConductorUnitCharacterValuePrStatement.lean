module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr
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

theorem _root_.GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k y ≤ valuation k x → Triv χ x → Triv χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), Triv χ x → Triv χ y → Triv χ (x + y)) ∧ (∀ χ : kˣ →* ℂˣ, Triv χ 0) ∧ (∀ (χ η : kˣ →* ℂˣ) (x : k), Triv χ x → Triv η x → Triv (χ * η) x) ∧ (∀ (χ : kˣ →* ℂˣ) (x : k), Triv χ x → Triv χ⁻¹ x) ∧ (∀ χ : kˣ →* ℂˣ, IsSmoothChar χ → IsOpen {x : k | Triv χ x} ∧ IsClosed {x : k | Triv χ x}) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k x = 1 → valuation k y = 1 → ev χ (x * y) = ev χ x * ev χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k x = 1 → valuation k y = 1 → Triv χ (x - y) → ev χ x = ev χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x : k), Triv χ 1 → ev χ x = 1) := by
  first | exact @GlobalTheory.PsType.triv_ev_props | exact GlobalTheory.PsType.triv_ev_props | (intros; apply GlobalTheory.PsType.triv_ev_props <;> assumption)
