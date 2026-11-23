module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfLeviPhaseCharacterIntegralsEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eq_of_leviPhaseCharacter_integrals_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ N₁ N₂ : Mx D W.rank r → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ μ → Integrable N₂ μ → (∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₁ u ∂μ = ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₂ u ∂μ) → N₁ = N₂ := by
  first | exact @GlobalTheory.LeviNormInj.eq_of_phase_integral_eq | exact GlobalTheory.LeviNormInj.eq_of_phase_integral_eq | (intros; apply GlobalTheory.LeviNormInj.eq_of_phase_integral_eq <;> assumption)
