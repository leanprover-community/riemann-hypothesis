module

public import Formalism.RealPlaceAnalysis.StatementE
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorRowExpansionEigenFunctional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.quantumMinor_rowExpansion_eigenFunctional : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (a b : Fin (t + 1) → Fin n) (a' b' : Fin t → Fin n) (a0 b0 : Fin n) (p : ℂ), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective b → Function.Injective a' → Function.Injective b' → Set.range a = insert a0 (Set.range a') → a0 ∉ Set.range a' → Set.range b = insert b0 (Set.range b') → b0 ∉ Set.range b' → a0 ∉ Set.range b → (∀ j v, l (E a0 (b j) v) = (if b j = b0 then p else 0) • l v) → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = (e * p) • l (Formalism.REAL.qminor E a' b' u v) := by
  first | exact @GlobalTheory.qminor_row_step_under_functional | exact GlobalTheory.qminor_row_step_under_functional | (intros; apply GlobalTheory.qminor_row_step_under_functional <;> assumption)
