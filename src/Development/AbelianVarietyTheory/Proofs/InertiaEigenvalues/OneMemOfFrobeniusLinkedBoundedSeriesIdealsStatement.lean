module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddOfMemLdivSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMemOfFrobeniusLinkedBoundedSeriesIdeals
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.one_mem_of_frobenius_linked_boundedSeries_ideals : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (l e a M₁ M₂ : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (J : ZMod a → Set K⟦X⟧), (∀ τ, ∀ x ∈ J τ, ∀ y ∈ J τ, x + y ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∃ c : ℝ, ∀ n, ‖coeff n x‖ ≤ c) → (∀ τ, ∃ g ∈ J τ, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → (∀ τ, ∀ h ∈ J (τ - 1), E K l e ^ M₁ * frob K l h ∈ J τ) → (∀ τ, ∀ h ∈ J τ, ∀ i < l, frobSlice l i (E K l e ^ M₂ * h) ∈ J (τ - 1)) → ∀ τ, (1 : K⟦X⟧) ∈ J τ := by
  first | exact @GlobalTheory.BK.GcdCore.one_mem | exact GlobalTheory.BK.GcdCore.one_mem | (intros; apply GlobalTheory.BK.GcdCore.one_mem <;> assumption)
