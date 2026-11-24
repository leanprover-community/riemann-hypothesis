module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationClosedUnderBoundedCombination
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.presentation_closed_under_bounded_combination : ∀ (D : D7) (T : TaylorLogMetric.Tor D) (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (F₀ : TaylorLogMetric.VC D a b → ℂ) (α : Type) (R : Finset α) (c : α → ℂ) (F : α → TaylorLogMetric.VC D a b → ℂ) (n β : ℝ), 0 ≤ β → (∀ x ∈ R, Pres D T L L' F₀ (F x) n) → (∀ x ∈ R, c x ∈ TaylorLogMetric.Qbar ∧ ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (c x)‖ ≤ β) → Pres D T L L' F₀ (fun z => ∑ x ∈ R, c x * F x z) (R.card * β * n) := by
  first | exact @GlobalTheory.PresSum.pres_sum | exact GlobalTheory.PresSum.pres_sum | (intros; apply GlobalTheory.PresSum.pres_sum <;> assumption)
