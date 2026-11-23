module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergEquivariantIsometry
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.heisenberg_equivariant_isometry : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ), (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ w w' : V × V, (∀ (s : ℝ) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β (s • w).1 (s • w).2 ⇑f →
      ⇑(T g) = GlobalTheory.GaussLine.heisFun β (s • w').1 (s • w').2 ⇑(T f)) →
    ∀ f g : SchwartzMap V ℂ, (∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x) →
    ∀ x, T g x = GlobalTheory.GaussLine.dHeis β w' ⇑(T f) x := by
  first | exact @GlobalTheory.HeisenbergL2.map_dHeis_of_isometry | exact GlobalTheory.HeisenbergL2.map_dHeis_of_isometry | (intros; apply GlobalTheory.HeisenbergL2.map_dHeis_of_isometry <;> assumption)
