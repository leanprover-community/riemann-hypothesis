module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSmoothOfChartDerivativesAtIdentity
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
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

theorem _root_.GlobalTheory.T.mem_smooth_of_chart_derivatives_at_identity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (K : Set (GA E a → ℂ)),
    (∀ f ∈ K, ∃ (ι : Type) (_ : Fintype ι) (fs : ι → GA E a → ℂ) (ℓ : ι → (Lie E a →L[ℝ] ℂ)), (∀ i, fs i ∈ K) ∧
      ∀ g, HasFDerivAt (chart f g) (∑ i, fs i g • ℓ i) (oneL E a)) → ∀ f ∈ K, f ∈ Sm E a := by
  first | exact @GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt | exact GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt | (intros; apply GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt <;> assumption)
