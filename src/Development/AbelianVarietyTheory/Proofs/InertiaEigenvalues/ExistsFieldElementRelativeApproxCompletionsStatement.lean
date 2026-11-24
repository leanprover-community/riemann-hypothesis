module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementRelativeApproxCompletions
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

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_field_element_relative_approx_completions : ∀ (L : Type) [Field L] [NumberField L] (R : Finset (HeightOneSpectrum (𝓞 L))) (z : ∀ P : HeightOneSpectrum (𝓞 L), P.adicCompletion L), (∀ P ∈ R, z P ≠ 0) → ∃ k : Lˣ, ∀ P ∈ R, Valued.v (z P - algebraMap L (P.adicCompletion L) (k : L)) ≤ WithZero.exp (-1 : ℤ) * Valued.v (z P) := by
  first | exact @GlobalTheory.WeakApprox.exists_units_approx | exact GlobalTheory.WeakApprox.exists_units_approx | (intros; apply GlobalTheory.WeakApprox.exists_units_approx <;> assumption)
