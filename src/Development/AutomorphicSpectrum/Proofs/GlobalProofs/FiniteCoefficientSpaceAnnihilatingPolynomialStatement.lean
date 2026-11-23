module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteCoefficientSpaceAnnihilatingPolynomial
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.Published.AutFin (IsContRep coeffSpan)

theorem _root_.GlobalTheory.T.finite_coefficient_space_annihilating_polynomial :
    ∀ (K W : Type) [Group K] [TopologicalSpace K] [AddCommGroup W] [Module ℂ W]
      [FiniteDimensional ℂ W] (ρ : Representation ℂ K W),
      IsContRep ρ → ∀ s : ℝ → K, Continuous s → s 0 = 1 →
        (∀ a b, s (a + b) = s a * s b) →
        ∃ m : Polynomial ℂ, m ≠ 0 ∧ ∀ f ∈ coeffSpan ρ, ∀ k : K,
          ∑ j ∈ Finset.range (m.natDegree + 1),
            m.coeff j * iteratedDeriv j (fun t : ℝ => f (k * s t)) 0 = 0 :=
  GlobalTheory.CompanionTheory.HcFinite.OneParam.coeff_ode
